"""Proof Orchestrator v5: Guide-Centric Architecture.

Every phase follows one pattern:
  1. Worker does mechanical work
  2. Guide reviews result via _consult_guide_raw()
  3. Guide decides next step via _consult_guide_decide()

The guide is the sole decision-maker for its lemma. The orchestrator handles
only plumbing (transitions, state persistence, agent lifecycle).

Two guide APIs:
  _consult_guide_raw(task)   → free-text response (advice, diagnosis)
  _consult_guide_decide(options, task) → structured choice + reason

Per-lemma state (LemmaContext):
  current_task     — what guide should focus on (set by caller, sticky)
  failure_context  — last error (set by any phase, sticky)
  needs_fresh_guide — dump .md + destroy + new guide reads .md
"""

from __future__ import annotations

import asyncio
import json
import re
import shutil
import time as _time
from dataclasses import dataclass, field
from enum import Enum
from pathlib import Path
from typing import Any, TypeVar

from .po_agents import verified_loop, run_splitter, LoopOutcome
from .po_lean import get_lean_tools, MoveSession
from .po_util import setup_child_workspace, copy_cheat_sheet, cheat_sheet_name, cheat_sheet_source
from .lemma_ledger import LemmaLedger, LemmaEntry, LemmaStatus
from .cycle_detection import detect, MatchType
from .verifiers.proof_writer_verifier import make_proof_writer_verifier
from .._helpers import swarm_agent
from .._lean_tools_mcp import create_extractor_mcp_server
from .._tokens import CancellationToken
from .._agent import SwarmAgent

T = TypeVar("T")

MAX_DEPTH = 5
MIN_CHUNK_TURNS = 50
MAX_CHUNK_TURNS = 100
CHUNK_TURNS = MIN_CHUNK_TURNS
GRACE_TURNS = 20
# Runaway backstop for a single lemma's guide-driven prove loop. The guide remains
# the decision-maker; this is only a safety net against an unbounded `continue`
# spin (a leaf that neither proves, decomposes, nor gets given up). On breach we
# stop asking the guide to `continue` and force the terminal path
# (decompose → give_up → propagate). These are deliberately HIGH — a normal proof
# should never approach them.
MAX_CHUNKS_PER_LEMMA = 80          # ~80 chunks × up to 100 turns = a lot of room
# TIER 1 — FLEXIBLE per-lemma backstop. This is a NO-PROGRESS budget, not raw
# wall-clock: the clock is measured from the last chunk that STRICTLY reduced the
# transitive open-sorry count (entry._last_progress_time). A proof that keeps
# shedding sorries never trips it — only genuine stalling does. The guide can also
# grant bounded extensions (EXTEND_MINUTES) when it judges the lemma is close.
LEMMA_IDLE_MINUTES = 180           # minutes WITHOUT progress before the backstop fires
MAX_GUIDE_EXTEND_MINUTES = 30      # max minutes the guide may add per grant
# ENDGAME grace: chunks with 0 leaf-sorries but a not-yet-compiling proof count as
# progress (reset the idle clock) for this many chunks — a writer that closed the
# last sorry and is fixing compile errors is on the critical path, not stalling.
# After the window the idle clock ages again so a permanently-wedged endgame (a
# proof the writer can never compile) is still caught by the flexible/hard backstop.
ENDGAME_GRACE_CHUNKS = 4
# TIER 2 — HARD run-level ceiling (absolute wall-clock for the WHOLE run). Set via
# `start_dashboard.sh --max-run-minutes`. None ⇒ NO stopping time (run until proved
# or otherwise terminated). This is the only unconditional stop.
# When a child gives up, its parent is re-activated to re-decompose differently.
# Bound how many times a single parent may be re-activated before we stop and
# propagate the failure further up (prevents the give_up ↔ re-decompose churn).
MAX_REACTIVATIONS = 2
# An agent's context window is rotated (swapped for a fresh instance) once usage
# crosses this. NOTE: the figure everywhere in this module is context *USED* —
# a LOW number means the agent has lots of runway left, NOT that it is exhausted.
CONTEXT_ROTATION_THRESHOLD = 75.0  # percent USED


def _runway_note(pct: float | None) -> str:
    """Render a writer's context-usage % as an unambiguous runway phrase for the
    guide's prompt.

    This exists because a bare "Writer context: 5%" was repeatedly misread by the
    guide as "5% left → exhausted" and triggered a premature `decompose` on turn 1
    (the number is context USED, so 5% means 95% free). We spell out both the
    number and its meaning so the signal cannot be inverted.
    """
    used = pct or 0.0
    free = 100.0 - used
    if used < CONTEXT_ROTATION_THRESHOLD * 0.6:        # < ~45% used
        band = "HEALTHY — plenty of runway, keep the writer working"
    elif used < CONTEXT_ROTATION_THRESHOLD:            # ~45–75% used
        band = "GETTING FULL — rotation approaching, wrap up soon"
    else:                                              # ≥ 75% used
        band = "FULL — will rotate to a fresh writer"
    return (f"Writer runway: {band} "
            f"({used:.0f}% of context USED, {free:.0f}% free)")


# ═══════════════════════════════════════════════════════════════════════════════
# State Machine
# ═══════════════════════════════════════════════════════════════════════════════

class Phase(str, Enum):
    INIT = "init"
    SELECT = "select"
    PROVE = "prove"
    EXTRACT = "extract"
    DETECT = "detect"
    UPDATE = "update"
    CHECK = "check"
    ASSEMBLING = "assembling"
    DONE = "done"
    FAILED = "failed"


class Trans(str, Enum):
    REGISTERED = "registered"
    PICKED = "picked"
    PROVED = "proved"
    HAS_SORRY = "has_sorry"
    CONTINGENT = "contingent"
    CONTRADICTORY = "contradictory"
    EXTRACTED = "extracted"
    CHECKED = "checked"
    NO_CYCLE = "no_cycle"
    ALL_PROVED = "all_proved"
    HAS_PENDING = "has_pending"
    BLOCKED = "blocked"
    ASSEMBLED = "assembled"
    ASSEMBLY_FAILED = "assembly_failed"
    RETRY = "retry"


TRANSITIONS: dict[tuple[str, str], str] = {
    (Phase.INIT, Trans.REGISTERED):       Phase.SELECT,
    (Phase.INIT, Trans.BLOCKED):          Phase.FAILED,

    (Phase.SELECT, Trans.PICKED):         Phase.PROVE,
    (Phase.SELECT, Trans.BLOCKED):        Phase.FAILED,

    (Phase.PROVE, Trans.PROVED):          Phase.UPDATE,
    (Phase.PROVE, Trans.HAS_SORRY):       Phase.EXTRACT,
    (Phase.PROVE, Trans.CONTINGENT):      Phase.UPDATE,
    (Phase.PROVE, Trans.CONTRADICTORY):   Phase.UPDATE,
    (Phase.PROVE, Trans.RETRY):           Phase.PROVE,

    (Phase.EXTRACT, Trans.EXTRACTED):     Phase.DETECT,
    (Phase.EXTRACT, Trans.RETRY):         Phase.PROVE,
    (Phase.EXTRACT, Trans.CONTRADICTORY): Phase.UPDATE,

    (Phase.DETECT, Trans.NO_CYCLE):       Phase.UPDATE,
    (Phase.DETECT, Trans.RETRY):          Phase.PROVE,
    (Phase.DETECT, Trans.CONTRADICTORY):  Phase.UPDATE,

    (Phase.UPDATE, Trans.CHECKED):        Phase.CHECK,

    (Phase.CHECK, Trans.ALL_PROVED):      Phase.ASSEMBLING,
    (Phase.CHECK, Trans.HAS_PENDING):     Phase.SELECT,
    (Phase.CHECK, Trans.BLOCKED):         Phase.FAILED,

    (Phase.ASSEMBLING, Trans.ASSEMBLED):          Phase.DONE,
    (Phase.ASSEMBLING, Trans.ASSEMBLY_FAILED):    Phase.FAILED,
    (Phase.ASSEMBLING, Trans.RETRY):              Phase.PROVE,
}


# ═══════════════════════════════════════════════════════════════════════════════
# State
# ═══════════════════════════════════════════════════════════════════════════════

@dataclass
class LemmaContext:
    """Per-lemma communication channel between phases."""
    current_task: str = ""
    failure_context: str = ""
    needs_fresh_guide: bool = False
    needs_fresh_writer: bool = False
    # How many times this lemma has been re-activated because a child gave up.
    # Bounds the re-decompose loop (Bug #3): after MAX_REACTIVATIONS we stop
    # re-decomposing and propagate the failure further up instead.
    reactivations: int = 0


@dataclass
class PO5State:
    root_workspace: str = ""
    root_theorem_name: str = ""
    root_theorem_file: str = ""
    # Theorems the user explicitly requested. Empty = prove ALL sorry-theorems.
    requested_theorem_names: list[str] = field(default_factory=list)
    root_id: str = ""
    stage: str = "init"
    current_lemma_id: str = ""
    skip_soundness: bool = False
    # Cheat sheet (project-specific proof playbook) config. use_cheat_sheet=False
    # disables it entirely; cheat_sheet_path="" uses the bundled default.
    use_cheat_sheet: bool = True
    cheat_sheet_path: str = ""
    # TIER 2 backstop: hard upper bound (minutes) on the ENTIRE run wall-clock.
    # None ⇒ no hard stop (run until proved or the run is killed externally).
    max_run_minutes: float | None = None
    agent_registry: dict = field(default_factory=dict)
    lemma_ctx: dict = field(default_factory=dict)  # lemma_id → LemmaContext
    total_attempts: int = 0
    lemmas_proved: int = 0
    cycles_detected: int = 0
    # Full accumulated give-up reason(s), propagated to the Task Manager → user.
    give_up_reason: str = ""
    # If the guide, on giving up on a TOP-LEVEL requested theorem, says the user
    # must fix something (false/mis-stated goal, wrong def, missing hypothesis,
    # unavailable dependency), the specific request(s) are captured here.
    user_fix_request: str = ""


def _read_hint(state: PO5State) -> str:
    """'the cheat sheet and the file' / 'the file' depending on cheat-sheet config."""
    return "the cheat sheet and the file" if cheat_sheet_name(
        state.use_cheat_sheet, state.cheat_sheet_path) else "the file"


# ═══════════════════════════════════════════════════════════════════════════════
# Guide APIs — the only way to interact with the guide
# ═══════════════════════════════════════════════════════════════════════════════

# Tools blocked while the orchestrator drives the guide via run_ai for strategy /
# a decision. The guide's reply TEXT is already copied into the writer's next
# prompt, so a send_message here would double-message the writer AND auto-start
# its listener out of sequence. wait_for_reply is blocked too: a blocking wait
# during a synchronous decision call would stall the orchestrator. Passed as bare
# names — blocked_tools_hooks matches on the MCP tool's final `__` segment.
_GUIDE_DECISION_BLOCK = ["send_message", "wait_for_reply"]

# Inline reminder prepended to every strategy/decision prompt, matching
# _GUIDE_DECISION_BLOCK. Told UP FRONT so the guide simply answers inline instead
# of attempting a send_message that the block hook would deny — a denied call
# still costs a turn. The hook stays as the failsafe.
_GUIDE_DECISION_NO_MSG = (
    "⚠️ ANSWER INLINE ONLY. Your reply text below is delivered to the writer "
    "automatically — do NOT call send_message or wait_for_reply in this response "
    "(they are disabled for this turn). Just write your answer.\n\n"
)


async def _consult_guide_raw(agent, state: PO5State, ledger: LemmaLedger,
                              entry: LemmaEntry, cwd: Path,
                              task: str | None = None) -> str:
    """Send a prompt to the lemma's guide. Returns raw text.

    If task is None → prompt built from ctx.current_task + ctx.failure_context.
    If task is provided → sent as-is. Context is NOT consumed.
    """
    guide = await _get_guide(agent, entry, state, ledger)

    if task is None:
        ctx = state.lemma_ctx.get(entry.id)
        parts = []
        if ctx and ctx.current_task:
            parts.append(ctx.current_task)
        if ctx and ctx.failure_context:
            parts.append(f"⚠️ FAILURE:\n{ctx.failure_context}")
        task = "\n\n".join(parts) if parts else "Continue. Read the file and advise."

    result = await guide.run_ai(inp=_GUIDE_DECISION_NO_MSG + task,
                                block_tools=_GUIDE_DECISION_BLOCK)
    return result.raw_result or ""


async def _consult_guide_decide(agent, state: PO5State, ledger: LemmaLedger,
                                 entry: LemmaEntry, cwd: Path,
                                 options: list[str],
                                 task: str | None = None,
                                 post_prompt: str = "",
                                 post_prompt_parser: callable = None,
                                 ) -> tuple[str, str, dict]:
    """Send a prompt + force a structured decision.

    Returns (choice, reason, extras).
    extras is empty dict unless post_prompt_parser is provided.

    post_prompt: additional lines appended to the decision prompt (e.g. "TURNS: <50-100>")
    post_prompt_parser: callable(raw_text) -> dict of extra parsed fields
    """
    guide = await _get_guide(agent, entry, state, ledger)

    if task is None:
        ctx = state.lemma_ctx.get(entry.id)
        parts = []
        if ctx and ctx.current_task:
            parts.append(ctx.current_task)
        if ctx and ctx.failure_context:
            parts.append(f"⚠️ FAILURE:\n{ctx.failure_context}")
        task = "\n\n".join(parts) if parts else "Decide."

    options_str = " | ".join(options)
    prompt = (
        f"{_GUIDE_DECISION_NO_MSG}"
        f"{task}\n\n"
        f"DECIDE one of: [{options_str}]\n"
        f"Reply EXACTLY:\n"
        f"DECISION: <{options_str}>\n"
    )
    if post_prompt:
        prompt += post_prompt + "\n"
    prompt += "REASON: <one sentence>"

    result = await guide.run_ai(inp=prompt, block_tools=_GUIDE_DECISION_BLOCK)
    raw = result.raw_result or ""

    pattern = "|".join(re.escape(o) for o in options)
    match = re.search(rf'DECISION:\s*({pattern})', raw, re.IGNORECASE)
    reason_match = re.search(r'REASON:\s*(.+)', raw)

    decision = match.group(1).lower() if match else options[0]
    reason = reason_match.group(1).strip() if reason_match else raw[:100]
    extras = post_prompt_parser(raw) if post_prompt_parser else {}
    return decision, reason, extras


async def _dump_guide_to_disk(agent, state: PO5State, ledger: LemmaLedger,
                               entry: LemmaEntry, cwd: Path):
    """Legacy wrapper — rotation is now handled inside _get_guide/_get_writer."""
    pass


# ═══════════════════════════════════════════════════════════════════════════════
# Registration helper
# ═══════════════════════════════════════════════════════════════════════════════

def _register_lemma(state: PO5State, ledger: LemmaLedger, **kwargs) -> LemmaEntry | str:
    """Add lemma to ledger + initialize its LemmaContext."""
    entry = ledger.add_lemma(**kwargs)
    if not isinstance(entry, str):
        state.lemma_ctx[entry.id] = LemmaContext()
    return entry


def _propagate_failure_to_parent(state: PO5State, ledger: LemmaLedger,
                                  entry: LemmaEntry, message: str):
    """A child gave up — route the failure to the parent AND re-activate it so its
    guide can re-decompose differently, instead of leaving a dead child that gets
    the same give-up re-derived forever (Bug #3).

    Steps:
      1. Record the failure text on the parent's context (guide sees it next turn).
      2. Prune the failed child's subtree so its dead siblings/imports don't linger.
      3. Reset the parent to PENDING (priority-boosted) so SELECT re-picks it and
         its guide is asked for a DIFFERENT decomposition — bounded by
         MAX_REACTIVATIONS. Once exhausted, we stop re-activating and let the
         failure bubble further up (the parent itself will hit its own give-up).
    """
    from .lemma_ledger import LemmaStatus

    parent = ledger.get_parent(entry.id)
    if not parent:
        return

    parent_ctx = state.lemma_ctx.get(parent.id)
    if parent_ctx is None:
        parent_ctx = LemmaContext()
        state.lemma_ctx[parent.id] = parent_ctx

    # 1. Record failure text (append — parent may have multiple failed children).
    if parent_ctx.failure_context:
        parent_ctx.failure_context += f"\n{message}"
    else:
        parent_ctx.failure_context = message

    # 2. Prune the dead child's subtree (mark_failed already set the child FAILED;
    #    prune_branch skips PROVED/FAILED roots, so prune its children explicitly).
    for cid in list(entry.children):
        ledger.prune_branch(cid, f"parent child '{entry.name}' gave up")

    # 3. Re-activate the parent for a different decomposition, if budget remains.
    if parent_ctx.reactivations >= MAX_REACTIVATIONS:
        # Exhausted: don't churn. Leave the parent as-is; when SELECT finds no
        # pending work under it, _phase_check escalates (and the parent's own
        # give-up will propagate one level further up).
        return
    parent_ctx.reactivations += 1
    parent_ctx.needs_fresh_guide = True
    parent_ctx.needs_fresh_writer = True
    parent_ctx.current_task = (
        f"A previous decomposition failed: {message}\n"
        f"Re-decompose '{parent.name}' DIFFERENTLY — the earlier split recreated an "
        f"unprovable/false obligation. Do NOT reproduce the same child."
    )
    ledger.mark_pending(parent.id, priority_boost=True)


# ═══════════════════════════════════════════════════════════════════════════════
# Main entry point
# ═══════════════════════════════════════════════════════════════════════════════

async def run_workflow(agent, inp: Any, result_type: type[T] | None = None):
    from .._types import AgentResult, AgentStatus

    start_time = _time.time()
    await agent._emit("status_change", "running")
    agent._po4_start_time = start_time

    cwd = Path(agent._cwd) if agent._cwd else Path.cwd()

    # Parse input
    if isinstance(inp, dict):
        workspace_rel = inp.get("workspace", "")
        # theorem_names: explicit list of targets. Empty/absent → prove ALL
        # sorry-theorems in the file. `theorem_name` (singular) is accepted for
        # backward compatibility and folded into the list.
        theorem_names = list(inp.get("theorem_names") or [])
        single = inp.get("theorem_name", "")
        if single and single not in theorem_names:
            theorem_names.append(single)
        theorem_file = inp.get("theorem_file", "")
        skip_soundness = inp.get("skip_soundness", False)
        use_cheat_sheet = inp.get("use_cheat_sheet", True)
        cheat_sheet_path = inp.get("cheat_sheet_path", "") or ""
        max_run_minutes = inp.get("max_run_minutes", None)
    else:
        workspace_rel = str(inp) if inp else ""
        theorem_names, theorem_file = [], ""
        skip_soundness = False
        use_cheat_sheet = True
        cheat_sheet_path = ""
        max_run_minutes = None

    if not workspace_rel:
        return AgentResult(name=agent.spec.name, status=AgentStatus.FAILED,
                           output={"phase": "failed", "error": "no workspace"})

    state = _load_state(cwd, workspace_rel)
    if not state:
        state = PO5State(
            root_workspace=workspace_rel,
            requested_theorem_names=theorem_names,
            root_theorem_file=theorem_file,
            skip_soundness=skip_soundness,
            use_cheat_sheet=use_cheat_sheet,
            cheat_sheet_path=cheat_sheet_path,
            max_run_minutes=(float(max_run_minutes) if max_run_minutes else None),
        )

    ledger = LemmaLedger(cwd / workspace_rel / "lemma_ledger.json")
    agent._workflow_state = state

    # Stale state recovery: if state references a lemma not in ledger, reset to init
    if state.stage != "init" and state.current_lemma_id:
        if ledger.get(state.current_lemma_id) is None:
            await agent._emit("message", "[PO5] Stale state (lemma not in ledger) — resetting to init")
            state.stage = "init"
            state.current_lemma_id = ""
            state.root_id = ""

    _target_desc = ", ".join(theorem_names) if theorem_names else "ALL sorry-theorems"
    await agent._emit("message", f"[PO5] Starting: {_target_desc} in {workspace_rel} (phase={state.stage})")

    # ─── INIT ─────────────────────────────────────────────────────────────
    if state.stage == "init":
        await agent._emit("message", "[PO5] Phase: INIT")
        stub_rel = f"{workspace_rel}/Stub.lean"

        if not (cwd / workspace_rel / "Stub" / "Def.lean").exists():
            await run_splitter(agent, workspace_rel, stub_rel)

        stub_clean = cwd / workspace_rel / "Stub.clean.lean"
        if not stub_clean.exists():
            shutil.copy2(cwd / stub_rel, stub_clean)

        # Copy the cheat sheet into the sandbox so the guide can read it. This is
        # a common silent-failure point: if the configured path doesn't resolve
        # against cwd, copy_cheat_sheet returns None and the guide later reports
        # "cheat sheet inaccessible". Surface the outcome explicitly.
        if state.use_cheat_sheet:
            copied = copy_cheat_sheet(cwd, cwd / workspace_rel,
                                      state.use_cheat_sheet, state.cheat_sheet_path)
            if copied:
                await agent._emit("message",
                    f"[PO5] Cheat sheet ready in sandbox: {copied}")
            else:
                src = cheat_sheet_source(cwd, state.use_cheat_sheet, state.cheat_sheet_path)
                cfg = state.cheat_sheet_path or "(bundled default)"
                await agent._emit("message",
                    f"[PO5] ⚠️ Cheat sheet ENABLED but NOT copied — guide will run "
                    f"WITHOUT it. Configured path: {cfg}; resolved source: "
                    f"{src or 'NOT FOUND'} (cwd: {cwd}).")

        tools = get_lean_tools()
        split = tools.split_theorems(stub_rel)
        if not split.blocks:
            state.stage = "failed"
            _save_state(cwd, state)
            return AgentResult(name=agent.spec.name, status=AgentStatus.FAILED,
                               output={"phase": "failed", "error": "no theorems in Stub.lean"})

        # Collect top-level proof obligations ("targets"): each standalone
        # theorem/def with sorry, or a whole mutual group (collapsed to one
        # representative) containing sorry.
        all_targets = _collect_sorry_targets(split)

        # Narrow to the user's requested theorems if any were named; an empty
        # request means "prove ALL sorry-theorems in the file".
        targets = _filter_requested_targets(
            all_targets, split, state.requested_theorem_names)
        if state.requested_theorem_names:
            matched = {b.name for b, _ in targets}
            unmatched = [n for n in state.requested_theorem_names
                         if n not in matched and not any(
                             b.mutual_group is not None
                             and n in split.mutual_groups.get(b.mutual_group, [])
                             for b, _ in targets)]
            if unmatched:
                await agent._emit("message",
                    f"[PO5] Requested theorems with no sorry / not found (skipped): {unmatched}")
            if not targets:
                await agent._emit("message",
                    "[PO5] None of the requested theorems have sorry — proving all sorry-targets instead")
                targets = all_targets

        # Decide single-root vs. synthetic-file-root.
        # Single root (behavior unchanged) when there is at most one target.
        # Synthetic root when ≥2 targets share the file — each becomes a child
        # obligation under a "whole file proved" root.
        if len(targets) <= 1:
            if targets:
                root_block = targets[0][0]
            else:
                # Nothing has sorry — register the last declaration so CHECK can
                # immediately recognize the file as already proven.
                root_block = split.blocks[-1]
            state.root_theorem_name = root_block.name

            sig_hash = LemmaLedger.compute_signature_hash(root_block.text)
            root_entry = _register_lemma(state, ledger,
                name=state.root_theorem_name, file_path=stub_rel,
                workspace=workspace_rel, signature_hash=sig_hash,
                statement=root_block.text,
            )
            if isinstance(root_entry, str):
                state.stage = "failed"
                _save_state(cwd, state)
                return AgentResult(name=agent.spec.name, status=AgentStatus.FAILED,
                                   output={"phase": "failed", "error": root_entry})
            state.root_id = root_entry.id
        else:
            # Multiple sorry-targets in one file: synthetic "file" root whose
            # completion means "every target in Stub.lean is sorry-free". It is
            # never proven by a writer — _propagate_proved promotes it once its
            # whole subtree (the shared file) is sorry-free.
            file_label = f"<file:{workspace_rel}/Stub.lean>"
            state.root_theorem_name = file_label
            root_entry = _register_lemma(state, ledger,
                name=file_label, file_path=stub_rel,
                workspace=workspace_rel,
                signature_hash=LemmaLedger.compute_signature_hash(file_label),
                statement=f"-- all {len(targets)} top-level theorems in {stub_rel} proved",
            )
            if isinstance(root_entry, str):
                state.stage = "failed"
                _save_state(cwd, state)
                return AgentResult(name=agent.spec.name, status=AgentStatus.FAILED,
                                   output={"phase": "failed", "error": root_entry})
            state.root_id = root_entry.id
            ledger.mark_contingent(root_entry.id)

            registered = 0
            for block, is_mut in targets:
                child = _register_lemma(state, ledger,
                    name=block.name, file_path=stub_rel,
                    workspace=workspace_rel,
                    signature_hash=LemmaLedger.compute_signature_hash(block.text),
                    statement=block.text, is_mutual=is_mut,
                    parent_id=root_entry.id)
                if not isinstance(child, str):
                    registered += 1
            await agent._emit("message",
                f"[PO5] Multi-theorem file: registered {registered} sorry-targets under synthetic root")

        state.stage = "select"
        ledger.save()
        _save_state(cwd, state)
        await agent._emit("state_transition", {"from": "init", "transition": "registered", "to": "select"})

    # Reset any PROVING entries to PENDING (crash recovery)
    for e in ledger.entries():
        if e.status == LemmaStatus.PROVING:
            e.status = LemmaStatus.PENDING

    # ─── State machine loop ───────────────────────────────────────────────
    HANDLERS = {
        Phase.SELECT:     lambda: _phase_select(agent, state, ledger, cwd),
        Phase.PROVE:      lambda: _phase_prove(agent, state, ledger, cwd),
        Phase.EXTRACT:    lambda: _phase_extract(agent, state, ledger, cwd),
        Phase.DETECT:     lambda: _phase_detect(agent, state, ledger, cwd),
        Phase.UPDATE:     lambda: _phase_update(agent, state, ledger, cwd),
        Phase.CHECK:      lambda: _phase_check(agent, state, ledger, cwd),
        Phase.ASSEMBLING: lambda: _phase_assemble(agent, state, ledger, cwd),
    }

    while state.stage not in ("done", "failed") and not agent.cancellation.is_cancelled:
        try:
            phase = Phase(state.stage)
        except ValueError:
            await agent._emit("message", f"[PO5] ERROR: invalid stage '{state.stage}'")
            state.stage = "failed"
            break

        handler = HANDLERS.get(phase)
        if not handler:
            state.stage = "failed"
            break

        transition = await handler()
        next_stage = TRANSITIONS.get((phase, transition))
        if next_stage is None:
            await agent._emit("message", f"[PO5] ERROR: no transition ({state.stage}, {transition.value})")
            state.stage = "failed"
            break

        await agent._emit("state_transition", {
            "from": state.stage, "transition": transition.value, "to": next_stage.value})
        state.stage = next_stage.value
        ledger.save()
        _save_state(cwd, state)

    # ─── Done ─────────────────────────────────────────────────────────────
    # Tear down every persistent writer/guide listen task. Most instances are
    # cached on `agent` per lemma-id and reused (never rotated/cleaned up on the
    # proved path), so their _listen_messages tasks would otherwise outlive the
    # workflow — a 1s-polling coroutine per instance holding a backend. Sweep all
    # of them here so no listener leaks past the run.
    await _stop_all_listeners(agent)

    elapsed = _time.time() - start_time
    total_cost = getattr(agent.swarm, '_total_cost', 0.0) if hasattr(agent, 'swarm') else 0.0
    await agent._emit("message",
        f"[PO5] Finished: stage={state.stage}, proved={state.lemmas_proved}, "
        f"cycles={state.cycles_detected}, time={elapsed/60:.1f}min, cost=${total_cost:.2f}")
    ledger.save()

    # Checkpoint swarm state
    if hasattr(agent, 'swarm') and hasattr(agent.swarm, '_checkpoint_manager') and agent.swarm._checkpoint_manager:
        try:
            agent.swarm._checkpoint_manager.save("prover_done")
        except Exception:
            pass

    status = AgentStatus.COMPLETED if state.stage == "done" else AgentStatus.FAILED
    return AgentResult(name=agent.spec.name, status=status,
                       output={"stage": state.stage, "proved": state.lemmas_proved,
                               "cycles": state.cycles_detected,
                               # Full give-up reason(s) + any user-fix request, so
                               # the Task Manager can relay them to the user.
                               "give_up_reason": state.give_up_reason,
                               "user_fix_request": state.user_fix_request})


# ═══════════════════════════════════════════════════════════════════════════════
# Phase: SELECT
# ═══════════════════════════════════════════════════════════════════════════════

async def _phase_select(agent, state: PO5State, ledger: LemmaLedger, cwd: Path) -> Trans:
    """Pick next lemma. Parent's guide chooses among pending children."""
    if not ledger.has_pending():
        return Trans.BLOCKED

    parent_entry, pending_kids = _find_dfs_candidates(ledger, state.current_lemma_id)

    if not pending_kids:
        lemma = ledger.pick_next()
        if lemma is None:
            return Trans.BLOCKED
        state.current_lemma_id = lemma.id
        ledger.mark_proving(lemma.id)
        await agent._emit("message", f"[PO5] Selected (fallback): {lemma.name}")
        return Trans.PICKED

    if len(pending_kids) == 1:
        winner = pending_kids[0]
        state.current_lemma_id = winner.id
        ledger.mark_proving(winner.id)
        await agent._emit("message", f"[PO5] Selected (only child): {winner.name}")
        return Trans.PICKED

    # Multiple candidates — ask parent's guide
    if parent_entry:
        children_desc = "\n".join(
            f"  {i+1}. {c.name} (depth={c.depth}) (#lemmas using this={len(ledger.get_all_parents(c.id))}) — {(c.statement or '')[:80]}"
            for i, c in enumerate(pending_kids))
        decision, reason, _extras = await _consult_guide_decide(
            agent, state, ledger, parent_entry, cwd,
            options=[c.id[:8] for c in pending_kids],
            task=(
                f"Your lemma '{parent_entry.name}' has these pending children:\n{children_desc}\n\n"
                f"Which should we prove NEXT? Pick the hardest/most general one."
            ))
        for c in pending_kids:
            if c.id.startswith(decision) or decision in c.name.lower():
                state.current_lemma_id = c.id
                ledger.mark_proving(c.id)
                await agent._emit("message", f"[PO5] Guide selected: {c.name}")
                return Trans.PICKED

    # Fallback
    pending_kids.sort(key=lambda e: (len(ledger.get_all_parents(e.id)), -e.depth, -e.attempts), reverse=True)
    winner = pending_kids[0]
    state.current_lemma_id = winner.id
    ledger.mark_proving(winner.id)
    await agent._emit("message", f"[PO5] Selected (depth fallback): {winner.name}")
    return Trans.PICKED


# ═══════════════════════════════════════════════════════════════════════════════
# Phase: PROVE
# ═══════════════════════════════════════════════════════════════════════════════

async def _phase_prove(agent, state: PO5State, ledger: LemmaLedger, cwd: Path) -> Trans:
    """Attempt proof of current lemma via guide + writer loop."""
    entry = ledger.get(state.current_lemma_id)
    result = await _attempt_prove(agent, state, ledger, entry, cwd)
    state.total_attempts += 1

    if result == "proved":
        state.lemmas_proved += 1
        return Trans.PROVED
    elif result == "contingent":
        return Trans.CONTINGENT
    elif result == "has_sorry":
        return Trans.HAS_SORRY
    elif result == "retry":
        return Trans.RETRY
    else:
        if entry.status != LemmaStatus.FAILED:
            ledger.mark_failed(entry.id, result)
            _propagate_failure_to_parent(state, ledger, entry, f"Child '{entry.name}' failed: {result}")
        return Trans.CONTRADICTORY


async def _attempt_prove(agent, state: PO5State, ledger: LemmaLedger,
                         entry: LemmaEntry, cwd: Path) -> str:
    """Guide-driven proof loop. Returns: proved | has_sorry | failed | retry"""
    tools = get_lean_tools()
    ctx = state.lemma_ctx.get(entry.id)
    if not ctx:
        ctx = LemmaContext()
        state.lemma_ctx[entry.id] = ctx

    stub_rel = _resolve_stub(entry, cwd, state)

    # Repair inconsistent state: if decomposed/ exists but Stub.lean doesn't import from it,
    # the extraction was lost (e.g. process crash). Re-add imports to make the file slim.
    _repair_orphaned_decomposed(entry, cwd, stub_rel)

    original_content = (cwd / stub_rel).read_text()

    # Ensure the cheat sheet (if any) exists in the workspace
    ws_path = cwd / entry.workspace
    copy_cheat_sheet(cwd, ws_path, state.use_cheat_sheet, state.cheat_sheet_path)

    writer = await _get_writer(agent, entry, state, ledger)
    # Keep the writer live and reactive for the WHOLE lemma. Between chunks (when no
    # run_ai drives it) this lets the guide's decision-phase questions reach the
    # writer immediately; during a chunk the writer's own run_ai owns the session
    # (via _driving_lock) and this listener parks. See _ensure_listening.
    _ensure_listening(agent, writer)
    verify_fn = _make_verifier(entry, stub_rel, original_content, ledger, cwd)
    protected_names = _get_protected_names(tools, stub_rel, entry)

    # In a shared multi-theorem file, tell the writer to touch ONLY its target and
    # leave sibling obligations' sorry in place (they are proved in their own turn).
    siblings = _sibling_target_names(ledger, entry, cwd, stub_rel)
    scope_note = ""
    if siblings:
        scope_note = (
            f"\n\n⚠️ SHARED FILE: prove ONLY {sorted(protected_names)}. "
            f"Other theorems here ({sorted(siblings)}) are proved separately — "
            f"leave their `sorry` untouched and do NOT modify or delete them."
        )

    # ── Step 1: Initial advice ──
    if ctx.current_task or ctx.failure_context:
        await agent._emit("message", f"[PO5] Guide: directed task for {entry.name}")
        advice = await _consult_guide_raw(agent, state, ledger, entry, cwd, task=None)
    else:
        ledger_summary = _build_ledger_summary(ledger, entry)
        await agent._emit("message", f"[PO5] Guide: initial strategy for {entry.name}")
        advice = await _consult_guide_raw(agent, state, ledger, entry, cwd,
            task=(
                f"CONTEXT:\n{ledger_summary}\n\n"
                f"We are proving '{entry.name}' in {stub_rel}.\n"
                f"Read {_read_hint(state)}, then advise on the best approach.\n"
                f"Also specify TURNS: <{MIN_CHUNK_TURNS}-{MAX_CHUNK_TURNS}> for how many turns "
                f"the writer should get for the first attempt."
            ))

    # ── Step 2: Main loop ──
    total_turns = 0
    prev_sorry_count = None
    chunks_this_call = 0
    loop_start = _time.time()
    # Extract initial turns from guide's advice
    turns_match = re.search(r'TURNS:\s*(\d+)', advice)
    chunk_budget = max(MIN_CHUNK_TURNS, min(MAX_CHUNK_TURNS, int(turns_match.group(1)))) if turns_match else CHUNK_TURNS

    while True:
        ledger.increment_attempts(entry.id)
        chunks_this_call += 1
        # ── Backstops ─────────────────────────────────────────────────────────
        # The guide drives strategy, but it must not spin forever on a target it
        # can neither close nor abandon. Two independent tiers plus a hard chunk cap:
        #   TIER 1 (flexible): NO-PROGRESS budget — minutes since the last chunk that
        #     STRICTLY reduced the transitive open-sorry count. A proof that keeps
        #     shedding sorries never trips it; only genuine stalling does. The guide
        #     may grant bounded extensions (EXTEND_MINUTES) that add to this budget.
        #   TIER 2 (hard): absolute run wall-clock vs state.max_run_minutes. None ⇒
        #     no stop. This is unconditional — no decompose escape hatch.
        #   MAX_CHUNKS_PER_LEMMA: fixed runaway guard (independent of the clocks).
        now = _time.time()
        # First iteration: no progress recorded yet — anchor the idle clock to loop start.
        if not hasattr(entry, '_last_progress_time'):
            entry._last_progress_time = loop_start
        idle_minutes = (now - entry._last_progress_time) / 60.0
        idle_budget = LEMMA_IDLE_MINUTES + getattr(entry, '_idle_extension_minutes', 0.0)
        run_minutes = (now - getattr(agent, '_po4_start_time', now)) / 60.0
        hard_stop = (state.max_run_minutes is not None
                     and run_minutes > state.max_run_minutes)
        tier1_stop = idle_minutes > idle_budget
        chunk_stop = chunks_this_call > MAX_CHUNKS_PER_LEMMA
        if hard_stop:
            # TIER 2: unconditional — the whole RUN has blown its user-set ceiling.
            # Do not attempt decompose; stop and propagate immediately.
            reason = (f"hard run-level backstop: {run_minutes:.0f}min ≥ "
                      f"max_run_minutes={state.max_run_minutes:.0f} (set via "
                      f"--max-run-minutes); stopping on '{entry.name}'")
            await agent._emit("message", f"[PO5] ⛔ {reason}")
            ctx.failure_context = f"Backstop give-up: {reason}"
            ledger.mark_failed(entry.id, f"Backstop give-up: {reason}")
            _record_give_up(state, entry, f"Backstop give-up: {reason}")
            _propagate_failure_to_parent(state, ledger, entry, f"Child '{entry.name}' hit run cap: {reason}")
            return "failed"
        if tier1_stop or chunk_stop:
            reason = (f"runaway backstop: {chunks_this_call} chunks / "
                      f"{idle_minutes:.0f}min idle (budget {idle_budget:.0f}min) "
                      f"on '{entry.name}' with no resolution")
            await agent._emit("message", f"[PO5] ⛔ {reason}")
            # Last resort: if a decomposition is possible, take it (a fresh subtree
            # may crack what inline attempts could not). Otherwise give up cleanly.
            if entry.depth < MAX_DEPTH:
                decompose_ok = await _validate_decompose(
                    agent, state, ledger, entry, cwd, tools, stub_rel, protected_names)
                if decompose_ok is True:
                    await agent._emit("message", "[PO5] Backstop → forced decompose")
                    break
            ctx.failure_context = f"Backstop give-up: {reason}"
            ledger.mark_failed(entry.id, f"Backstop give-up: {reason}")
            _record_give_up(state, entry, f"Backstop give-up: {reason}")
            await _ask_guide_user_fix(agent, state, ledger, entry, cwd, f"Backstop give-up: {reason}")
            _propagate_failure_to_parent(state, ledger, entry, f"Child '{entry.name}' hit backstop: {reason}")
            return "failed"
        elapsed = _time.time() - getattr(agent, '_po4_start_time', _time.time())
        writer_pct = await writer.get_context_percentage()
        # _get_guide handles rotation internally if >= 75%
        guide = await _get_guide(agent, entry, state, ledger)
        # Keep the guide live and reactive for the WHOLE lemma via a persistent
        # listen task (idempotent; re-ensured each iteration in case the guide
        # rotated to a fresh instance). While the writer proves this chunk the guide
        # is not being driven by run_ai, so its listener answers the writer in real
        # time; when the orchestrator later calls run_ai on the guide for its
        # review/decision, run_ai owns the session and the listener parks.
        _ensure_listening(agent, guide)
        # Open the live writer↔guide channel for THIS chunk. Re-established every
        # iteration because either instance may have rotated (new name). Both
        # instances now listen persistently, so a writer→guide message lands in
        # real time and the guide can reply on the same channel.
        guide_name = _link_writer_guide(agent, writer, guide)
        guide_pct = await guide.get_context_percentage()
        await agent._emit("message",
            f"[PO5] Chunk {entry.attempts} ({chunk_budget}t, total={total_turns}) "
            f"[{elapsed/60:.1f}min] | writer: {writer_pct or 0:.0f}% | guide: {guide_pct or 0:.0f}%")

        # Writer works. The guide is already live in its own persistent listen task
        # (_ensure_listening above), so it answers the writer's mid-chunk messages
        # in real time — no per-chunk gather/cancel dance, and the guide is NOT torn
        # down at the chunk boundary. The writer's run_ai holds _driving_lock for
        # the whole chunk; if it messages the guide and waits, the reply is injected
        # at the writer's next turn boundary (run_ai's own between-turn mailbox pull).
        chunk = min(MAX_CHUNK_TURNS, max(MIN_CHUNK_TURNS, chunk_budget))
        outcome = await verified_loop(
            agent_ctx=writer,
            initial_input=(
                f"STRATEGY ADVICE from your proof guide:\n{advice}\n\n"
                f"You have {chunk} turns. File MUST compile (sorry allowed).{scope_note}\n\n"
                f"Your proof guide '{guide_name}' is live RIGHT NOW while you work and "
                f"answers in real time. Keep proving — do NOT block waiting on it. If you "
                f"hit something strategic — the goal looks false or mis-stated, the "
                f"signature seems unprovable as written, a lemma you need is missing, or "
                f"you're stuck in a way tactics alone won't fix — report it with "
                f"send_message(to=\"{guide_name}\", message=\"...\") and KEEP WORKING; its "
                f"reply reaches you at your next turn. Only if you genuinely cannot proceed "
                f"without the answer, follow up with wait_for_reply(sender=\"{guide_name}\", "
                f"timeout=<seconds you expect it to take>) — pick a short timeout for a quick "
                f"check, a longer one for a deep architectural call. Do NOT message for "
                f"routine compile errors — fix those yourself."
            ),
            verify=verify_fn, max_rounds=2, max_turns=chunk, use_run_ai=True,
        )

        total_turns += chunk
        await agent._emit("message", f"[PO5] Writer finished chunk {entry.attempts} ({total_turns} total turns)")

        # Build the AUTHORITATIVE dependency+sorry overview ONCE. This single
        # source of truth drives (a) the proved/contingent gate, (b) the guide's
        # progress metric, and (c) the guide-facing overview. It joins in-file
        # dependency edges (comment-stripped, word-boundary, transitively closed)
        # + the module-SAFE `#print axioms` verdict (build + non-module scratch;
        # never run in-place inside a `module`) + sorry positions. The guide no
        # longer reasons from stale memory or snapshot line numbers.
        tsm = tools.transitive_sorry_map(stub_rel, sorted(protected_names))
        cr = tools.check_compiles(stub_rel)

        # Check: proved? (TARGET-SCOPED — a shared file may hold sibling theorems
        # whose sorry is not ours to close, so we gate on the protected targets.)
        if cr.success and tsm.build_ok and protected_names and all(
                tsm.targets[n].done for n in protected_names if n in tsm.targets):
            ledger.mark_proved(entry.id, stub_rel.replace("/", ".").removesuffix(".lean"))
            return "proved"

        # Not (yet) proved. If the writer's OWN block is locally sorry-free but the
        # target is transitively unproven, decide whether it is (a)/(b) someone
        # else's job — a sibling obligation proved separately, or a registered
        # child still being proved → park as contingent, _propagate_proved promotes
        # us later — or whether the target depends on writer-created INLINE helpers
        # that still need work. `siblings` EXCLUDES inline helpers.
        local_sorry = tools.get_sorries_by_theorem(stub_rel)
        protected_local_sorry = sum(len(local_sorry.get(n, [])) for n in protected_names)
        if cr.success and tsm.build_ok and protected_local_sorry == 0:
            sibling_sorry = any(
                n in siblings and positions
                for n, positions in local_sorry.items())
            if sibling_sorry or entry.children:
                ledger.mark_contingent(entry.id)
                return "contingent"

        # Reachable in-file helpers the TARGET depends on that still carry a
        # LITERAL sorry, excluding the protected targets themselves and genuine
        # siblings. These are the writer's real pending obligations even when its
        # own block reads clean (it factored the goal into inline `sorry` helpers).
        # Filter on has_local_sorry (a literal token), NOT the axioms verdict's
        # open_deps: when the build is RED the verdict marks EVERY reachable decl
        # has_transitive_sorry=True, which in the endgame (0 sorries, still fixing
        # compile errors) would falsely flag clean helpers and contradict the
        # positive endgame framing.
        open_deps_all: set[str] = set()
        for t in protected_names:
            if t in tsm.targets:
                open_deps_all |= set(tsm.targets[t].open_deps)
        transitive_inline_sorry_info = {
            n: [tsm.decls[n].start] for n in sorted(open_deps_all)
            if n not in protected_names and n not in siblings and n in tsm.decls
            and tsm.decls[n].has_local_sorry
        }

        # Progress metric: the number of literal `sorry` TOKENS in OUR obligations
        # (protected targets + the inline helpers they depend on), excluding
        # siblings whose sorries other branches own. This is the LEAF-sorry count —
        # deliberately NOT tsm.open_sorry_count(), which counts distinct reachable
        # decls via the axioms verdict. That decl-count had two failure modes on the
        # critical path, both of which this replaces:
        #   * BUILD RED → the axioms oracle can't confirm anything, so every
        #     reachable decl reads has_transitive_sorry=True and the count freezes
        #     at the reachable-decl total. A proof with 0 real sorries but compile
        #     errors then looked identical to a genuine stall (idle clock never
        #     reset, backstop could kill a nearly-done proof).
        #   * 1:1 FACTORING → moving a sorry from the target into a fresh inline
        #     helper spawns a new reachable decl, so the decl-count SPIKED upward
        #     (4→5) on healthy decomposition — the very signal feeding decompose /
        #     give-up. Leaf-count stays flat when a sorry just moves.
        # For display: literal-sorry positions, partitioned protected vs sibling.
        sorry_info = local_sorry
        protected_sorry_info = {n: sorry_info.get(n, []) for n in protected_names if sorry_info.get(n)}
        sibling_sorry_info = {n: v for n, v in sorry_info.items()
                              if n not in protected_names and v}
        # Our leaf-sorries = every literal sorry position EXCEPT those in sibling
        # obligations. Covers protected targets + writer-created inline helpers.
        sorry_count = sum(len(v) for n, v in sorry_info.items() if n not in siblings)
        file_compiles_now = cr.success
        # ENDGAME: 0 leaf-sorries but the file does not compile yet. The writer has
        # replaced the last sorry with a real proof and is closing compile errors on
        # the full statement — the single most forward state there is. Treated as
        # progress below (resets the idle clock) and framed positively to the guide,
        # so a proof one tactic from done is never scored as a stall.
        finishing_compile = (sorry_count == 0 and not file_compiles_now)
        progress = _format_progress(prev_sorry_count, sorry_count, compiles=file_compiles_now)
        prior_sorry_count = prev_sorry_count  # snapshot BEFORE overwrite (stuck check)
        prev_sorry_count = sorry_count
        writer_pct = await writer.get_context_percentage()

        # Guide reviews → next advice
        compile_note = ""
        if not outcome.success and outcome.last_error:
            compile_note = f"\n⚠️ COMPILATION FAILED after {outcome.rounds} fix rounds: {outcome.last_error}\n"
        sibling_note = (
            f"\nNOT YOUR TASK — sibling sorries owned by other branches (ignore): {sibling_sorry_info}\n"
            if sibling_sorry_info else "")
        # The writer factored the target into inline `sorry` helpers, so its own
        # protected block reads clean while the target is still TRANSITIVELY
        # unproven. Make this explicit — otherwise the guide sees an empty sorry
        # set, believes the branch is done, and loops `continue` forever. These
        # inline helpers are YOURS: either close them inline or `decompose` to
        # extract them into their own files.
        transitive_note = (
            f"\n⚠️ TARGET NOT DONE — your block has NO literal sorry, but it is "
            f"TRANSITIVELY UNPROVEN: the writer left `sorry` in inline helpers it "
            f"created, which your goal depends on. These ARE your obligation — "
            f"close them inline or `decompose` to extract them: "
            f"{transitive_inline_sorry_info}\n"
            if transitive_inline_sorry_info else "")
        from .._snapshot_mcp import snapshot_summary
        snap_summary = snapshot_summary(cwd, entry.workspace)
        snap_note = f"\n{snap_summary}\n" if snap_summary else ""
        sorry_map = _format_sorry_map(tsm, set(protected_names), siblings)
        # In the endgame (0 sorries, not yet compiling) `progress` already frames the
        # non-compile positively; only tack on the alarming "(NOT COMPILING)" when
        # there is still open work, so a near-done proof doesn't read as a stall.
        _compile_suffix = ' (NOT COMPILING)' if (compile_note and not finishing_compile) else ''
        await agent._emit("message", f"[PO5] Guide reviews: {progress}{_compile_suffix}")
        advice = await _consult_guide_raw(agent, state, ledger, entry, cwd,
            task=(
                f"Writer completed chunk {entry.attempts} ({total_turns} total turns).\n"
                f"{_runway_note(writer_pct)}\n"
                f"{progress}\nFile: {stub_rel}\n"
                f"{sorry_map}"
                f"{transitive_note}"
                f"{sibling_note}"
                f"{snap_note}"
                f"{compile_note}"
                f"Focus on STRATEGY and overall progress. Compilation errors (if any) are "
                f"the writer's to fix — only flag them if you believe the writer cannot fix "
                f"them or they signal a wrong direction. Watch the snapshot trajectory for "
                f"regression. Diagnose and advise what to try next."
            ))

        # Guide decides. We also let the guide independently call for a snapshot
        # of the CURRENT state (a strategic cross-check on the writer's own
        # judgment) — but only when the file compiles, since a snapshot of a
        # non-compiling file would be rejected anyway.
        file_compiles = tools.check_compiles(stub_rel).success

        def _parse_turns(raw: str) -> dict:
            out = {}
            m = re.search(r'TURNS:\s*(\d+)', raw)
            if m:
                out["turns"] = int(m.group(1))
            sm = re.search(r'SNAPSHOT:\s*(yes|no)', raw, re.IGNORECASE)
            if sm and sm.group(1).lower() == "yes":
                out["snapshot"] = True
                tm = re.search(r'SNAPSHOT_TAG:\s*(.+)', raw)
                out["snapshot_tag"] = tm.group(1).strip() if tm else "guide-checkpoint"
            em = re.search(r'EXTEND_MINUTES:\s*(\d+)', raw)
            if em:
                out["extend_minutes"] = int(em.group(1))
            return out

        # Track consecutive no-reduction chunks. Progress = the leaf-sorry count
        # STRICTLY decreased this chunk. A chunk that closes an inline helper counts
        # as progress; a chunk that merely MOVES a sorry into a fresh helper does not
        # inflate the count (leaf-count is flat under 1:1 factoring), so it is
        # neither scored as progress nor as a stall. Compare against the value
        # captured BEFORE we overwrote prev_sorry_count above.
        if not hasattr(entry, '_stuck_count'):
            entry._stuck_count = 0
        made_progress = (
            prior_sorry_count is not None and sorry_count < prior_sorry_count)
        # `finishing_compile` (computed above): 0 leaf-sorries but not yet compiling.
        # It must NOT be scored as a stall — the axioms-verdict count used to read
        # this as "still N open, NOT COMPILING" and let the idle clock run toward a
        # backstop that could kill a proof one tactic from done.
        still_open = sorry_count > 0
        if still_open and not made_progress:
            entry._stuck_count = getattr(entry, '_stuck_count', 0) + 1
        else:
            entry._stuck_count = 0
        # Endgame credit is BOUNDED. `finishing_compile` counts as progress (resets
        # the idle clock) only for the first ENDGAME_GRACE_CHUNKS chunks — enough for
        # a writer that is genuinely one-tactic-away, but not a licence to reset the
        # backstop forever on a compile the writer can never close. After the grace
        # window the idle clock is allowed to age again so the flexible/hard
        # backstops can still fire on a truly wedged endgame.
        if finishing_compile:
            entry._endgame_count = getattr(entry, '_endgame_count', 0) + 1
        else:
            entry._endgame_count = 0
        endgame_credit = finishing_compile and entry._endgame_count <= ENDGAME_GRACE_CHUNKS
        # Record the moment of last real progress so the flexible per-lemma
        # backstop (Fix B) measures time-SINCE-PROGRESS, not raw wall-clock — a
        # proof that is still shedding sorries (or, within the grace window, closing
        # out the final compile errors with no sorries left) must not be killed.
        if made_progress or endgame_credit or prior_sorry_count is None:
            entry._last_progress_time = _time.time()

        stuck_hint = ""
        if finishing_compile and entry._endgame_count > ENDGAME_GRACE_CHUNKS:
            # 0 sorries but stuck on the SAME broken proof for several chunks — this
            # is NOT a decompose situation (there is nothing left to extract). Steer
            # the guide toward recovering a compiling snapshot or a fresh approach.
            stuck_hint = (
                f"\n⚠️ ENDGAME STALL: {entry._endgame_count} chunks with 0 sorries but the "
                f"proof still does NOT compile. The writer replaced the last sorry with a "
                f"proof it cannot make compile. Do NOT decompose (nothing to extract). "
                f"Consider read_snapshot(<best compiling tag>) to recover the last green "
                f"state, or fresh_start for a different closing tactic.\n"
            )
        elif entry._stuck_count >= 3:
            stuck_hint = (
                f"\n⚠️ STUCK: {entry._stuck_count} consecutive chunks with no sorry reduction. "
                f"Consider decompose even if the writer still has runway — after this many "
                f"idle chunks the writer may simply be unable to close these obligations in "
                f"the current file.\n"
            )
        if transitive_inline_sorry_info:
            stuck_hint += (
                f"\n⚠️ Your block is locally sorry-free but TRANSITIVELY UNPROVEN via inline "
                f"helpers ({sorted(transitive_inline_sorry_info)}). `continue` only helps if the "
                f"writer will close them inline; otherwise choose `decompose` to extract them.\n"
            )

        # Flexible TIER-1 backstop status for the guide. The idle clock is measured
        # from the last chunk that reduced the transitive sorry count; if it is
        # getting close to the budget but the lemma looks close, the guide can add
        # bounded minutes with EXTEND_MINUTES rather than being force-stopped.
        _idle_min = (_time.time() - getattr(entry, '_last_progress_time', loop_start)) / 60.0
        _idle_budget = LEMMA_IDLE_MINUTES + getattr(entry, '_idle_extension_minutes', 0.0)
        extend_prompt = ""
        if _idle_min > 0.5 * _idle_budget:
            stuck_hint += (
                f"\n⏳ IDLE BUDGET: {_idle_min:.0f}/{_idle_budget:.0f} min without a sorry "
                f"reduction. At {_idle_budget:.0f} min the flexible backstop fires. If you "
                f"judge this lemma is CLOSE, you may grant more time with EXTEND_MINUTES "
                f"(≤{MAX_GUIDE_EXTEND_MINUTES} per grant).\n"
            )
            extend_prompt = (
                f"\nEXTEND_MINUTES: <0-{MAX_GUIDE_EXTEND_MINUTES}> (extra idle minutes to "
                f"grant if you believe the lemma is close; 0 or omit for none)"
            )

        snapshot_prompt = ""
        if file_compiles:
            snapshot_prompt = (
                "\nSNAPSHOT: <yes|no> (does the CURRENT compiling state deserve to be "
                "banked as a safety net — real progress worth preserving? Judge this "
                "independently of the writer.)\n"
                "SNAPSHOT_TAG: <short label> (only if SNAPSHOT: yes)"
            )

        decision, reason, extras = await _consult_guide_decide(
            agent, state, ledger, entry, cwd,
            options=["continue", "decompose", "fresh_start", "give_up"],
            task=(
                f"{_runway_note(writer_pct)}\n"
                f"(Runway is a USAGE figure: a LOW % means the writer has LOTS of room "
                f"left — NOT that it is exhausted. Do NOT decompose while runway is HEALTHY.)\n"
                f"- continue: Keep trying in this file (the default while runway is HEALTHY).\n"
                f"- decompose: Split into helper files — ONLY when the writer is genuinely "
                f"stuck AND runway is GETTING FULL/FULL. Never split a mutually-recursive "
                f"goal into separate files (keep it in one `mutual` block).\n"
                f"- fresh_start: Current approach exhausted, start over.\n"
                f"- give_up: Statement is false."
                f"{stuck_hint}"
            ),
            post_prompt=(
                f"TURNS: <{MIN_CHUNK_TURNS}-{MAX_CHUNK_TURNS}> (how many turns for writer next, if continue)"
                f"{snapshot_prompt}"
                f"{extend_prompt}"
            ),
            post_prompt_parser=_parse_turns,
        )

        # Apply a guide-granted flexible-backstop extension (Fix B, Tier 1). Bounded
        # per grant; there is no total cap — the guide keeps ownership of the clock
        # while it judges the lemma close. The hard run-level ceiling (Tier 2) still
        # applies unconditionally.
        if extras.get("extend_minutes"):
            grant = min(MAX_GUIDE_EXTEND_MINUTES, max(0, int(extras["extend_minutes"])))
            if grant > 0:
                entry._idle_extension_minutes = (
                    getattr(entry, '_idle_extension_minutes', 0.0) + grant)
                await agent._emit("message",
                    f"[PO5] Guide extended idle budget by {grant}min "
                    f"(total extension {entry._idle_extension_minutes:.0f}min)")

        # Guide-driven snapshot: an independent strategic checkpoint, in addition
        # to any the writer took on its own. save_snapshot re-checks compilation
        # and dedups, so a redundant request is a harmless no-op.
        if extras.get("snapshot"):
            from .._snapshot_mcp import save_snapshot
            msg = save_snapshot(stub_rel, entry.workspace, cwd,
                                extras.get("snapshot_tag", "guide-checkpoint"),
                                note=f"guide checkpoint after chunk {entry.attempts}")
            await agent._emit("message", f"[PO5] Guide snapshot: {msg}")

        if decision == "give_up":
            await agent._emit("message", f"[PO5] Guide gives up: {reason}")
            ctx.failure_context = f"Guide gave up: {reason}"
            ledger.mark_failed(entry.id, f"Guide gave up: {reason}")
            _record_give_up(state, entry, f"Guide gave up: {reason}")
            await _ask_guide_user_fix(agent, state, ledger, entry, cwd, f"Guide gave up: {reason}")
            _propagate_failure_to_parent(state, ledger, entry, f"Child '{entry.name}' gave up: {reason}")
            return "failed"
        elif decision == "fresh_start":
            await agent._emit("message", f"[PO5] Fresh start: {reason}")
            ctx.needs_fresh_guide = True
            ctx.needs_fresh_writer = True
            ctx.failure_context = f"Previous approach exhausted: {reason}"
            ctx.current_task = ""
            return "retry"
        elif decision == "decompose":
            await agent._emit("message", f"[PO5] Decompose: {reason}")
            # Pre-extraction validation: ask guide which helpers are actually extractable
            decompose_ok = await _validate_decompose(
                agent, state, ledger, entry, cwd, tools, stub_rel, protected_names)
            if decompose_ok is True:
                break
            # Guide determined nothing is extractable — get revised strategy and continue
            await agent._emit("message", f"[PO5] Decompose blocked — proving inline")
            advice = await _consult_guide_raw(agent, state, ledger, entry, cwd,
                task=(
                    f"Extraction was BLOCKED because some helpers recurse back into the parent.\n"
                    f"Details: {decompose_ok}\n\n"
                    f"Give the writer a concrete strategy to prove the recursive helpers INLINE\n"
                    f"(with termination_by / fuel-based induction). Once those are closed,\n"
                    f"any remaining standalone helpers can be extracted in a later pass.\n"
                    f"Specify TURNS: <{MIN_CHUNK_TURNS}-{MAX_CHUNK_TURNS}>."
                ))
            turns_match = re.search(r'TURNS:\s*(\d+)', advice)
            chunk_budget = max(MIN_CHUNK_TURNS, min(MAX_CHUNK_TURNS, int(turns_match.group(1)))) if turns_match else CHUNK_TURNS
            continue
        else:
            if "turns" in extras:
                chunk_budget = max(MIN_CHUNK_TURNS, min(MAX_CHUNK_TURNS, extras["turns"]))

    # ── Max depth: no extraction ──
    if entry.depth >= MAX_DEPTH:
        return await _prove_at_max_depth(agent, state, ledger, entry, cwd,
                                          tools, stub_rel)

    # ── Grace phase: factor sorry into external helpers ──
    return await _grace_phase(agent, state, ledger, entry, cwd,
                               writer, verify_fn, tools, stub_rel, protected_names)


async def _validate_decompose(agent, state, ledger, entry, cwd, tools, stub_rel, protected_names):
    """Ask guide to verify which sorry helpers are truly extractable before committing.

    Returns True if decomposition should proceed, or a string with revised
    instructions for the writer if nothing is extractable.
    """
    split = tools.split_theorems(stub_rel)
    if not split or split.error:
        return True  # can't analyze, let extraction try

    # Sibling obligations sharing this file are NOT extractable helpers.
    siblings = _sibling_target_names(ledger, entry, cwd, stub_rel)
    sorry_helpers = [b for b in split.blocks
                     if b.has_sorry and b.name not in protected_names
                     and b.name not in siblings]
    if not sorry_helpers:
        return True  # nothing to check

    helper_list = "\n".join(
        f"  - {b.name} (lines {b.start}-{b.end})" for b in sorry_helpers)

    decision, reason, _extras = await _consult_guide_decide(
        agent, state, ledger, entry, cwd,
        options=["proceed_extract", "continue_inline"],
        task=(
            f"BEFORE EXTRACTING — verify each sorry helper is truly standalone.\n\n"
            f"Sorry helpers that would be extracted:\n{helper_list}\n\n"
            f"For EACH helper, answer: does its proof need to:\n"
            f"  - Recurse back into '{entry.name}' (tail re-entry on shorter trace)?\n"
            f"  - Use `ih` applied to the FULL statement (not just the body)?\n"
            f"  - Call any theorem in the same mutual block?\n\n"
            f"If YES for ANY helper → choose 'continue_inline' and explain what the\n"
            f"writer must prove inline (with termination_by) vs what can be extracted later.\n\n"
            f"If ALL helpers are genuinely standalone (no callbacks) → choose 'proceed_extract'."
        ))

    if decision == "proceed_extract":
        return True
    else:
        return (
            f"Guide reviewed helpers before extraction and determined they cannot be extracted:\n"
            f"{reason}\n"
            f"Prove the recursive/inline helpers first, then extract standalone ones."
        )



async def _prove_at_max_depth(agent, state, ledger, entry, cwd,
                               tools, stub_rel) -> str:
    """At max depth: fresh guide + proof_closer that know nothing about decomposition.
    Pure prove loop — guide advises, closer works, guide decides continue/give_up."""
    ctx = state.lemma_ctx[entry.id]
    await agent._emit("message", "[PO5] MAX DEPTH — spawning proof_closer (no decomposition).")

    # Kill existing guide+writer — they carry decomposition context we don't want
    await _cleanup_agents(agent, entry)

    # Spawn proof_closer (different agent spec — no sorry allowed)
    deep_writer = await _get_proof_closer(agent, entry, state, ledger)
    original_content = (cwd / stub_rel).read_text()
    verify_fn = _make_verifier(entry, stub_rel, original_content, ledger, cwd)

    # Fresh guide — initial task is pure "prove this, no decomposition exists"
    ledger_summary = _build_ledger_summary(ledger, entry)
    advice = await _consult_guide_raw(agent, state, ledger, entry, cwd,
        task=(
            f"You must prove '{entry.name}' in {stub_rel} with ZERO sorry.\n"
            f"There is NO decomposition available — everything must be proved in this one file.\n"
            f"You CAN create helper theorems within the same file.\n"
            f"Use mutual recursion, induction, structural recursion — any technique.\n\n"
            f"CONTEXT:\n{ledger_summary}\n\n"
            f"Read {_read_hint(state)}. Advise on the best approach."
        ))

    # Same loop pattern as _attempt_prove but only continue/fresh_start/give_up
    total_turns = 0
    prev_sorry_count = None
    chunk_budget = CHUNK_TURNS

    while True:
        chunk = min(MAX_CHUNK_TURNS, max(MIN_CHUNK_TURNS, chunk_budget))
        await agent._emit("message", f"[PO5] Deep chunk ({chunk}t, total={total_turns})")

        await verified_loop(
            agent_ctx=deep_writer,
            initial_input=(
                f"STRATEGY ADVICE from your proof guide:\n{advice}\n\n"
                f"You have {chunk} turns. Close ALL sorry. File MUST compile."
            ),
            verify=verify_fn, max_rounds=5, max_turns=chunk, use_run_ai=True,
        )
        total_turns += chunk

        # Check: proved? Uses the authoritative transitive oracle (#print axioms),
        # not the text/warning-based cr.has_sorry which misses sorry reached
        # through imported/assembled dependencies. _proved_or_contingent also
        # parks the entry as CONTINGENT when it is locally clean but still waiting
        # on an unproven SIBLING obligation (not just a child), matching the
        # per-target gate — otherwise a finished target gets needlessly re-driven.
        _compiles_now = tools.check_compiles(stub_rel).success
        if _compiles_now:
            verdict = _proved_or_contingent(tools, ledger, entry, cwd, stub_rel)
            if verdict is not None:
                return verdict
            # None: transitive sorry from untracked imports / fresh inline
            # helper — continue proving.

        # Gather state
        sorry_info = tools.get_sorries_by_theorem(stub_rel)
        sorry_count = sum(len(v) for v in sorry_info.values())
        progress = _format_progress(prev_sorry_count, sorry_count, compiles=_compiles_now)
        prev_sorry_count = sorry_count
        writer_pct = await deep_writer.get_context_percentage()

        # Guide reviews → next advice
        await agent._emit("message", f"[PO5] Deep guide reviews: {progress}")
        advice = await _consult_guide_raw(agent, state, ledger, entry, cwd,
            task=(
                f"Writer completed chunk ({total_turns} total turns).\n"
                f"{_runway_note(writer_pct)}\n"
                f"{progress}\nFile: {stub_rel}\nSorries: {sorry_info}\n"
                f"Remember: NO decomposition. Everything in one file.\n"
                f"Diagnose and advise what to try next."
            ))

        # Guide decides — only continue/fresh_start/give_up (NO decompose)
        def _parse_turns_deep(raw: str) -> dict:
            m = re.search(r'TURNS:\s*(\d+)', raw)
            return {"turns": int(m.group(1))} if m else {}

        decision, reason, extras = await _consult_guide_decide(
            agent, state, ledger, entry, cwd,
            options=["continue", "fresh_start", "give_up"],
            task=(
                f"{_runway_note(writer_pct)}\n"
                f"(Runway is a USAGE figure: a LOW % means the writer has LOTS of room "
                f"left — NOT that it is exhausted. Prefer continue while runway is HEALTHY.)\n"
                f"- continue: Keep trying.\n"
                f"- fresh_start: Current approach exhausted, try new strategy.\n"
                f"- give_up: Cannot be proved."
            ),
            post_prompt=f"TURNS: <{MIN_CHUNK_TURNS}-{MAX_CHUNK_TURNS}> (how many turns for writer next, if continue)",
            post_prompt_parser=_parse_turns_deep,
        )

        if decision == "give_up":
            await agent._emit("message", f"[PO5] Deep guide gives up: {reason}")
            ctx.failure_context = f"Max depth, gave up: {reason}"
            ledger.mark_failed(entry.id, f"Max depth, gave up: {reason}")
            _record_give_up(state, entry, f"Max depth, gave up: {reason}")
            await _ask_guide_user_fix(agent, state, ledger, entry, cwd, f"Max depth, gave up: {reason}")
            _propagate_failure_to_parent(state, ledger, entry, f"Child '{entry.name}' failed at max depth: {reason}")
            return "failed"
        elif decision == "fresh_start":
            await agent._emit("message", f"[PO5] Deep fresh start: {reason}")
            ctx.needs_fresh_guide = True
            ctx.failure_context = f"Max depth, fresh start: {reason}"
            return "retry"
        else:
            if "turns" in extras:
                chunk_budget = max(MIN_CHUNK_TURNS, min(MAX_CHUNK_TURNS, extras["turns"]))



async def _grace_phase(agent, state, ledger, entry, cwd,
                        writer, verify_fn, tools, stub_rel, protected_names) -> str:
    """Decompose-time wrap-up: factor the protected block's remaining sorry into
    NAMED helpers so the extraction pipeline can move them out.

    This is NOT a "close ALL sorry" grind — the writer is not asked to finish the
    hard sub-lemmas here, only to (a) prove what it easily can and (b) push each
    remaining hard goal into a named helper theorem declared above, closing the
    protected block with `exact helper ...`. The helpers keep their `sorry` and
    become child obligations after extraction. No writer↔guide back-and-forth.
    """
    sorry_info = tools.get_sorries_by_theorem(stub_rel)
    protected_sorry = sum(len(sorry_info.get(n, [])) for n in protected_names)

    if protected_sorry == 0:
        await agent._emit("message", "[PO5] Protected block sorry-free → extract")
        return "has_sorry"

    is_mutual = len(protected_names) > 1
    mutual_note = ""
    if is_mutual:
        mutual_note = (
            f"\nMUTUAL BLOCK RULE: {sorted(protected_names)} must ALL be sorry-free.\n"
            f"Helpers go OUTSIDE and ABOVE the mutual...end block.\n"
        )

    await agent._emit("message", f"[PO5] Grace (factor & wrap up): {protected_sorry} sorry in protected block")

    # Bounded — this is a wrap-up, not a solve. A couple of passes is enough to
    # lift the remaining goals into named helpers; if it stalls we stop and let
    # extraction take whatever is factored.
    prev_count = protected_sorry
    for grace in range(2):
        sorry_info = tools.get_sorries_by_theorem(stub_rel)
        positions = {n: sorry_info.get(n, []) for n in protected_names if sorry_info.get(n)}

        await verified_loop(
            agent_ctx=writer,
            initial_input=(
                f"WRAP UP for extraction — grace {grace+1}.\n"
                f"Sorry still in the protected block: {positions}\n\n"
                f"GOAL: make the protected block ({sorted(protected_names)}) sorry-free by "
                f"FACTORING, not by finishing every hard proof now. For each remaining sorry:\n"
                f"  1. If you can close it quickly, do so.\n"
                f"  2. Otherwise, declare a NEW named helper theorem ABOVE it (with its own "
                f"`sorry`) capturing exactly that obligation, and close the goal with "
                f"`exact helper ...` / `apply helper ...`.\n"
                f"The helpers keep their `sorry` — the extraction pipeline moves them into "
                f"their own files and they become separate obligations. You cannot create "
                f"files yourself; declare helpers IN THIS SAME FILE.\n"
                f"The protected block itself must end up sorry-free (all its sorry pushed "
                f"into named helpers)."
                f"{mutual_note}\nYou have {GRACE_TURNS} turns."
            ),
            verify=verify_fn, max_rounds=2, max_turns=GRACE_TURNS, use_run_ai=True,
        )

        if tools.check_compiles(stub_rel).success:
            # Same proved/contingent/fall-through decision as the per-target gate:
            # PROVED (transitively sorry-free), CONTINGENT (locally clean but
            # waiting on an unproven sibling/child), or None (fall through to keep
            # factoring out helpers in the grace phase).
            verdict = _proved_or_contingent(tools, ledger, entry, cwd, stub_rel)
            if verdict is not None:
                return verdict

        sorry_info = tools.get_sorries_by_theorem(stub_rel)
        cur = sum(len(sorry_info.get(n, [])) for n in protected_names)
        if cur == 0:
            await agent._emit("message", "[PO5] Protected block sorry-free → extract")
            return "has_sorry"
        if cur >= prev_count:
            break
        prev_count = cur

    if tools.check_compiles(stub_rel).success:
        split = tools.split_theorems(stub_rel)
        extractable = [b for b in split.blocks
                       if b.name not in protected_names and b.mutual_group is None]
        if extractable:
            return "has_sorry"

    ctx = state.lemma_ctx.get(entry.id, LemmaContext())
    ctx.failure_context = "Could not make the protected block sorry-free despite multiple attempts"
    ledger.mark_failed(entry.id, "Protected block still has sorry after grace phase")
    _propagate_failure_to_parent(state, ledger, entry,
        f"Child '{entry.name}' failed: could not eliminate sorry from the main proof body")
    return "failed"


# ═══════════════════════════════════════════════════════════════════════════════
# Phase: EXTRACT
# ═══════════════════════════════════════════════════════════════════════════════

async def _phase_extract(agent, state: PO5State, ledger: LemmaLedger, cwd: Path) -> Trans:
    """Extract helpers into files. Guide reviews before committing."""
    entry = ledger.get(state.current_lemma_id)
    ctx = state.lemma_ctx.get(entry.id, LemmaContext())
    tools = get_lean_tools()
    stub_rel = _resolve_stub(entry, cwd, state)

    # Save predecomp snapshot
    shutil.copy2(cwd / stub_rel, cwd / entry.workspace / "Stub.predecomp.lean")

    # Worker: decl_extractor
    new_decomp_dir = cwd / entry.workspace / "new_decomposition"
    if new_decomp_dir.exists():
        shutil.rmtree(new_decomp_dir)

    split = tools.split_theorems(stub_rel)
    protected_names = _get_protected_names(tools, stub_rel, entry)
    # Sibling obligations sharing this file must not be extracted as helpers.
    siblings = _sibling_target_names(ledger, entry, cwd, stub_rel)
    extractable = [b for b in split.blocks
                   if b.name not in protected_names and b.mutual_group is None
                   and b.name not in siblings]

    # Fix A: nothing to extract. A forced decompose (e.g. from the backstop) can land
    # here when every declaration is a protected/sibling obligation. Spawning an
    # extractor is pointless — it can only no-op or, worse, move protected siblings
    # (the IMO2026 corruption). Skip the extractor entirely and let the guide decide
    # (retry with a different tack, or give up) instead of spinning.
    if not extractable:
        await agent._emit("message",
            f"[PO5] Nothing extractable from {stub_rel} "
            f"(all {len(split.blocks)} decls protected/sibling) — skipping extractor")
        decision, reason, _extras = await _consult_guide_decide(
            agent, state, ledger, entry, cwd,
            options=["retry", "give_up"],
            task=(
                f"Cannot decompose: every declaration in {stub_rel} is a protected "
                f"target or sibling obligation ({sorted(protected_names | siblings)}), "
                f"so there is nothing to extract into a helper.\n"
                f"The remaining difficulty is in the protected block(s) themselves or "
                f"in already-extracted children.\n"
                f"Options: retry proving inline (different tactic/approach), or give up."
            ))
        if decision == "give_up":
            ctx.failure_context = f"Nothing extractable, gave up: {reason}"
            ledger.mark_failed(entry.id, f"Nothing extractable, gave up: {reason}")
            _record_give_up(state, entry, f"Nothing extractable, gave up: {reason}")
            await _ask_guide_user_fix(agent, state, ledger, entry, cwd,
                                      f"Nothing extractable, gave up: {reason}")
            _propagate_failure_to_parent(state, ledger, entry,
                                         f"Child '{entry.name}' cannot be decomposed: {reason}")
            return Trans.CONTRADICTORY
        ctx.failure_context = "Nothing extractable — must prove inline."
        ctx.current_task = (
            f"Decomposition is not possible (all declarations are protected/sibling "
            f"obligations). Guide decided: {reason}\n"
            f"Prove the remaining sorry inline.")
        return Trans.RETRY

    session = MoveSession(tools, stub_rel, entry.name, entry.workspace,
                          output_subdir="new_decomposition",
                          protected_names=(protected_names | siblings))
    # Proof-DAG ancestors (dotted workspace paths) so add_import_safely can refuse
    # cycle-forming imports — same source as the writer's import server.
    ancestor_modules = []
    for anc_id in ledger.get_ancestry(entry.id):
        anc = ledger.get(anc_id)
        if anc:
            ancestor_modules.append(anc.workspace.replace("/", "."))
    extractor_mcp = create_extractor_mcp_server(session, ancestor_modules=ancestor_modules)

    do_not_move_names = sorted(protected_names | siblings)
    do_not_move = ""
    if len(do_not_move_names) > 1:
        do_not_move = f"\nDo NOT move: {do_not_move_names} (protected/sibling obligations).\n"

    await agent._emit("message", f"[PO5] Extracting {len(extractable)} helpers from {stub_rel}")

    async with swarm_agent("decl_extractor", swarm=agent.swarm, cwd=agent._cwd,
                           workspace=entry.workspace,
                           extra_mcp_servers={"extractor_tools": extractor_mcp}) as extractor:
        outcome = await verified_loop(
            agent_ctx=extractor,
            initial_input=(
                f"Extract standalone helpers from {stub_rel} into separate files.\n"
                f"Main theorem: '{entry.name}' (do NOT move this).{do_not_move}\n"
                f"Call get_declarations, then move_decl for each, then commit."
            ),
            verify=lambda: _verify_extraction(tools, stub_rel, entry, new_decomp_dir),
            max_rounds=2, max_turns=50, use_run_ai=False,
        )

    if not outcome.success:
        extract_error = outcome.last_error or "unknown error"
        session.revert()
        decision, reason, _extras = await _consult_guide_decide(
            agent, state, ledger, entry, cwd,
            options=["retry", "give_up"],
            task=(
                f"Extraction FAILED. The extractor could not produce compilable output.\n"
                f"Error: {extract_error}\n"
                f"The file has been reverted to pre-extraction state.\n"
                f"Options: retry proving (different factoring), or give up."
            ))
        if decision == "give_up":
            ctx.failure_context = f"Extraction failed ({extract_error}), gave up: {reason}"
            ledger.mark_failed(entry.id, f"Extraction failed, gave up: {reason}")
            _record_give_up(state, entry, f"Extraction failed ({extract_error}), gave up: {reason}")
            await _ask_guide_user_fix(agent, state, ledger, entry, cwd,
                                      f"Extraction failed ({extract_error}), gave up: {reason}")
            _propagate_failure_to_parent(state, ledger, entry, f"Child '{entry.name}' extraction failed: {reason}")
            return Trans.CONTRADICTORY
        ctx.failure_context = f"Extraction failed: {extract_error}"
        ctx.current_task = (
            f"Extraction failed: {extract_error}\n"
            f"Guide decided: {reason}\n"
            f"Restructure the file so helpers can be extracted, or prove inline."
        )
        return Trans.RETRY

    finalize_result = session.finalize()
    if finalize_result and "Error" in finalize_result:
        await agent._emit("message", f"[PO5] finalize warning: {finalize_result}")
    new_files = sorted(new_decomp_dir.glob("lemma_helper_*.lean")) if new_decomp_dir.exists() else []
    await agent._emit("message", f"[PO5] Extraction done: {len(new_files)} files staged")

    # Post-extraction compilation check — catch any issues the extractor missed
    if new_files:
        import subprocess
        stub_module = stub_rel.replace("/", ".").removesuffix(".lean")
        build_result = subprocess.run(["lake", "build", stub_module],
                                       cwd=str(cwd), capture_output=True, text=True, timeout=300)
        build_errors = [l for l in (build_result.stdout + "\n" + build_result.stderr).splitlines()
                        if ": error:" in l]
        if build_errors:
            error_summary = "\n".join(build_errors[:5])
            session.revert()
            ctx.failure_context = f"Post-extraction build failed:\n{error_summary}"
            ctx.current_task = "Extraction produced files but they don't compile together. The guide should review the errors and advise the writer how to restructure."
            await agent._emit("message", f"[PO5] Post-extraction build FAILED — reverting")
            return Trans.RETRY

    if not new_files:
        # Extractor ran but produced nothing — diagnose why
        tools_check = get_lean_tools()
        split = tools_check.split_theorems(stub_rel)
        blocked_reasons = []
        if split and not split.error:
            for b in split.blocks:
                if b.name == entry.name:
                    continue
                if not b.has_sorry:
                    continue
                if b.mutual_group is not None:
                    group_names = split.mutual_groups.get(b.mutual_group, [])
                    if entry.name in group_names:
                        blocked_reasons.append(f"'{b.name}' — in mutual block with main theorem")
                    else:
                        blocked_reasons.append(f"'{b.name}' — in mutual group {group_names}")
                elif "private " in b.text[:50]:
                    blocked_reasons.append(f"'{b.name}' — private (cannot be imported)")

        # Include extractor's last output if available (may explain why commit failed)
        extractor_msg = ""
        if outcome and outcome.output:
            extractor_msg = f"\nExtractor reported: {str(outcome.output)[:300]}"

        blocked_str = "\n".join(f"  - {r}" for r in blocked_reasons) if blocked_reasons else f"no structural blockers detected{extractor_msg}"
        ctx.failure_context = (
            f"Extraction produced 0 files. Blocked helpers:\n{blocked_str}"
        )
        ctx.current_task = (
            f"Extraction produced 0 files despite the extractor reporting success.\n"
            f"Diagnosis: {blocked_str}\n"
            f"If helpers are in a mutual block with main, move them out as standalone theorems above.\n"
            f"If private, remove 'private'. Otherwise prove inline."
        )
        await agent._emit("message", f"[PO5] 0 files extracted — blocked: {blocked_str[:100]}")
        return Trans.RETRY

    # Guide reviews decomposition
    file_list = "\n".join(f"  - {f.stem}" for f in new_files)
    decision, reason, _extras = await _consult_guide_decide(
        agent, state, ledger, entry, cwd,
        options=["proceed", "revert"],
        task=(
            f"Extracted {len(new_files)} helpers:\n{file_list}\n\n"
            f"Review each helper: does its proof need to call a theorem defined in the\n"
            f"current mutual block (i.e., call back into the parent)? If yes → revert.\n\n"
            f"If reverting: explain WHICH helpers must stay in the mutual block, HOW the\n"
            f"proof writer should reorganize them (e.g., add them into the mutual...end with\n"
            f"shared termination_by), and what existing helpers should be altered or removed\n"
            f"to accommodate the change. Be specific — the writer will use your instructions."
        ))

    if decision == "revert":
        _revert_extraction(entry, cwd)
        ctx.current_task = f"Guide reverted extraction: {reason}. Prove inline."
        ctx.failure_context = f"Decomposition invalid: {reason}"
        await agent._emit("message", f"[PO5] Guide reverted: {reason}")
        return Trans.RETRY

    return Trans.EXTRACTED


# ═══════════════════════════════════════════════════════════════════════════════
# Phase: DETECT
# ═══════════════════════════════════════════════════════════════════════════════

async def _phase_detect(agent, state: PO5State, ledger: LemmaLedger, cwd: Path) -> Trans:
    """Cycle detection. Guide decides on issues."""
    entry = ledger.get(state.current_lemma_id)
    ctx = state.lemma_ctx.get(entry.id, LemmaContext())

    result, verdicts = await _run_detection(agent, state, ledger, entry, cwd)

    if result == "rejected":
        _revert_extraction(entry, cwd)
        ctx.failure_context = "Decomposition rejected: identical to previously failed attempt."
        ctx.current_task = "Try a completely different decomposition."
        await agent._emit("message", "[PO5] Rejected — guide will retry.")
        return Trans.RETRY

    if result == "cycle_found":
        cycle_info = [v for v in verdicts if v.match_type == "cycle"]
        cycle_desc = "\n".join(f"  - {v.name} needs {v.matched_name} (ancestor)" for v in cycle_info)

        decision, reason, _extras = await _consult_guide_decide(
            agent, state, ledger, entry, cwd,
            options=["expand_mutual", "different_decomposition", "fresh_start", "give_up"],
            task=(
                f"CYCLE DETECTED:\n{cycle_desc}\n\n"
                f"- expand_mutual: Add into mutual block with shared termination_by\n"
                f"- different_decomposition: Revert, try different factoring\n"
                f"- fresh_start: New guide from scratch\n"
                f"- give_up: Cannot be proved"
            ))

        _revert_extraction(entry, cwd)
        state.cycles_detected += 1

        if decision == "give_up":
            ctx.failure_context = f"Cycle, gave up: {reason}"
            ledger.mark_failed(entry.id, f"Cycle, gave up: {reason}")
            _record_give_up(state, entry, f"Cycle, gave up: {reason}")
            await _ask_guide_user_fix(agent, state, ledger, entry, cwd, f"Cycle, gave up: {reason}")
            _propagate_failure_to_parent(state, ledger, entry, f"Child '{entry.name}' has unresolvable cycle: {reason}")
            return Trans.CONTRADICTORY
        elif decision == "expand_mutual":
            ctx.current_task = (
                "The extracted helpers have mutual recursion with the parent block. "
                "Add them INTO the mutual...end with shared termination_by. "
                "Do NOT create external sorry stubs.")
            ctx.failure_context = f"CYCLE: {cycle_desc}"
            await agent._emit("message", f"[PO5] Expand mutual: {reason}")
            return Trans.RETRY
        elif decision == "fresh_start":
            ctx.needs_fresh_guide = True
            ctx.needs_fresh_writer = True
            ctx.failure_context = f"Cycle, fresh start: {cycle_desc}"
            return Trans.RETRY
        else:
            ctx.current_task = "Try completely different decomposition."
            ctx.failure_context = f"Cycle: {cycle_desc}"
            return Trans.RETRY

    # Check duplicates
    existing_names = {e.name for e in ledger.entries()}
    duplicates = [v for v in verdicts if v.name in existing_names]
    if duplicates:
        dup_names = [v.name for v in duplicates]
        decision, reason, _extras = await _consult_guide_decide(
            agent, state, ledger, entry, cwd,
            options=["revert", "proceed"],
            task=f"Duplicate names: {dup_names}. Revert and import existing, or proceed?")
        if decision == "revert":
            _revert_extraction(entry, cwd)
            ctx.failure_context = f"Duplicates: {dup_names}. Use imports."
            return Trans.RETRY

    # All clean — register
    _register_all_helpers(state, ledger, entry, cwd)
    state._detect_verdicts = verdicts
    return Trans.NO_CYCLE


# ═══════════════════════════════════════════════════════════════════════════════
# Phase: UPDATE
# ═══════════════════════════════════════════════════════════════════════════════

async def _phase_update(agent, state: PO5State, ledger: LemmaLedger, cwd: Path) -> Trans:
    """Apply verdicts to ledger. Mechanical — no guide needed."""
    entry = ledger.get(state.current_lemma_id)
    _apply_verdicts(state, ledger, entry, cwd)
    _resolve_import_dependencies(ledger, cwd)

    from .cycle_detection import prune_siblings_of_dead
    prune_siblings_of_dead(ledger, cwd)
    _propagate_proved(ledger, cwd)

    return Trans.CHECKED


# ═══════════════════════════════════════════════════════════════════════════════
# Phase: CHECK
# ═══════════════════════════════════════════════════════════════════════════════

async def _phase_check(agent, state: PO5State, ledger: LemmaLedger, cwd: Path) -> Trans:
    """Status inspection. On stuck: consult root's guide."""
    root = ledger.get(state.root_id)
    if root and root.status == LemmaStatus.PROVED:
        return Trans.ALL_PROVED
    if root and root.status == LemmaStatus.FAILED:
        return Trans.BLOCKED
    if ledger.all_proved():
        return Trans.ALL_PROVED
    if ledger.has_pending():
        return Trans.HAS_PENDING

    # Stuck
    stuck = [e for e in ledger.entries()
             if e.status in (LemmaStatus.CONTINGENT, LemmaStatus.PROVING)]
    stuck_desc = "\n".join(f"  - {e.name} [{e.status}]" for e in stuck)

    root_entry = ledger.get(state.root_id)
    if root_entry:
        decision, reason, _extras = await _consult_guide_decide(
            agent, state, ledger, root_entry, cwd,
            options=["unblock", "give_up"],
            task=f"STUCK: No pending work.\nStuck:\n{stuck_desc}\nCan we unblock or give up?")
        if decision == "unblock":
            for e in stuck:
                if e.status == LemmaStatus.CONTINGENT:
                    e.status = LemmaStatus.PENDING
                    ctx = state.lemma_ctx.get(e.id)
                    if ctx:
                        ctx.current_task = f"Re-attempting: {reason}"
                    ledger.save()
                    await agent._emit("message", f"[PO5] Unblocked: {e.name}")
                    break
            return Trans.HAS_PENDING
        else:
            ledger.mark_failed(state.root_id, f"Stuck, gave up: {reason}")
            _record_give_up(state, root_entry, f"Stuck, gave up: {reason}")
            # Root give-up: ask the guide whether the user must fix something.
            await _ask_guide_user_fix(agent, state, ledger, root_entry, cwd,
                                      f"Stuck, gave up: {reason}")

    return Trans.BLOCKED


# ═══════════════════════════════════════════════════════════════════════════════
# Phase: ASSEMBLE
# ═══════════════════════════════════════════════════════════════════════════════

async def _phase_assemble(agent, state: PO5State, ledger: LemmaLedger, cwd: Path) -> Trans:
    """Assembly: copy proved files, build, guide + fixer on errors."""
    import subprocess
    tools = get_lean_tools()
    root_entry = ledger.get(state.root_id)

    # Copy proved Stub.lean → .lean
    topo = _topo_sort(ledger)
    for eid in topo:
        e = ledger.get(eid)
        if not e or e.status != LemmaStatus.PROVED:
            continue
        stub = cwd / e.workspace / "Stub.lean"
        target = cwd / f"{e.workspace}.lean"
        if stub.exists() and target.exists():
            shutil.copy2(stub, target)

    # Build + fix loop (guide + fixer pairs)
    root_module = f"{state.root_workspace}.Stub".replace("/", ".")
    for attempt in range(3):
        result = subprocess.run(
            ["lake", "build", root_module], cwd=str(cwd),
            capture_output=True, text=True, timeout=180,
        )
        errors = [l for l in (result.stdout + "\n" + result.stderr).splitlines()
                  if ": error:" in l]
        if not errors:
            break

        error_text = "\n".join(errors[:20])
        await agent._emit("message", f"[PO5] Build errors (attempt {attempt+1}/3)")

        # Guide reviews
        advice = await _consult_guide_raw(agent, state, ledger, root_entry, cwd,
            task=f"Assembly build failed:\n{error_text}\nDiagnose and advise the fixer.")

        # Fixer works
        fixed = await _run_fixer(agent, state, cwd, error_text, advice)
        if not fixed:
            decision, reason, _extras = await _consult_guide_decide(
                agent, state, ledger, root_entry, cwd,
                options=["retry", "give_up"],
                task=f"Fixer failed (attempt {attempt+1}/3). Retry or give up?")
            if decision == "give_up":
                _record_give_up(state, root_entry, f"Assembly build failed, gave up: {reason}")
                await _ask_guide_user_fix(agent, state, ledger, root_entry, cwd,
                                          f"Assembly build failed, gave up: {reason}")
                return Trans.ASSEMBLY_FAILED
    else:
        return Trans.ASSEMBLY_FAILED

    # Verify the requested proof obligations are sorry-free. This must use the
    # SAME authoritative transitive oracle as the per-target gate
    # (`axioms_by_theorem` / `#print axioms`), not just the text/warning-based
    # `cr.has_sorry`: a theorem can be textually clean yet still bottom out in a
    # `sorryAx` through an assembled dependency.
    #
    # SCOPE: only the obligations the TM asked us to prove — i.e. the ones
    # registered in the ledger (INIT narrows these to the requested subset via
    # `_filter_requested_targets`). Un-requested sibling theorems in the same
    # file may legitimately still carry `sorry`; they are NOT our task, so we
    # must not gate assembly on them (neither the whole-file `has_sorry` nor the
    # transitive check).
    root_stub = f"{state.root_workspace}/Stub.lean"
    cr = tools.check_compiles(root_stub)
    if not cr.success:
        await agent._emit("message", "[PO5] Assembly: root does not compile")
        return Trans.ASSEMBLY_FAILED

    obligation_names = _requested_obligation_names(ledger, state, root_stub)

    if obligation_names:
        # Literal-sorry check scoped to our obligations (not the whole file).
        local_sorry = tools.get_sorries_by_theorem(root_stub)
        with_sorry = [n for n in obligation_names if local_sorry.get(n)]
        if with_sorry:
            await agent._emit("message",
                f"[PO5] Assembly: requested obligations still have literal sorry: {with_sorry}")
            return Trans.ASSEMBLY_FAILED
        # Transitive check: none of our obligations may depend on sorryAx.
        ax = tools.axioms_by_theorem(root_stub, obligation_names)
        unproven = [n for n in obligation_names if not ax.is_proven(n)]
        if unproven:
            await agent._emit("message",
                f"[PO5] Assembly: requested obligations transitively depend on sorry: {unproven}")
            return Trans.ASSEMBLY_FAILED
    elif cr.has_sorry:
        # No registered obligation names to scope to (single-root fallback):
        # keep the whole-file guard.
        await agent._emit("message", "[PO5] Assembly: root still has sorry")
        return Trans.ASSEMBLY_FAILED

    ledger.mark_proved(state.root_id, root_stub.replace("/", ".").removesuffix(".lean"))
    await agent._emit("message", "[PO5] Assembly complete: requested obligations sorry-free (transitively verified) ✅")

    return Trans.ASSEMBLED


# ═══════════════════════════════════════════════════════════════════════════════
# Helpers — agent management
# ═══════════════════════════════════════════════════════════════════════════════

async def _get_guide(agent, entry: LemmaEntry, state: PO5State, ledger: LemmaLedger) -> SwarmAgent:
    """Get or create persistent guide. Rotates automatically at 75% context or when needs_fresh_guide is set."""
    from .._ledger_mcp import create_ledger_mcp_server
    attr = f"_guide_{entry.id}"
    cwd = Path(agent._cwd) if agent._cwd else Path.cwd()
    ctx = state.lemma_ctx.get(entry.id)

    # Check if existing guide needs rotation (context exhausted or fresh_start requested)
    existing = getattr(agent, attr, None)
    if existing is not None:
        force_rotate = ctx and ctx.needs_fresh_guide
        try:
            pct = await existing.get_context_percentage()
        except Exception:
            pct = None
        # Rotate if: fresh_start requested, context exhausted, or process died
        if force_rotate or pct is None or pct >= CONTEXT_ROTATION_THRESHOLD:
            await _rotate_agent(agent, entry, cwd, role="guide", instance=existing)
            if ctx:
                ctx.needs_fresh_guide = False
            # Fall through to create fresh

    if getattr(agent, attr, None) is None:
        cheat_file = cheat_sheet_name(state.use_cheat_sheet, state.cheat_sheet_path)
        cheat_rel = f"{entry.workspace}/{cheat_file}" if cheat_file else ""
        ledger_mcp = create_ledger_mcp_server(ledger)
        from .._snapshot_mcp import create_snapshot_server
        stub_rel = f"{entry.workspace}/Stub.lean" if "/Stub.lean" not in entry.file_path else entry.file_path
        snapshot_mcp = create_snapshot_server(stub_rel, entry.workspace, cwd, can_write=False)
        ctx = swarm_agent(
            "proof_guide", swarm=agent.swarm, cwd=agent._cwd,
            workspace=entry.workspace,
            template_vars={"cheat_sheet_path": cheat_rel},
            can_see=["SearchAgent"],
            extra_mcp_servers={"ledger": ledger_mcp, "snapshots": snapshot_mcp},
            disable_compaction=True,
        )
        internal = await ctx.__aenter__()
        setattr(agent, f"{attr}_ctx", ctx)
        setattr(agent, attr, internal)
        state.agent_registry[entry.id] = state.agent_registry.get(entry.id, {})
        state.agent_registry[entry.id]["guide"] = internal.spec.name

        # Inject prior state if exists — enough turns to read cheat sheet + file
        state_path = cwd / entry.workspace / "guide_state" / f"{entry.name}.md"
        _read_cheat = (f"1. Read the cheat sheet ({cheat_file} in your workspace)\n"
                       if cheat_file else "")
        init_prompt = (
            "You are starting a new session. Before receiving any task:\n"
            f"{_read_cheat}"
            "2. Read the current Stub.lean to see the proof state\n"
            "3. Use any tools you need to understand the current situation\n"
        )
        if state_path.exists():
            prior = state_path.read_text()
            init_prompt += f"\nPRIOR SESSION STATE:\n\n{prior}\n"
        init_prompt += "\nOnce you have full context, acknowledge. Do NOT start proving yet."
        await internal.run_ai(inp=init_prompt, max_turns=15)

    return getattr(agent, attr)


async def _get_writer(agent, entry: LemmaEntry, state: PO5State, ledger: LemmaLedger):
    """Get or create persistent writer. Rotates automatically at 75% context
    or when needs_fresh_writer is set (e.g. after a fresh_start)."""
    from .._lean_tools_mcp import create_writer_import_server
    attr = f"_writer_{entry.id}"
    cwd = Path(agent._cwd) if agent._cwd else Path.cwd()
    ctx = state.lemma_ctx.get(entry.id)

    # Check if existing writer needs rotation
    existing = getattr(agent, attr, None)
    if existing is not None:
        force_rotate = ctx and ctx.needs_fresh_writer
        try:
            pct = await existing.get_context_percentage()
        except Exception:
            pct = None
        # Rotate if: fresh_start requested, context exhausted, or process died
        if force_rotate or pct is None or pct >= CONTEXT_ROTATION_THRESHOLD:
            await _rotate_agent(agent, entry, cwd, role="writer", instance=existing)
            if ctx:
                ctx.needs_fresh_writer = False
            # Fall through to create fresh

    if getattr(agent, attr, None) is None:
        ancestor_modules = []
        for anc_id in ledger.get_ancestry(entry.id):
            anc = ledger.get(anc_id)
            if anc:
                ancestor_modules.append(anc.workspace.replace("/", "."))
        stub_rel = f"{entry.workspace}/Stub.lean" if "/Stub.lean" not in entry.file_path else entry.file_path
        import_mcp = create_writer_import_server(stub_rel, ancestor_modules, ledger, current_entry_id=entry.id)
        from .._snapshot_mcp import create_snapshot_server
        from .hooks import snapshot_tip_hooks
        snapshot_mcp = create_snapshot_server(stub_rel, entry.workspace, cwd, can_write=True)
        ctx = swarm_agent(
            "proof_writer_v2", swarm=agent.swarm, cwd=agent._cwd,
            workspace=entry.workspace,
            can_see=["SearchAgent"],
            extra_mcp_servers={"writer_imports": import_mcp, "snapshots": snapshot_mcp},
            extra_hooks=snapshot_tip_hooks(agent_ref=agent, probability=1.0),
        )
        internal = await ctx.__aenter__()
        setattr(agent, f"{attr}_ctx", ctx)
        setattr(agent, attr, internal)
        state.agent_registry[entry.id] = state.agent_registry.get(entry.id, {})
        state.agent_registry[entry.id]["writer"] = internal.spec.name
        _remove_guide_from_visibility(agent, entry, internal)

        # Inject prior state if exists — enough turns to read file + orient
        state_path = cwd / entry.workspace / "guide_state" / f"writer_{entry.name}.md"
        init_prompt = (
            "You are starting a new session. Before receiving any task:\n"
            "1. Read your assigned Stub.lean file to see the current proof state\n"
            "2. Check sorry positions and goal state at those positions\n"
            "3. Use any tools you need to understand the context\n"
        )
        if state_path.exists():
            prior = state_path.read_text()
            init_prompt += f"\nPRIOR SESSION STATE:\n\n{prior}\n"
        init_prompt += "\nOnce oriented, acknowledge. Then wait for strategy advice."
        await internal.run_ai(inp=init_prompt, max_turns=15)

    return getattr(agent, attr)


async def _get_proof_closer(agent, entry: LemmaEntry, state: PO5State, ledger: LemmaLedger):
    """Get or create proof_closer for this lemma. Used at max depth — no sorry allowed."""
    from .._lean_tools_mcp import create_writer_import_server
    attr = f"_closer_{entry.id}"
    if getattr(agent, attr, None) is None:
        ancestor_modules = []
        for anc_id in ledger.get_ancestry(entry.id):
            anc = ledger.get(anc_id)
            if anc:
                ancestor_modules.append(anc.workspace.replace("/", "."))
        stub_rel = f"{entry.workspace}/Stub.lean" if "/Stub.lean" not in entry.file_path else entry.file_path
        import_mcp = create_writer_import_server(stub_rel, ancestor_modules, ledger, current_entry_id=entry.id)
        ctx = swarm_agent(
            "proof_closer", swarm=agent.swarm, cwd=agent._cwd,
            workspace=entry.workspace,
            can_see=["SearchAgent"],
            extra_mcp_servers={"writer_imports": import_mcp},
        )
        internal = await ctx.__aenter__()
        setattr(agent, f"{attr}_ctx", ctx)
        setattr(agent, attr, internal)
        state.agent_registry[entry.id] = state.agent_registry.get(entry.id, {})
        state.agent_registry[entry.id]["closer"] = internal.spec.name
        _remove_guide_from_visibility(agent, entry, internal)
    return getattr(agent, attr)


def _remove_guide_from_visibility(agent, entry: LemmaEntry, writer_agent):
    """Remove any guide agent from the writer's visibility set."""
    writer_name = writer_agent.spec.name
    registry = agent.swarm._registry
    visible = registry.visibility_graph.get(writer_name)
    if visible is None:
        return
    guide_names = [n for n in visible if "guide" in n]
    for g in guide_names:
        visible.discard(g)


def _ensure_listening(agent, instance) -> None:
    """Attach a persistent background _listen_messages task to a writer/guide
    instance, so it stays live and reactive for the WHOLE lemma — not just during
    one chunk's gather.

    The task parks on the instance's message channel and, when a message arrives,
    injects it into that instance's backend session. It coordinates with any
    orchestrator-driven run_ai() on the SAME instance via _driving_lock (held by
    run_ai for its whole run; only try-acquired by the listener) — so the listener
    yields the session whenever run_ai is driving and resumes when it finishes.
    That is what lets the guide answer the writer mid-chunk while the writer proves,
    and lets the writer answer the guide during the decision phase, with no torn
    turns and no split results.

    Idempotent: a no-op if the instance already has a live listen task. The task's
    lifetime is bound to the instance — _stop_listening is called wherever the
    instance is destroyed (_rotate_agent, _cleanup_agents).
    """
    if instance is None:
        return
    existing = getattr(instance, "_po5_listen_task", None)
    if existing is not None and not existing.done():
        return
    token = CancellationToken()
    task = asyncio.ensure_future(instance._listen_messages(token))
    instance._po5_listen_token = token
    instance._po5_listen_task = task


async def _stop_listening(instance) -> None:
    """Cancel and await the instance's persistent listen task (see _ensure_listening).

    Graceful first: signal the CancellationToken so the loop stops at its next
    boundary (never truncating an in-flight reply). Then hard-cancel the task as a
    backstop and await it so the coroutine is fully torn down before the instance's
    backend is disconnected.
    """
    if instance is None:
        return
    token = getattr(instance, "_po5_listen_token", None)
    task = getattr(instance, "_po5_listen_task", None)
    if token is not None:
        token.cancel()
    if task is not None and not task.done():
        task.cancel()
        try:
            await task
        except (asyncio.CancelledError, Exception):
            pass
    instance._po5_listen_token = None
    instance._po5_listen_task = None


async def _stop_all_listeners(agent) -> None:
    """Run-level sweep: cancel EVERY persistent listen task still attached to a
    cached guide/writer/closer instance on the orchestrator.

    Instances are cached on `agent` keyed by lemma id (`_guide_<id>`,
    `_writer_<id>`, …) and reused across chunks. They are torn down on rotation
    (_rotate_agent) and on the decompose path (_cleanup_agents), but a lemma that
    finishes proved/contingent/failed WITHOUT rotating leaves its instance — and
    its 1s-polling _listen_messages coroutine — cached for the rest of the run.
    Call this once at workflow completion so no listener outlives its usefulness.
    Identify instances by the marker attribute _ensure_listening sets, so we do
    not depend on which lemma ids are still live at the end.
    """
    seen = set()
    for value in list(vars(agent).values()):
        if id(value) in seen:
            continue
        seen.add(id(value))
        if getattr(value, "_po5_listen_task", None) is not None:
            await _stop_listening(value)


def _link_writer_guide(agent, writer_agent, guide_agent) -> str:
    """Open a live, bidirectional message channel between THIS writer and THIS
    guide instance and return the guide's current name.

    The writer proves a chunk while the guide is parked in its persistent
    ``_listen_messages`` task (see _ensure_listening), so a writer→guide message
    lands in real time and the guide can reply on the same channel. Likewise a
    guide→writer question between chunks reaches the writer's own live listener.
    `send_message` enforces a
    DIRECTED visibility check (recipient ∈ visibility_graph[sender]), so BOTH
    directions need an edge: writer→guide (to report) and guide→writer (to
    reply). Instance names change on rotation, so we (re)establish the edge each
    chunk with the current names rather than relying on spawn-time wiring.
    Idempotent — adding to a set is a no-op if the edge already exists.
    """
    registry = agent.swarm._registry
    graph = registry.visibility_graph
    writer_name = writer_agent.spec.name
    guide_name = guide_agent.spec.name
    graph.setdefault(writer_name, set()).add(guide_name)
    graph.setdefault(guide_name, set()).add(writer_name)
    return guide_name


async def _rotate_agent(agent, entry: LemmaEntry, cwd: Path, role: str, instance):
    """Dump agent state to disk and destroy the instance so a fresh one is created."""
    # Stop the persistent listen task BEFORE dumping state / disconnecting: the
    # state-dump below is itself a run_ai() call on this instance, and we must not
    # leave a listener racing it (or holding the session) as the backend goes away.
    await _stop_listening(instance)
    # Ask agent to dump its state
    try:
        result = await instance.run_ai(
            inp=(
                "DUMP YOUR STATE: Summarize everything you know about this proof.\n"
                "Include: strategies tried + outcomes, key insights, what to try next.\n"
                "Be concise but complete. This will be your memory for next session."
            ),
            max_turns=3,
        )
        state_text = result.raw_result or ""
    except Exception:
        state_text = ""

    # Write state to disk
    if state_text.strip():
        guide_dir = cwd / entry.workspace / "guide_state"
        guide_dir.mkdir(parents=True, exist_ok=True)
        filename = f"{entry.name}.md" if role == "guide" else f"writer_{entry.name}.md"
        (guide_dir / filename).write_text(state_text)

    # Destroy the instance
    attr = f"_{role}_{entry.id}"
    ctx_attr = f"{attr}_ctx"
    ctx = getattr(agent, ctx_attr, None)
    if ctx:
        try:
            await ctx.__aexit__(None, None, None)
        except Exception:
            pass
    setattr(agent, ctx_attr, None)
    setattr(agent, attr, None)


async def _cleanup_agents(agent, entry: LemmaEntry):
    """Destroy guide + writer + closer for this lemma (no state dump)."""
    for role in ("guide", "writer", "closer"):
        attr = f"_{role}_{entry.id}"
        ctx_attr = f"{attr}_ctx"
        instance = getattr(agent, attr, None)
        # Tear down the persistent listen task before disconnecting the backend.
        await _stop_listening(instance)
        ctx = getattr(agent, ctx_attr, None)
        if ctx:
            try:
                await ctx.__aexit__(None, None, None)
            except Exception:
                pass
            setattr(agent, ctx_attr, None)
            setattr(agent, attr, None)


# ═══════════════════════════════════════════════════════════════════════════════
# Helpers — detection worker
# ═══════════════════════════════════════════════════════════════════════════════

@dataclass
class DetectVerdict:
    file_path: str
    name: str
    signature_hash: str
    statement: str
    match_type: str  # "cycle" | "reuse" | "none"
    matched_id: str = ""
    matched_name: str = ""
    import_path: str = ""
    reason: str = ""


async def _run_detection(agent, state, ledger, entry, cwd) -> tuple[str, list[DetectVerdict]]:
    """Run cycle detection on staged files. Returns (result, verdicts)."""
    tools = get_lean_tools()
    new_decomp_dir = cwd / entry.workspace / "new_decomposition"
    if not new_decomp_dir.exists():
        return "no_cycle", []

    new_files = sorted(new_decomp_dir.glob("lemma_helper_*.lean"))
    if not new_files:
        return "no_cycle", []

    await agent._emit("message", f"[PO5] Detecting cycles on {len(new_files)} helpers...")

    pruned_hashes = set()
    for child_id in entry.children:
        child = ledger.get(child_id)
        if child and child.status in (LemmaStatus.PRUNED, LemmaStatus.CYCLE, LemmaStatus.FAILED):
            pruned_hashes.add(child.signature_hash)

    verdicts = []
    cycles_found = False
    matched_pruned = 0

    for f in new_files:
        rel = str(f.relative_to(cwd))
        split = tools.split_theorems(rel)
        if not split or not split.blocks:
            continue
        for block in split.blocks:
            if block.decl_type not in ("theorem", "def"):
                continue
            if "private " in block.text[:50]:
                continue
            if not block.has_sorry:
                verdicts.append(DetectVerdict(
                    file_path=rel, name=block.name,
                    signature_hash=LemmaLedger.compute_signature_hash(block.text),
                    statement=block.text, match_type="none"))
                continue

            sig_hash = LemmaLedger.compute_signature_hash(block.text)
            if sig_hash in pruned_hashes:
                matched_pruned += 1

            det_result = await detect(
                agent=agent, ledger=ledger, name=block.name,
                file_path=rel, signature_hash=sig_hash,
                parent_id=entry.id, cwd=cwd,
            )
            verdicts.append(DetectVerdict(
                file_path=rel, name=block.name, signature_hash=sig_hash,
                statement=block.text,
                match_type=det_result.match_type.value,
                matched_id=det_result.matched_id,
                matched_name=det_result.matched_name,
                import_path=det_result.import_path,
                reason=det_result.reason,
            ))
            if det_result.match_type == MatchType.CYCLE:
                cycles_found = True

    if matched_pruned > 0 and matched_pruned >= len(new_files):
        shutil.rmtree(new_decomp_dir)
        return "rejected", []

    # Commit: rename new_decomposition/ → decomposed/
    decomposed_dir = cwd / entry.workspace / "decomposed"
    if decomposed_dir.exists():
        idx = 0
        while (cwd / entry.workspace / f"decomposed_old_{idx}").exists():
            idx += 1
        decomposed_dir.rename(cwd / entry.workspace / f"decomposed_old_{idx}")
    new_decomp_dir.rename(decomposed_dir)
    _rewrite_imports(cwd, entry.workspace, "new_decomposition", "decomposed")

    for v in verdicts:
        v.file_path = v.file_path.replace("/new_decomposition/", "/decomposed/")

    await agent._emit("message",
        f"[PO5] Detection: {len(verdicts)} verdicts, cycles={'yes' if cycles_found else 'no'}")
    return ("cycle_found" if cycles_found else "no_cycle"), verdicts


# ═══════════════════════════════════════════════════════════════════════════════
# Helpers — ledger mutations (UPDATE phase internals)
# ═══════════════════════════════════════════════════════════════════════════════

def _apply_verdicts(state: PO5State, ledger: LemmaLedger, entry: LemmaEntry, cwd: Path):
    """Register detect verdicts into ledger."""
    verdicts = getattr(state, '_detect_verdicts', None)
    if not verdicts:
        return
    tools = get_lean_tools()

    for v in verdicts:
        if v.match_type == "cycle":
            new = _register_lemma(state, ledger,
                name=v.name, file_path=v.file_path,
                workspace=v.file_path.removesuffix(".lean"),
                signature_hash=v.signature_hash, statement=v.statement,
                parent_id=entry.id)
            if not isinstance(new, str):
                ledger.mark_cycle(new.id, v.matched_id)
            state.cycles_detected += 1
        elif v.match_type == "reuse":
            new = _register_lemma(state, ledger,
                name=v.name, file_path=v.file_path,
                workspace=v.file_path.removesuffix(".lean"),
                signature_hash=v.signature_hash, statement=v.statement,
                parent_id=entry.id)
            if not isinstance(new, str):
                ledger.add_parent(new.id, v.matched_id)
                matched = ledger.get(v.matched_id)
                if matched and matched.status == LemmaStatus.PROVED:
                    ledger.mark_proved(new.id, v.import_path, proved_by="shortcut")
                else:
                    ledger.mark_contingent(new.id)
        else:
            new = _register_lemma(state, ledger,
                name=v.name, file_path=v.file_path,
                workspace=v.file_path.removesuffix(".lean"),
                signature_hash=v.signature_hash, statement=v.statement,
                parent_id=entry.id)
            if not isinstance(new, str) and not tools.has_sorry(v.file_path):
                cr = tools.check_compiles(v.file_path)
                # Transitive oracle, not text/warning has_sorry: a locally clean
                # file can still depend on sorryAx through an import.
                if cr.success and _entry_transitively_proven(tools, new):
                    ledger.mark_proved(new.id, v.file_path.replace("/", ".").removesuffix(".lean"),
                                       proved_by="direct")
                elif cr.success:
                    ledger.mark_contingent(new.id)

    state._detect_verdicts = None
    if entry.status == LemmaStatus.PROVING:
        ledger.mark_contingent(entry.id)


def _entry_transitively_proven(tools, entry: LemmaEntry) -> bool:
    """AUTHORITATIVE per-entry proof check: the entry's obligation (its own
    theorem + any mutual-group peers) compiles, has no LOCAL sorry, and — via
    `#print axioms` — depends on NO `sorryAx`.

    This is the same oracle the per-target gate uses (`_attempt_prove`). It must
    be used everywhere an entry is promoted to PROVED, because the text/warning
    based `check_compiles.has_sorry` misses sorry reached transitively through
    imported/assembled dependencies (and is suppressed by `set_option
    warn.sorry false`). A synthetic `<file:...>` root has no theorem of its own,
    so it is verified by its children, not here — callers skip it.
    """
    stub_rel = entry.file_path
    cr = tools.check_compiles(stub_rel)
    if not cr.success:
        return False
    protected = _get_protected_names(tools, stub_rel, entry)
    if not protected:
        return False
    local_sorry = tools.get_sorries_by_theorem(stub_rel)
    if any(local_sorry.get(n) for n in protected):
        return False
    ax = tools.axioms_by_theorem(stub_rel, sorted(protected))
    return all(ax.is_proven(n) for n in protected)


def _proved_or_contingent(tools, ledger, entry, cwd, stub_rel) -> str | None:
    """Shared PROVED/CONTINGENT/fall-through decision for the prove loops.

    Assumes the file already compiles. Returns:
      - "proved":     protected block is transitively sorry-free (marks PROVED).
      - "contingent": block is locally clean but transitively depends on a sorry
                      owned by an unproven SIBLING obligation in this shared file
                      or a registered CHILD helper — i.e. we are WAITING for a
                      proof still in flight (marks CONTINGENT). _propagate_proved
                      promotes it once that sibling/subtree clears.
      - None:         no sibling/child explains the transitive sorry (untracked
                      dep or a fresh inline helper) → caller falls through to
                      continue proving / extraction.

    Centralizes the logic the per-target gate uses so the deep and grace loops
    stay consistent (they previously keyed CONTINGENT on `entry.children` only,
    missing the sibling-wait case and needlessly re-driving finished targets).
    """
    if _entry_transitively_proven(tools, entry):
        ledger.mark_proved(entry.id, stub_rel.replace("/", ".").removesuffix(".lean"))
        return "proved"
    local_sorry = tools.get_sorries_by_theorem(stub_rel)
    siblings = _sibling_target_names(ledger, entry, cwd, stub_rel)
    sibling_sorry = any(n in siblings and positions
                        for n, positions in local_sorry.items())
    if sibling_sorry or entry.children:
        ledger.mark_contingent(entry.id)
        return "contingent"
    return None


def _propagate_proved(ledger: LemmaLedger, cwd: Path):
    """Re-check contingent entries — mark proved only if TRANSITIVELY proven.

    A CONTINGENT entry is one that was locally sorry-free but waiting on a
    sibling/child. It is promoted to PROVED only when the authoritative
    transitive oracle confirms it depends on no `sorryAx` — NOT merely when the
    file is textually sorry-free. Entries that never clear stay CONTINGENT and
    are surfaced by the CHECK stuck-handler (re-picked → PENDING, or escalated
    to the guide) instead of being silently promoted.
    """
    tools = get_lean_tools()
    changed = True
    while changed:
        changed = False
        for e in ledger.entries():
            if e.status != LemmaStatus.CONTINGENT:
                continue
            if e.name.startswith("<"):
                # Synthetic file-root: proven when all its real children are.
                kids = ledger.get_children(e.id)
                real_kids = [k for k in kids if not k.name.startswith("<")]
                if real_kids and all(k.status == LemmaStatus.PROVED for k in real_kids):
                    ledger.mark_proved(e.id, e.file_path.replace("/", ".").removesuffix(".lean"),
                                       proved_by="assembly")
                    changed = True
                continue
            if not (cwd / e.file_path).exists():
                continue
            if _entry_transitively_proven(tools, e):
                ledger.mark_proved(e.id, e.file_path.replace("/", ".").removesuffix(".lean"),
                                   proved_by="assembly")
                changed = True


def _register_all_helpers(state: PO5State, ledger: LemmaLedger, entry: LemmaEntry, cwd: Path):
    """Register public theorems/defs from Stub.lean into ledger."""
    if entry.status == LemmaStatus.FAILED:
        return
    tools = get_lean_tools()
    stub_rel = _resolve_stub_simple(entry)
    if not (cwd / stub_rel).exists():
        return

    split = tools.split_theorems(stub_rel)
    if not split or split.error:
        return

    current_names = {b.name for b in split.blocks
                     if b.decl_type in ("theorem", "def") and "private " not in b.text[:50]}

    existing_names = {e.name for e in ledger.entries()}
    for block in split.blocks:
        if block.name in existing_names or block.name == entry.name:
            continue
        if block.decl_type not in ("theorem", "def") or "private " in block.text[:50]:
            continue
        sig_hash = LemmaLedger.compute_signature_hash(block.text)
        new = _register_lemma(state, ledger,
            name=block.name, file_path=stub_rel,
            workspace=entry.workspace, signature_hash=sig_hash,
            statement=block.text, parent_id=entry.id)
        if not isinstance(new, str) and not block.has_sorry:
            cr = tools.check_compiles(stub_rel)
            # Promote to PROVED only when the transitive oracle confirms it — a
            # locally sorry-free helper can still depend on sorryAx. Otherwise
            # leave it CONTINGENT so _propagate_proved re-checks it later.
            if cr.success and _entry_transitively_proven(tools, new):
                ledger.mark_proved(new.id, stub_rel.replace("/", ".").removesuffix(".lean"),
                                   proved_by="direct")
            elif cr.success:
                ledger.mark_contingent(new.id)


# ═══════════════════════════════════════════════════════════════════════════════
# Helpers — compilation fixer
# ═══════════════════════════════════════════════════════════════════════════════

async def _run_fixer(agent, state: PO5State, cwd: Path, error_text: str, advice: str) -> bool:
    """Spawn compilation fixer with guide's advice."""
    async with swarm_agent("compilation_fixer", swarm=agent.swarm, cwd=agent._cwd) as fixer:
        outcome = await verified_loop(
            agent_ctx=fixer,
            initial_input=(
                f"Fix these compilation errors:\n{error_text}\n\n"
                f"Guide's diagnosis:\n{advice}"
            ),
            verify=lambda: None,
            max_rounds=2, max_turns=30, use_run_ai=False,
        )
    return outcome.success if outcome else False


# ═══════════════════════════════════════════════════════════════════════════════
# Helpers — pure utilities
# ═══════════════════════════════════════════════════════════════════════════════

def _resolve_stub(entry: LemmaEntry, cwd: Path, state: PO5State) -> str:
    stub_rel = f"{entry.workspace}/Stub.lean" if "/Stub.lean" not in entry.file_path else entry.file_path
    if not (cwd / stub_rel).exists():
        setup_child_workspace(cwd, entry.file_path, state.root_workspace,
                              state.use_cheat_sheet, state.cheat_sheet_path)
        stub_rel = f"{entry.workspace}/Stub.lean"
        if not (cwd / stub_rel).exists():
            stub_rel = entry.file_path
    return stub_rel


def _resolve_stub_simple(entry: LemmaEntry) -> str:
    return f"{entry.workspace}/Stub.lean" if "/Stub.lean" not in entry.file_path else entry.file_path


def _make_verifier(entry, stub_rel, original_content, ledger, cwd):
    ancestor_modules = []
    for anc_id in ledger.get_ancestry(entry.id):
        anc = ledger.get(anc_id)
        if anc:
            ancestor_modules.append(anc.workspace.replace("/", "."))
    return make_proof_writer_verifier(
        stub_rel, original_content, entry.workspace, entry.name,
        ancestor_modules=ancestor_modules, ledger=ledger)


def _sibling_target_names(ledger, entry, cwd: Path | None = None,
                          stub_rel: str | None = None) -> set[str]:
    """Names of OTHER top-level declarations in this entry's file that must NOT be
    extracted as helpers.

    Two sources, unioned:
    1. Other registered obligations sharing this file_path (the ledger view). Covers
       the multi-target synthetic-root case where every target is registered.
    2. Every OTHER top-level theorem/def present in the ORIGINAL file snapshot
       (Stub.clean.lean). This covers the case where the user targeted only a SUBSET
       of the file's sorry-theorems — the un-targeted ones aren't in the ledger, but
       they are still original obligations, not helpers. Genuine writer-created helpers
       are absent from the snapshot (created later), so they stay extractable.

    The entry's own name (and mutual-group peers, handled by protected_names) are the
    caller's concern; here we just exclude the entry itself and the synthetic root.
    """
    names = {
        e.name for e in ledger.entries()
        if e.id != entry.id and e.file_path == entry.file_path
        and not e.name.startswith("<")  # exclude the synthetic file-root marker
    }
    if cwd is not None:
        clean = cwd / entry.workspace / "Stub.clean.lean"
        if clean.exists():
            tools = get_lean_tools()
            snap = tools.split_theorems(str(clean.relative_to(cwd)))
            if snap and not snap.error:
                for b in snap.blocks:
                    if b.name != entry.name and b.decl_type in ("theorem", "def"):
                        names.add(b.name)
    names.discard(entry.name)
    return names


def _filter_requested_targets(targets, split, requested_names):
    """Narrow sorry-targets to the user's requested theorem names.

    Empty requested_names → return all targets (prove everything with sorry).
    A requested name matches a target if it IS the target's representative name,
    or (for mutual groups) if it is any member of that group. Requested names that
    are already proven or don't exist simply don't match (reported by the caller).
    """
    if not requested_names:
        return targets
    wanted = set(requested_names)
    selected = []
    for block, is_mut in targets:
        names_for_target = {block.name}
        if block.mutual_group is not None:
            names_for_target |= set(split.mutual_groups.get(block.mutual_group, []))
        if wanted & names_for_target:
            selected.append((block, is_mut))
    return selected


def _collect_sorry_targets(split):
    """Top-level proof obligations in a freshly-split file.

    Returns a list of (representative_block, is_mutual) tuples — one per standalone
    theorem/def that has sorry, and one per mutual group that contains any sorry
    (represented by its first member, matching how _get_protected_names expands a
    mutual group). Definitions and already-proven blocks are skipped.
    """
    targets = []
    seen_groups: set[int] = set()
    for block in split.blocks:
        if block.mutual_group is not None:
            gid = block.mutual_group
            if gid in seen_groups:
                continue
            members = [b for b in split.blocks if b.mutual_group == gid]
            if any(b.has_sorry for b in members):
                seen_groups.add(gid)
                # Representative = first member (lowest start line)
                rep = min(members, key=lambda b: b.start)
                targets.append((rep, True))
            continue
        if block.decl_type not in ("theorem", "def"):
            continue
        if not block.has_sorry:
            continue
        targets.append((block, False))
    return targets


def _requested_obligation_names(ledger, state, root_stub: str) -> list[str]:
    """The real theorem names the TM asked us to prove, for the root file.

    These are the entries registered at INIT (already narrowed to the requested
    subset by `_filter_requested_targets`): either the single real root, or the
    children of the synthetic `<file:...>` root. Synthetic `<...>` labels are
    excluded. Mutual-group members are expanded so the whole group is verified.
    """
    root = ledger.get(state.root_id)
    if not root:
        return []
    if root.name.startswith("<"):
        entries = ledger.get_children(state.root_id)
    else:
        entries = [root]

    names: set[str] = set()
    split = get_lean_tools().split_theorems(root_stub)
    blocks = split.blocks if split and not split.error else []
    groups = split.mutual_groups if split and not split.error else {}
    for e in entries:
        if e.name.startswith("<"):
            continue
        names.add(e.name)
        # Expand mutual groups: every member must be sorry-free, not just the rep.
        for b in blocks:
            if b.name == e.name and b.mutual_group is not None:
                names.update(groups.get(b.mutual_group, []))
                break
    return sorted(names)


def _is_top_level(ledger, state, entry) -> bool:
    """True iff `entry` is one of the TOP-LEVEL requested obligations.

    A top-level obligation is either the single real root, or a DIRECT child of
    the synthetic `<file:...>` root (one of the theorems the TM asked us to prove
    — see `_requested_obligation_names`). Decomposed helpers (grandchildren) are
    NOT top-level: the user never asked for them, so we don't burden the user
    with a fix request about a lemma the prover invented.
    """
    if entry.id == state.root_id:
        return True
    root = ledger.get(state.root_id)
    if root and root.name.startswith("<"):
        parent = ledger.get_parent(entry.id)
        return parent is not None and parent.id == state.root_id
    return False


def _record_give_up(state, entry, reason: str):
    """Accumulate a give-up reason on state so it propagates to the TM → user.

    De-duplicates: the same lemma re-deriving the same give-up must not append the
    identical line hundreds of times (Bug #3 symptom)."""
    line = f"'{entry.name}': {reason}"
    existing = state.give_up_reason.split("\n") if state.give_up_reason else []
    if line in existing:
        return
    if state.give_up_reason:
        state.give_up_reason += f"\n{line}"
    else:
        state.give_up_reason = line


async def _ask_guide_user_fix(agent, state, ledger, entry, cwd, give_up_reason: str):
    """Ask the guide whether the USER must fix something before this can be proved.

    Only meaningful for TOP-LEVEL requested theorems (the user owns the goal
    statement and its definitions/dependencies; they did not write the prover's
    internal helpers). Records the request on `state.user_fix_request` so the
    Task Manager can relay it verbatim to the user. Best-effort: any failure
    leaves user_fix_request untouched (the give_up_reason still propagates).
    """
    if not _is_top_level(ledger, state, entry):
        return
    try:
        decision, _reason, extras = await _consult_guide_decide(
            agent, state, ledger, entry, cwd,
            options=["user_fix", "no_user_fix"],
            task=(
                f"You are giving up on the top-level theorem '{entry.name}'.\n"
                f"Give-up reason: {give_up_reason}\n\n"
                f"Does the USER need to fix something before this can be proved?\n"
                f"- user_fix: the goal statement is false/mis-stated, a definition "
                f"is wrong, a needed hypothesis is missing, or a required "
                f"dependency/lemma is unavailable — something ONLY the user can change.\n"
                f"- no_user_fix: it's provable as stated; we just couldn't find the proof."
            ),
            post_prompt=(
                "FIX: <if user_fix, one or two concrete sentences telling the user "
                "EXACTLY what to change (file/def/statement); else 'none'>"),
            post_prompt_parser=lambda raw: {
                "fix": (m.group(1).strip()
                        if (m := re.search(r'FIX:\s*(.+)', raw, re.DOTALL)) else "")},
        )
    except Exception as e:
        await agent._emit("message", f"[PO5] user-fix consult failed: {e}")
        return
    if decision == "user_fix":
        fix = extras.get("fix", "").strip()
        if fix and fix.lower() != "none":
            request = f"'{entry.name}': {fix}"
            if state.user_fix_request:
                state.user_fix_request += f"\n{request}"
            else:
                state.user_fix_request = request
            await agent._emit("message", f"[PO5] Guide requests user fix for '{entry.name}': {fix}")


def _get_protected_names(tools, stub_rel, entry) -> set[str]:
    split = tools.split_theorems(stub_rel)
    protected = {entry.name}
    for block in split.blocks:
        if block.name == entry.name and block.mutual_group is not None:
            protected = set(split.mutual_groups.get(block.mutual_group, [entry.name]))
            break
    return protected


def _format_progress(prev: int | None, current: int, *, compiles: bool = True) -> str:
    """Render the chunk-over-chunk progress line from the LEAF-sorry count.

    `current`/`prev` are counts of literal `sorry` tokens in our obligations
    (build-INDEPENDENT), not the axioms-verdict decl count. The one special case
    is the ENDGAME: 0 sorries left but the file does not yet compile — the writer
    has replaced the last sorry with a real (still-buggy) proof and is closing
    compile errors. That is forward motion on the critical path, NOT a stall, so
    it gets its own positive message (and the caller keeps the idle clock alive)."""
    if current == 0 and not compiles:
        if prev is not None and prev > 0:
            return (f"PROGRESS: last sorry closed ({prev} → 0). SKETCH COMPLETE — "
                    f"0 sorries remaining; writer is closing compile errors on the "
                    f"full proof (endgame, not a stall).")
        return ("SKETCH COMPLETE — 0 sorries remaining; writer is closing compile "
                "errors on the full proof (endgame, not a stall).")
    if prev is None:
        return f"Open leaf-sorries: {current}."
    if current < prev:
        return f"PROGRESS: leaf-sorries {prev} → {current}."
    elif current == prev:
        return f"NO REDUCTION: still {current} leaf-sorries."
    return f"Leaf-sorry count: {current} (was {prev})."


def _format_sorry_map(tsm, protected_names: set, siblings: set) -> str:
    """Render the AUTHORITATIVE dependency+sorry overview for the guide.

    ONE consolidated picture, recomputed this chunk from ground truth — it
    supersedes anything the guide remembers or reads from snapshot notes. For each
    protected target: is it done, and exactly which in-file lemmas it transitively
    depends on that still carry a `sorry` (with fresh line numbers)."""
    if tsm.error:
        return f"AUTHORITATIVE SORRY MAP: unavailable (parse error: {tsm.error})\n"
    if not tsm.build_ok:
        return (
            "AUTHORITATIVE SORRY MAP: build FAILED — cannot confirm anything "
            f"(treat all as unproven): {tsm.build_error}\n")

    def _line(n: str) -> str:
        d = tsm.decls.get(n)
        if not d:
            return f"    • {n}  (not found in file)"
        pos = ""
        if d.sorry_positions:
            ls = ", ".join(str(p.get("line", "?") + 1) for p in d.sorry_positions)
            pos = f"  sorry @ line {ls}"
        elif d.start:
            pos = f"  (decl @ line {d.start}, transitive sorry via a dep)"
        return f"    • {n}{pos}"

    out = [
        "AUTHORITATIVE SORRY MAP (recomputed NOW from ground truth — this "
        "SUPERSEDES any line numbers you remember or that appear in snapshot notes):"
    ]
    for t in sorted(protected_names):
        info = tsm.targets.get(t)
        if info is None:
            out.append(f"  TARGET {t}: (not found in file)")
            continue
        if info.done:
            out.append(f"  TARGET {t}: ✅ DONE (transitively sorry-free)")
            continue
        # open deps that are OURS (not the target itself, not siblings)
        ours = [n for n in info.open_deps
                if n != t and n not in siblings]
        out.append(f"  TARGET {t}: ❌ NOT DONE (transitively depends on sorry)")
        if t in info.open_deps and (tsm.decls.get(t) and tsm.decls[t].sorry_positions):
            out.append("    (its own body still has a literal sorry)")
            out.append(_line(t))
        if ours:
            out.append("    In-file lemmas it uses that are still UNPROVEN (yours to close):")
            for n in ours:
                out.append(_line(n))
        sib_open = [n for n in info.open_deps if n in siblings]
        if sib_open:
            out.append(f"    (NOT yours — sibling obligations still open: {sib_open})")
    out.append(f"  Transitive OPEN-sorry count reachable from your targets: "
               f"{tsm.open_sorry_count()}")
    return "\n".join(out) + "\n"


def _verify_extraction(tools, stub_rel: str, entry: LemmaEntry, output_dir: Path) -> str | None:
    # Check that files were actually created — if the extractor reverted, this catches it
    if not output_dir.exists() or not list(output_dir.glob("lemma_helper_*.lean")):
        return "No helper files created (extractor may have reverted)"
    split = tools.split_theorems(stub_rel)
    if not split or split.error:
        return f"Cannot parse Stub.lean: {split.error if split else 'unknown'}"
    protected = {entry.name}
    for block in split.blocks:
        if block.name == entry.name and block.mutual_group is not None:
            protected = set(split.mutual_groups.get(block.mutual_group, [entry.name]))
            break
    sorry_info = tools.get_sorries_by_theorem(stub_rel)
    bad = [n for n in protected if n in sorry_info]
    if bad:
        return f"Protected block has sorry: {bad}"
    return None


def _repair_orphaned_decomposed(entry: LemmaEntry, cwd: Path, stub_rel: str):
    """Detect and fix: decomposed/ dir exists but Stub.lean doesn't import from it.

    This happens after a process crash between extraction and state persistence,
    or when a child failure brings the parent back to PROVE without proper restoration.
    Fix: re-add the missing imports so Stub.lean uses the precompiled helpers.
    """
    decomposed_dir = cwd / entry.workspace / "decomposed"
    if not decomposed_dir.exists():
        return
    helper_files = sorted(decomposed_dir.glob("lemma_helper_*.lean"))
    if not helper_files:
        return

    stub_path = cwd / stub_rel
    content = stub_path.read_text()

    # Check if Stub.lean already imports from decomposed/
    ws_module = entry.workspace.replace("/", ".")
    decomposed_import_prefix = f"import {ws_module}.decomposed."
    if decomposed_import_prefix in content:
        return

    # Stub.lean doesn't import the helpers — add them
    lines = content.splitlines()
    import_end = 0
    for i, l in enumerate(lines):
        if l.strip().startswith("import "):
            import_end = i + 1

    new_imports = []
    for hf in helper_files:
        module = f"{ws_module}.decomposed.{hf.stem}"
        imp_line = f"import {module}"
        if imp_line not in content:
            new_imports.append(imp_line)

    if not new_imports:
        return

    # Insert imports and remove inlined helper blocks (they're now in separate files)
    # Strategy: keep only the main theorem + any block not in decomposed/
    # Simple approach: just add imports — the duplicate definitions will cause errors
    # Better: use split_theorems to identify and remove inlined blocks that exist in decomposed/
    tools = get_lean_tools()
    helper_names = {hf.stem.removeprefix("lemma_helper_") for hf in helper_files}

    split = tools.split_theorems(stub_rel)
    if not split or split.error:
        # Can't parse — just add imports and hope for the best
        lines = lines[:import_end] + new_imports + lines[import_end:]
        stub_path.write_text("\n".join(lines))
        return

    # Remove blocks whose names match extracted helpers
    lines_to_remove: set[int] = set()
    for block in split.blocks:
        if block.name in helper_names and block.name != entry.name:
            for i in range(block.start - 1, block.end):
                lines_to_remove.add(i)

    new_lines = lines[:import_end] + new_imports
    for i in range(import_end, len(lines)):
        if i not in lines_to_remove:
            new_lines.append(lines[i])

    # Clean up multiple blank lines
    cleaned = []
    prev_blank = False
    for l in new_lines:
        if l.strip() == "":
            if not prev_blank:
                cleaned.append(l)
            prev_blank = True
        else:
            cleaned.append(l)
            prev_blank = False

    stub_path.write_text("\n".join(cleaned))


def _revert_extraction(entry: LemmaEntry, cwd: Path):
    predecomp = cwd / entry.workspace / "Stub.predecomp.lean"
    stub = cwd / entry.workspace / "Stub.lean"
    if predecomp.exists():
        shutil.copy2(predecomp, stub)
    for subdir in ("new_decomposition", "decomposed"):
        d = cwd / entry.workspace / subdir
        if d.exists():
            shutil.rmtree(d)


def _rewrite_imports(cwd: Path, workspace: str, old_name: str, new_name: str):
    old_mod = old_name.replace("/", ".")
    new_mod = new_name.replace("/", ".")
    stub = cwd / workspace / "Stub.lean"
    if stub.exists():
        content = stub.read_text()
        if old_mod in content:
            stub.write_text(content.replace(old_mod, new_mod))
    renamed = cwd / workspace / new_name
    if renamed.exists():
        for f in renamed.rglob("*.lean"):
            content = f.read_text()
            if old_mod in content:
                f.write_text(content.replace(old_mod, new_mod))


def _resolve_import_dependencies(ledger: LemmaLedger, cwd: Path):
    """Add cross-branch dependency edges inferred from Lean imports.

    This is meaningful ONLY for the separate-workspace model where each lemma
    lives in its own file (module ↔ entry is 1:1). In a SHARED multi-theorem
    file, every target and the synthetic root have the same file_path/module, so
    (a) a module→id map would collapse them and (b) reading the shared file's
    imports for every entry would attribute a single helper-import to all of
    them — corrupting the DAG. The correct parent→child edges for shared-file
    targets are already set at registration/extraction time, so we simply skip
    any entry whose file_path is not unique to it (both as import source and as
    resolvable target).
    """
    tools = get_lean_tools()

    file_path_counts: dict[str, int] = {}
    for e in ledger.entries():
        file_path_counts[e.file_path] = file_path_counts.get(e.file_path, 0) + 1

    module_to_id = {}
    for e in ledger.entries():
        if file_path_counts[e.file_path] != 1:
            continue  # ambiguous shared-file module — not a resolvable target
        module = e.file_path.replace("/", ".").removesuffix(".lean")
        module_to_id[module] = e.id

    existing_edges = set()
    for e in ledger.entries():
        for cid in e.children:
            existing_edges.add((e.id, cid))

    for e in ledger.entries():
        if file_path_counts[e.file_path] != 1:
            continue  # shared file — imports can't be attributed to one entry
        if not (cwd / e.file_path).exists():
            continue
        imports = tools.check_imports(e.file_path)
        if imports.error:
            continue
        for imp in imports.imports:
            if imp in module_to_id:
                dep_id = module_to_id[imp]
                if dep_id == e.id:
                    continue
                if (e.id, dep_id) in existing_edges or (dep_id, e.id) in existing_edges:
                    continue
                ancestry = ledger.get_ancestry(e.id)
                if dep_id in ancestry:
                    continue
                ledger.add_parent(e.id, dep_id)


def _find_dfs_candidates(ledger, start_id):
    if not start_id:
        pending = [e for e in ledger.entries() if e.status == LemmaStatus.PENDING]
        return (None, pending)
    current = ledger.get(start_id)
    visited = set()
    while current:
        if current.id in visited:
            break
        visited.add(current.id)
        pending_kids = ledger.pending_children(current.id)
        if pending_kids:
            return (current, pending_kids)
        current = ledger.get_parent(current.id)
    pending = [e for e in ledger.entries() if e.status == LemmaStatus.PENDING]
    return (None, pending)


def _topo_sort(ledger: LemmaLedger) -> list[str]:
    result = []
    visited = set()
    def visit(eid):
        if eid in visited:
            return
        visited.add(eid)
        e = ledger.get(eid)
        if e:
            for cid in e.children:
                visit(cid)
        result.append(eid)
    for e in ledger.entries():
        visit(e.id)
    return result


def _build_ledger_summary(ledger: LemmaLedger, entry: LemmaEntry) -> str:
    lines = [f"Lemma DAG ({len(list(ledger.entries()))} entries):"]
    for e in ledger.entries():
        marker = {"proved": "✓", "contingent": "◇", "proving": "⟳",
                  "pending": "○", "failed": "✗", "cycle": "⊘"}.get(e.status, "?")
        suffix = ""
        if e.failure_reason:
            suffix = f" FAIL: {e.failure_reason[:40]}"
        lines.append(f"  {marker} {e.name} [{e.status}] d={e.depth}{suffix}")
    return "\n".join(lines)


def _save_state(cwd: Path, state: PO5State):
    import yaml
    state_dir = cwd / "StrataAgent" / "strataswarm" / "temp"
    state_dir.mkdir(parents=True, exist_ok=True)
    data = {
        "root_workspace": state.root_workspace,
        "root_theorem_name": state.root_theorem_name,
        "requested_theorem_names": list(state.requested_theorem_names),
        "use_cheat_sheet": state.use_cheat_sheet,
        "cheat_sheet_path": state.cheat_sheet_path,
        "root_id": state.root_id,
        "stage": state.stage,
        "current_lemma_id": state.current_lemma_id,
        "total_attempts": state.total_attempts,
        "lemmas_proved": state.lemmas_proved,
        "cycles_detected": state.cycles_detected,
        "give_up_reason": state.give_up_reason,
        "user_fix_request": state.user_fix_request,
    }
    (state_dir / "po5_state.yaml").write_text(
        yaml.dump(data, default_flow_style=False))


def _load_state(cwd: Path, workspace_rel: str) -> PO5State | None:
    import yaml
    state_file = cwd / "StrataAgent" / "strataswarm" / "temp" / "po5_state.yaml"
    if not state_file.exists():
        return None
    try:
        data = yaml.safe_load(state_file.read_text())
        if data.get("root_workspace") != workspace_rel:
            return None
        s = PO5State()
        for k, v in data.items():
            if hasattr(s, k):
                setattr(s, k, v)
        return s
    except Exception:
        return None
