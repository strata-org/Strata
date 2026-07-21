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
from .po_util import setup_child_workspace, copy_cheat_sheet, cheat_sheet_name
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
    agent_registry: dict = field(default_factory=dict)
    lemma_ctx: dict = field(default_factory=dict)  # lemma_id → LemmaContext
    total_attempts: int = 0
    lemmas_proved: int = 0
    cycles_detected: int = 0


def _read_hint(state: PO5State) -> str:
    """'the cheat sheet and the file' / 'the file' depending on cheat-sheet config."""
    return "the cheat sheet and the file" if cheat_sheet_name(
        state.use_cheat_sheet, state.cheat_sheet_path) else "the file"


# ═══════════════════════════════════════════════════════════════════════════════
# Guide APIs — the only way to interact with the guide
# ═══════════════════════════════════════════════════════════════════════════════

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

    result = await guide.run_ai(inp=task)
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
        f"{task}\n\n"
        f"DECIDE one of: [{options_str}]\n"
        f"Reply EXACTLY:\n"
        f"DECISION: <{options_str}>\n"
    )
    if post_prompt:
        prompt += post_prompt + "\n"
    prompt += "REASON: <one sentence>"

    result = await guide.run_ai(inp=prompt)
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
    """Set failure_context on the parent so its guide sees it on next activation."""
    parent = ledger.get_parent(entry.id)
    if parent:
        parent_ctx = state.lemma_ctx.get(parent.id)
        if parent_ctx:
            # Append — parent might have multiple failed children
            if parent_ctx.failure_context:
                parent_ctx.failure_context += f"\n{message}"
            else:
                parent_ctx.failure_context = message
        else:
            state.lemma_ctx[parent.id] = LemmaContext(failure_context=message)


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
    else:
        workspace_rel = str(inp) if inp else ""
        theorem_names, theorem_file = [], ""
        skip_soundness = False
        use_cheat_sheet = True
        cheat_sheet_path = ""

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

        copy_cheat_sheet(cwd, cwd / workspace_rel,
                         state.use_cheat_sheet, state.cheat_sheet_path)

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
                               "cycles": state.cycles_detected})


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
    # Extract initial turns from guide's advice
    turns_match = re.search(r'TURNS:\s*(\d+)', advice)
    chunk_budget = max(MIN_CHUNK_TURNS, min(MAX_CHUNK_TURNS, int(turns_match.group(1)))) if turns_match else CHUNK_TURNS

    while True:
        ledger.increment_attempts(entry.id)
        elapsed = _time.time() - getattr(agent, '_po4_start_time', _time.time())
        writer_pct = await writer.get_context_percentage()
        # _get_guide handles rotation internally if >= 75%
        guide = await _get_guide(agent, entry, state, ledger)
        guide_pct = await guide.get_context_percentage()
        await agent._emit("message",
            f"[PO5] Chunk {entry.attempts} ({chunk_budget}t, total={total_turns}) "
            f"[{elapsed/60:.1f}min] | writer: {writer_pct or 0:.0f}% | guide: {guide_pct or 0:.0f}%")

        # Writer works
        chunk = min(MAX_CHUNK_TURNS, max(MIN_CHUNK_TURNS, chunk_budget))
        # We will let the guide run in background meanwhile
        cancellation_token = CancellationToken()

        async def _run_guide_while_listening_to_messages():
            result = await guide.run_while_listening_to_messages(cancellation_token=cancellation_token)
            await agent._emit("message", f"[PO5] Guide stopped listening for messages: {result.raw_result or ''}")
            return result.raw_result or ""

        async def _run_writer_then_cancel():
            result = await verified_loop(
                agent_ctx=writer,
                initial_input=(
                    f"STRATEGY ADVICE from your proof guide:\n{advice}\n\n"
                    f"You have {chunk} turns. File MUST compile (sorry allowed).{scope_note}"
                ),
                verify=verify_fn, max_rounds=2, max_turns=chunk, use_run_ai=True,
            )
            await agent._emit("message", f"[PO5] Writer finished chunk {entry.attempts} ({total_turns} total turns)")
            cancellation_token.cancel()
            await agent._emit("message", "[PO5] Cancelled guide listening to messages")
            await asyncio.sleep(2)  # give guide a moment to stop listening
            return result

        outcome, _ = await asyncio.gather(
            _run_writer_then_cancel(),
            _run_guide_while_listening_to_messages(),
        )

        # outcome = await verified_loop(
        #     agent_ctx=writer,
        #     initial_input=(
        #         f"STRATEGY ADVICE from your proof guide:\n{advice}\n\n"
        #         f"You have {chunk} turns. File MUST compile (sorry allowed)."
        #     ),
        #     verify=verify_fn, max_rounds=2, max_turns=chunk, use_run_ai=True,
        # )
        total_turns += chunk

        # Check: proved? (TARGET-SCOPED — a shared file may hold sibling theorems
        # whose sorry is not ours to close, so we gate on the protected block only.)
        cr = tools.check_compiles(stub_rel)
        if cr.success:
            # 1. Cheap local check: is the protected block free of literal sorry?
            local_sorry = tools.get_sorries_by_theorem(stub_rel)
            protected_local_sorry = sum(len(local_sorry.get(n, [])) for n in protected_names)
            if protected_local_sorry == 0:
                # 2. Authoritative transitive check via `#print axioms`: the protected
                #    block is proven iff NONE of its members depend on sorryAx.
                ax = tools.axioms_by_theorem(stub_rel, sorted(protected_names))
                if all(ax.is_proven(n) for n in protected_names):
                    ledger.mark_proved(entry.id, stub_rel.replace("/", ".").removesuffix(".lean"))
                    return "proved"
                # Protected block is locally sorry-free but transitively depends on a
                # sorry (through a child/import). Wait on children if any are registered.
                if entry.children:
                    ledger.mark_contingent(entry.id)
                    return "contingent"
                # No children yet: transitive sorry from untracked deps —
                # fall through to extraction (will discover and register them).

        # Gather state
        sorry_info = tools.get_sorries_by_theorem(stub_rel)
        sorry_count = sum(len(v) for v in sorry_info.values())
        progress = _format_progress(prev_sorry_count, sorry_count)
        prev_sorry_count = sorry_count
        writer_pct = await writer.get_context_percentage()

        # Guide reviews → next advice
        compile_note = ""
        if not outcome.success and outcome.last_error:
            compile_note = f"\n⚠️ COMPILATION FAILED after {outcome.rounds} fix rounds: {outcome.last_error}\n"
        await agent._emit("message", f"[PO5] Guide reviews: {progress}{' (NOT COMPILING)' if compile_note else ''}")
        advice = await _consult_guide_raw(agent, state, ledger, entry, cwd,
            task=(
                f"Writer completed chunk {entry.attempts} ({total_turns} total turns).\n"
                f"Writer context: {writer_pct or 0:.0f}%\n"
                f"{progress}\nFile: {stub_rel}\nSorries: {sorry_info}\n"
                f"{compile_note}"
                f"Diagnose and advise what to try next."
            ))

        # Guide decides
        def _parse_turns(raw: str) -> dict:
            m = re.search(r'TURNS:\s*(\d+)', raw)
            return {"turns": int(m.group(1))} if m else {}

        # Track consecutive no-reduction chunks
        if not hasattr(entry, '_stuck_count'):
            entry._stuck_count = 0
        if sorry_count > 0 and prev_sorry_count is not None and sorry_count >= prev_sorry_count:
            entry._stuck_count = getattr(entry, '_stuck_count', 0) + 1
        else:
            entry._stuck_count = 0

        stuck_hint = ""
        if entry._stuck_count >= 3:
            stuck_hint = (
                f"\n⚠️ STUCK: {entry._stuck_count} consecutive chunks with no sorry reduction. "
                f"Consider decompose even if context is low — the writer may be unable to close "
                f"these obligations in the current file.\n"
            )

        decision, reason, extras = await _consult_guide_decide(
            agent, state, ledger, entry, cwd,
            options=["continue", "decompose", "fresh_start", "give_up"],
            task=(
                f"Writer context: {writer_pct or 0:.0f}%\n"
                f"- continue: Keep trying in this file.\n"
                f"- decompose: Needs helpers in separate files.\n"
                f"- fresh_start: Current approach exhausted, start over.\n"
                f"- give_up: Statement is false."
                f"{stuck_hint}"
            ),
            post_prompt=f"TURNS: <{MIN_CHUNK_TURNS}-{MAX_CHUNK_TURNS}> (how many turns for writer next, if continue)",
            post_prompt_parser=_parse_turns,
        )

        if decision == "give_up":
            await agent._emit("message", f"[PO5] Guide gives up: {reason}")
            ctx.failure_context = f"Guide gave up: {reason}"
            ledger.mark_failed(entry.id, f"Guide gave up: {reason}")
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

        # Check: proved?
        if not tools.has_sorry(stub_rel) and tools.check_compiles(stub_rel).success:
            cr = tools.check_compiles(stub_rel)
            if not cr.has_sorry:
                ledger.mark_proved(entry.id, stub_rel.replace("/", ".").removesuffix(".lean"))
                return "proved"
            else:
                if entry.children:
                    ledger.mark_contingent(entry.id)
                    return "contingent"
                # No children: transitive sorry from untracked imports — continue proving

        # Gather state
        sorry_info = tools.get_sorries_by_theorem(stub_rel)
        sorry_count = sum(len(v) for v in sorry_info.values())
        progress = _format_progress(prev_sorry_count, sorry_count)
        prev_sorry_count = sorry_count
        writer_pct = await deep_writer.get_context_percentage()

        # Guide reviews → next advice
        await agent._emit("message", f"[PO5] Deep guide reviews: {progress}")
        advice = await _consult_guide_raw(agent, state, ledger, entry, cwd,
            task=(
                f"Writer completed chunk ({total_turns} total turns).\n"
                f"Writer context: {writer_pct or 0:.0f}%\n"
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
                f"Writer context: {writer_pct or 0:.0f}%\n"
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
    """Factor sorry out of protected block into standalone helpers."""
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

    await agent._emit("message", f"[PO5] Grace: {protected_sorry} sorry in protected block")

    prev_count = protected_sorry
    for grace in range(max(protected_sorry, 3)):
        sorry_info = tools.get_sorries_by_theorem(stub_rel)
        positions = {n: sorry_info.get(n, []) for n in protected_names if sorry_info.get(n)}

        await verified_loop(
            agent_ctx=writer,
            initial_input=(
                f"WRAP UP — grace {grace+1}.\n"
                f"Sorry in protected block: {positions}\n"
                f"Factor each sorry into a NEW helper theorem declared ABOVE, IN THIS SAME "
                f"FILE (you cannot create files — the extraction pipeline moves them out "
                f"later), then close the protected block with `exact helper ...`.\n"
                f"Protected block ({sorted(protected_names)}) must be sorry-free."
                f"{mutual_note}\nYou have {GRACE_TURNS} turns."
            ),
            verify=verify_fn, max_rounds=2, max_turns=GRACE_TURNS, use_run_ai=True,
        )

        if not tools.has_sorry(stub_rel) and tools.check_compiles(stub_rel).success:
            cr = tools.check_compiles(stub_rel)
            if not cr.has_sorry:
                ledger.mark_proved(entry.id, stub_rel.replace("/", ".").removesuffix(".lean"))
                return "proved"
            else:
                if entry.children:
                    ledger.mark_contingent(entry.id)
                    return "contingent"
                # No children: fall through to continue grace phase

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

    session = MoveSession(tools, stub_rel, entry.name, entry.workspace,
                          output_subdir="new_decomposition")
    extractor_mcp = create_extractor_mcp_server(session)

    split = tools.split_theorems(stub_rel)
    protected_names = _get_protected_names(tools, stub_rel, entry)
    # Sibling obligations sharing this file must not be extracted as helpers.
    siblings = _sibling_target_names(ledger, entry, cwd, stub_rel)
    extractable = [b for b in split.blocks
                   if b.name not in protected_names and b.mutual_group is None
                   and b.name not in siblings]

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
                return Trans.ASSEMBLY_FAILED
    else:
        return Trans.ASSEMBLY_FAILED

    # Check root sorry-free
    root_stub = f"{state.root_workspace}/Stub.lean"
    cr = tools.check_compiles(root_stub)
    if cr.success and not cr.has_sorry:
        ledger.mark_proved(state.root_id, root_stub.replace("/", ".").removesuffix(".lean"))
        await agent._emit("message", "[PO5] Assembly complete: root sorry-free ✅")

    return Trans.ASSEMBLED


# ═══════════════════════════════════════════════════════════════════════════════
# Helpers — agent management
# ═══════════════════════════════════════════════════════════════════════════════

CONTEXT_ROTATION_THRESHOLD = 75.0  # percent

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
        ctx = swarm_agent(
            "proof_guide", swarm=agent.swarm, cwd=agent._cwd,
            workspace=entry.workspace,
            template_vars={"cheat_sheet_path": cheat_rel},
            can_see=["SearchAgent"],
            extra_mcp_servers={"ledger": ledger_mcp},
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
        ctx = swarm_agent(
            "proof_writer_v2", swarm=agent.swarm, cwd=agent._cwd,
            workspace=entry.workspace,
            can_see=["SearchAgent"],
            extra_mcp_servers={"writer_imports": import_mcp},
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


async def _rotate_agent(agent, entry: LemmaEntry, cwd: Path, role: str, instance):
    """Dump agent state to disk and destroy the instance so a fresh one is created."""
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
                if cr.success and not cr.has_sorry:
                    ledger.mark_proved(new.id, v.file_path.replace("/", ".").removesuffix(".lean"),
                                       proved_by="direct")
                elif cr.success:
                    ledger.mark_contingent(new.id)

    state._detect_verdicts = None
    if entry.status == LemmaStatus.PROVING:
        ledger.mark_contingent(entry.id)


def _propagate_proved(ledger: LemmaLedger, cwd: Path):
    """Re-check contingent entries — mark proved if sorry-free."""
    tools = get_lean_tools()
    changed = True
    while changed:
        changed = False
        for e in ledger.entries():
            if e.status != LemmaStatus.CONTINGENT:
                continue
            if not (cwd / e.file_path).exists():
                continue
            if tools.has_sorry(e.file_path):
                continue
            cr = tools.check_compiles(e.file_path)
            if cr.success and not cr.has_sorry:
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
            if cr.success and not cr.has_sorry:
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


def _get_protected_names(tools, stub_rel, entry) -> set[str]:
    split = tools.split_theorems(stub_rel)
    protected = {entry.name}
    for block in split.blocks:
        if block.name == entry.name and block.mutual_group is not None:
            protected = set(split.mutual_groups.get(block.mutual_group, [entry.name]))
            break
    return protected


def _format_progress(prev: int | None, current: int) -> str:
    if prev is None:
        return f"Sorry count: {current}."
    if current < prev:
        return f"PROGRESS: sorry {prev} → {current}."
    elif current == prev:
        return f"NO REDUCTION: still {current} sorry."
    return f"Sorry count: {current} (was {prev})."


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
    tools = get_lean_tools()
    module_to_id = {}
    for e in ledger.entries():
        module = e.file_path.replace("/", ".").removesuffix(".lean")
        module_to_id[module] = e.id

    existing_edges = set()
    for e in ledger.entries():
        for cid in e.children:
            existing_edges.add((e.id, cid))

    for e in ledger.entries():
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
