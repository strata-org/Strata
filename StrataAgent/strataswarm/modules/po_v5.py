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

import json
import re
import shutil
import time as _time
from dataclasses import dataclass, field
from enum import Enum
from pathlib import Path
from typing import Any, TypeVar

from .po_agents import verified_loop, run_splitter
from .po_lean import get_lean_tools, MoveSession
from .po_util import setup_child_workspace
from .lemma_ledger import LemmaLedger, LemmaEntry, LemmaStatus
from .cycle_detection import detect, MatchType
from .verifiers.proof_writer_verifier import make_proof_writer_verifier
from .._helpers import swarm_agent
from .._lean_tools_mcp import create_extractor_mcp_server

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


@dataclass
class PO5State:
    root_workspace: str = ""
    root_theorem_name: str = ""
    root_theorem_file: str = ""
    root_id: str = ""
    stage: str = "init"
    current_lemma_id: str = ""
    skip_soundness: bool = False
    agent_registry: dict = field(default_factory=dict)
    lemma_ctx: dict = field(default_factory=dict)  # lemma_id → LemmaContext
    total_attempts: int = 0
    lemmas_proved: int = 0
    cycles_detected: int = 0


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
                                 task: str | None = None) -> tuple[str, str]:
    """Send a prompt + force a structured decision. Returns (choice, reason).

    Same task resolution as _consult_guide_raw.
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
        f"REASON: <one sentence>"
    )
    result = await guide.run_ai(inp=prompt)
    raw = result.raw_result or ""

    pattern = "|".join(re.escape(o) for o in options)
    match = re.search(rf'DECISION:\s*({pattern})', raw, re.IGNORECASE)
    reason_match = re.search(r'REASON:\s*(.+)', raw)

    decision = match.group(1).lower() if match else options[0]
    reason = reason_match.group(1).strip() if reason_match else raw[:100]
    return decision, reason


async def _dump_guide_to_disk(agent, state: PO5State, ledger: LemmaLedger,
                               entry: LemmaEntry, cwd: Path):
    """Ask guide to summarize state → write .md → destroy guide+writer."""
    guide = await _get_guide(agent, entry, state, ledger)
    result = await guide.run_ai(
        inp=(
            "DUMP YOUR STATE: Summarize everything you know about this proof.\n"
            "Include: strategies tried + outcomes, key insights, what to try next.\n"
            "Be concise but complete. This will be your memory for next session."
        ),
        max_turns=3,
    )
    state_text = result.raw_result or ""
    if state_text.strip():
        guide_dir = cwd / entry.workspace / "guide_state"
        guide_dir.mkdir(parents=True, exist_ok=True)
        (guide_dir / f"{entry.name}.md").write_text(state_text)
    await _cleanup_agents(agent, entry)


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
        theorem_name = inp.get("theorem_name", "")
        theorem_file = inp.get("theorem_file", "")
        skip_soundness = inp.get("skip_soundness", False)
    else:
        workspace_rel = str(inp) if inp else ""
        theorem_name, theorem_file = "", ""
        skip_soundness = False

    if not workspace_rel:
        return AgentResult(name=agent.spec.name, status=AgentStatus.FAILED,
                           output={"phase": "failed", "error": "no workspace"})

    state = _load_state(cwd, workspace_rel)
    if not state:
        state = PO5State(
            root_workspace=workspace_rel,
            root_theorem_name=theorem_name,
            root_theorem_file=theorem_file,
            skip_soundness=skip_soundness,
        )

    ledger = LemmaLedger(cwd / workspace_rel / "lemma_ledger.json")
    agent._workflow_state = state

    await agent._emit("message", f"[PO5] Starting: {theorem_name} in {workspace_rel} (phase={state.stage})")

    # ─── INIT ─────────────────────────────────────────────────────────────
    if state.stage == "init":
        await agent._emit("message", "[PO5] Phase: INIT")
        stub_rel = f"{workspace_rel}/Stub.lean"

        if not (cwd / workspace_rel / "Stub" / "Def.lean").exists():
            await run_splitter(agent, workspace_rel, stub_rel)

        stub_clean = cwd / workspace_rel / "Stub.clean.lean"
        if not stub_clean.exists():
            shutil.copy2(cwd / stub_rel, stub_clean)

        cheat_src = cwd / "StrataAgent" / "strataswarm" / "agent_specs" / "StrataProofCheatSheet.md"
        cheat_dst = cwd / workspace_rel / "StrataProofCheatSheet.md"
        if cheat_src.exists() and not cheat_dst.exists():
            shutil.copy2(cheat_src, cheat_dst)

        tools = get_lean_tools()
        split = tools.split_theorems(stub_rel)
        if not split.blocks:
            state.stage = "failed"
            _save_state(cwd, state)
            return AgentResult(name=agent.spec.name, status=AgentStatus.FAILED,
                               output={"phase": "failed", "error": "no theorems in Stub.lean"})

        root_block = split.blocks[-1]
        if not state.root_theorem_name:
            state.root_theorem_name = root_block.name

        if state.root_theorem_name and "'" in state.root_theorem_name:
            m = re.search(r"'([^']+)'", state.root_theorem_name)
            if m:
                state.root_theorem_name = m.group(1)

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
        decision, reason = await _consult_guide_decide(
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
    original_content = (cwd / stub_rel).read_text()

    # Fresh guide if requested
    if ctx.needs_fresh_guide:
        await _dump_guide_to_disk(agent, state, ledger, entry, cwd)
        ctx.needs_fresh_guide = False

    writer = await _get_writer(agent, entry, state, ledger)
    verify_fn = _make_verifier(entry, stub_rel, original_content, ledger, cwd)
    protected_names = _get_protected_names(tools, stub_rel, entry)

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
                f"Read the cheat sheet, then advise on the best approach."
            ))

    # ── Step 2: Main loop ──
    total_turns = 0
    prev_sorry_count = None
    chunk_budget = CHUNK_TURNS

    while True:
        ledger.increment_attempts(entry.id)
        elapsed = _time.time() - getattr(agent, '_po4_start_time', _time.time())
        writer_pct = await writer.get_context_percentage()
        guide = await _get_guide(agent, entry, state, ledger)
        guide_pct = await guide.get_context_percentage()
        await agent._emit("message",
            f"[PO5] Chunk {entry.attempts} ({chunk_budget}t, total={total_turns}) "
            f"[{elapsed/60:.1f}min] | writer: {writer_pct or 0:.0f}% | guide: {guide_pct or 0:.0f}%")

        if guide_pct and guide_pct >= 75.0:
            await _dump_guide_to_disk(agent, state, ledger, entry, cwd)
            ctx.needs_fresh_guide = True  # just dumped, will recreate on next _get_guide

        # Writer works
        chunk = min(MAX_CHUNK_TURNS, max(MIN_CHUNK_TURNS, chunk_budget))
        await verified_loop(
            agent_ctx=writer,
            initial_input=(
                f"STRATEGY ADVICE from your proof guide:\n{advice}\n\n"
                f"You have {chunk} turns. File MUST compile (sorry allowed)."
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
                ledger.mark_contingent(entry.id)
                return "has_sorry"

        # Gather state
        sorry_info = tools.get_sorries_by_theorem(stub_rel)
        sorry_count = sum(len(v) for v in sorry_info.values())
        progress = _format_progress(prev_sorry_count, sorry_count)
        prev_sorry_count = sorry_count
        writer_pct = await writer.get_context_percentage()

        # Guide reviews → next advice
        await agent._emit("message", f"[PO5] Guide reviews: {progress}")
        advice = await _consult_guide_raw(agent, state, ledger, entry, cwd,
            task=(
                f"Writer completed chunk {entry.attempts} ({total_turns} total turns).\n"
                f"Writer context: {writer_pct or 0:.0f}%\n"
                f"{progress}\nFile: {stub_rel}\nSorries: {sorry_info}\n"
                f"Diagnose and advise what to try next."
            ))

        # Guide decides
        decision, reason = await _consult_guide_decide(
            agent, state, ledger, entry, cwd,
            options=["continue", "decompose", "fresh_start", "give_up"],
            task=(
                f"Writer context: {writer_pct or 0:.0f}%\n"
                f"- continue: Keep trying in this file.\n"
                f"- decompose: Needs helpers in separate files (only if writer ≥ 65%).\n"
                f"- fresh_start: Current approach exhausted, start over.\n"
                f"- give_up: Statement is false.\n"
                f"If continue: include turns ({MIN_CHUNK_TURNS}-{MAX_CHUNK_TURNS}) in REASON."
            ))

        if decision == "give_up":
            await agent._emit("message", f"[PO5] Guide gives up: {reason}")
            ctx.failure_context = f"Guide gave up: {reason}"
            ledger.mark_failed(entry.id, f"Guide gave up: {reason}")
            _propagate_failure_to_parent(state, ledger, entry, f"Child '{entry.name}' gave up: {reason}")
            return "failed"
        elif decision == "fresh_start":
            await agent._emit("message", f"[PO5] Fresh start: {reason}")
            ctx.needs_fresh_guide = True
            ctx.failure_context = f"Previous approach exhausted: {reason}"
            ctx.current_task = ""
            return "retry"
        elif decision == "decompose":
            await agent._emit("message", f"[PO5] Decompose: {reason}")
            guide = await _get_guide(agent, entry, state, ledger)
            await _dump_guide_to_disk(agent, state, ledger, entry, cwd)
            break
        else:
            turns_match = re.search(r'(\d+)', reason)
            if turns_match:
                chunk_budget = max(MIN_CHUNK_TURNS, min(MAX_CHUNK_TURNS, int(turns_match.group(1))))

    # ── Max depth: no extraction ──
    if entry.depth >= MAX_DEPTH:
        return await _prove_at_max_depth(agent, state, ledger, entry, cwd,
                                          tools, stub_rel)

    # ── Grace phase: factor sorry into external helpers ──
    return await _grace_phase(agent, state, ledger, entry, cwd,
                               writer, verify_fn, tools, stub_rel, protected_names)


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
            f"Read the file and the cheat sheet. Advise on the best approach."
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
                ledger.mark_contingent(entry.id)
                return "has_sorry"

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
        decision, reason = await _consult_guide_decide(
            agent, state, ledger, entry, cwd,
            options=["continue", "fresh_start", "give_up"],
            task=(
                f"Writer context: {writer_pct or 0:.0f}%\n"
                f"- continue: Keep trying.\n"
                f"- fresh_start: Current approach exhausted, try new strategy.\n"
                f"- give_up: Cannot be proved.\n"
                f"If continue: include turns ({MIN_CHUNK_TURNS}-{MAX_CHUNK_TURNS}) in REASON."
            ))

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
            turns_match = re.search(r'(\d+)', reason)
            if turns_match:
                chunk_budget = max(MIN_CHUNK_TURNS, min(MAX_CHUNK_TURNS, int(turns_match.group(1))))



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
                f"Factor each into a standalone helper with sorry, use `exact helper ...`.\n"
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
                ledger.mark_contingent(entry.id)
                return "has_sorry"

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
    extractable = [b for b in split.blocks
                   if b.name not in protected_names and b.mutual_group is None]

    do_not_move = ""
    if len(protected_names) > 1:
        do_not_move = f"\nDo NOT move: {sorted(protected_names)} (mutual block).\n"

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
            verify=lambda: _verify_extraction(tools, stub_rel, entry),
            max_rounds=3, max_turns=30, use_run_ai=False,
        )

    if not outcome.success:
        session.revert()
        decision, reason = await _consult_guide_decide(
            agent, state, ledger, entry, cwd,
            options=["retry", "give_up"],
            task="Extraction failed (file didn't compile after moves). Retry or give up?")
        if decision == "give_up":
            ctx.failure_context = f"Extraction failed, gave up: {reason}"
            ledger.mark_failed(entry.id, f"Extraction failed, gave up: {reason}")
            _propagate_failure_to_parent(state, ledger, entry, f"Child '{entry.name}' extraction failed: {reason}")
            return Trans.CONTRADICTORY
        ctx.failure_context = f"Extraction failed: {reason}"
        ctx.current_task = "Re-prove with a different factoring strategy."
        return Trans.RETRY

    session.finalize()
    new_files = sorted(new_decomp_dir.glob("lemma_helper_*.lean")) if new_decomp_dir.exists() else []
    await agent._emit("message", f"[PO5] Extraction done: {len(new_files)} files staged")

    if not new_files:
        return Trans.EXTRACTED

    # Guide reviews decomposition
    file_list = "\n".join(f"  - {f.stem}" for f in new_files)
    decision, reason = await _consult_guide_decide(
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

        decision, reason = await _consult_guide_decide(
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
        decision, reason = await _consult_guide_decide(
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
        decision, reason = await _consult_guide_decide(
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
            decision, reason = await _consult_guide_decide(
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

async def _get_guide(agent, entry: LemmaEntry, state: PO5State, ledger: LemmaLedger):
    """Get or create persistent guide for this lemma. Reads .md on creation."""
    from .._ledger_mcp import create_ledger_mcp_server
    attr = f"_guide_{entry.id}"
    if getattr(agent, attr, None) is None:
        cwd = Path(agent._cwd) if agent._cwd else Path.cwd()
        cheat_rel = f"{entry.workspace}/StrataProofCheatSheet.md"
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

        # Inject prior state
        guide_state_path = cwd / entry.workspace / "guide_state" / f"{entry.name}.md"
        if guide_state_path.exists():
            prior = guide_state_path.read_text()
            await internal.run_ai(
                inp=f"PRIOR SESSION STATE:\n\n{prior}\n\nAcknowledge briefly — do NOT start proving yet.")

    return getattr(agent, attr)


async def _get_writer(agent, entry: LemmaEntry, state: PO5State, ledger: LemmaLedger):
    """Get or create persistent writer (proof_writer_v2) for this lemma."""
    from .._lean_tools_mcp import create_writer_import_server
    attr = f"_writer_{entry.id}"
    if getattr(agent, attr, None) is None:
        tools = get_lean_tools()
        import_mcp = create_writer_import_server(tools, entry.workspace)
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
    return getattr(agent, attr)


async def _get_proof_closer(agent, entry: LemmaEntry, state: PO5State, ledger: LemmaLedger):
    """Get or create proof_closer for this lemma. Used at max depth — no sorry allowed."""
    from .._lean_tools_mcp import create_writer_import_server
    attr = f"_closer_{entry.id}"
    if getattr(agent, attr, None) is None:
        tools = get_lean_tools()
        import_mcp = create_writer_import_server(tools, entry.workspace)
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
    return getattr(agent, attr)


async def _cleanup_agents(agent, entry: LemmaEntry):
    """Destroy guide + writer + closer for this lemma."""
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
        setup_child_workspace(cwd, entry.file_path, state.root_workspace)
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


def _verify_extraction(tools, stub_rel: str, entry: LemmaEntry) -> str | None:
    cr = tools.check_compiles(stub_rel)
    if not cr.success:
        return "Stub.lean doesn't compile after extraction"
    split = tools.split_theorems(stub_rel)
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
    state_dir = cwd / "strataswarm" / "temp"
    state_dir.mkdir(parents=True, exist_ok=True)
    data = {
        "root_workspace": state.root_workspace,
        "root_theorem_name": state.root_theorem_name,
        "root_id": state.root_id,
        "stage": state.stage,
        "current_lemma_id": state.current_lemma_id,
        "total_attempts": state.total_attempts,
        "lemmas_proved": state.lemmas_proved,
        "cycles_detected": state.cycles_detected,
    }
    (state_dir / "po5_state.yaml").write_text(
        __import__("yaml").dump(data, default_flow_style=False))


def _load_state(cwd: Path, workspace_rel: str) -> PO5State | None:
    import yaml
    state_file = cwd / "strataswarm" / "temp" / "po5_state.yaml"
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
