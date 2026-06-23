"""Proof Orchestrator v4: Single-PO worklist with Lemma Ledger.

Architecture:
  One PO manages a flat global worklist of all proof obligations.
  Picks the most impactful lemma, attempts to prove it, decomposes if needed,
  detects cycles/reuse, and context-switches between lemmas based on priority.

Key differences from v3:
  - No recursive child POs — single orchestrator manages everything
  - Per-lemma persistent (writer, guide) pairs
  - Cycle detection after every decomposition
  - Priority-based lemma selection (indegree-driven)
  - Assembly only after ALL lemmas proved (DAG fully colored)
"""

from __future__ import annotations

import json
import shutil
from dataclasses import dataclass, field, asdict
from enum import Enum
from pathlib import Path
from typing import Any, TypeVar

from .po_agents import verified_loop, run_splitter, run_cea
from .po_lean import get_lean_tools, MoveSession
from .po_util import write_checkpoint as _write_checkpoint_v3, setup_child_workspace
from .lemma_ledger import LemmaLedger, LemmaEntry, LemmaStatus
from .cycle_detection import detect, MatchType
from .verifiers.proof_writer_verifier import make_proof_writer_verifier
from .._helpers import swarm_agent
from .._lean_tools_mcp import create_extractor_mcp_server

T = TypeVar("T")

MAX_DEPTH = 3


# ─── Guide verdict (structured output for stall decisions) ───────────────────

class GuideAction(str, Enum):
    CONTINUE = "continue"    # keep trying, theorem is provable in-file
    DECOMPOSE = "decompose"  # needs helper lemmas extracted into separate files
    GIVE_UP = "give_up"      # statement itself is mathematically false


@dataclass
class GuideVerdict:
    action: GuideAction = GuideAction.CONTINUE
    reason: str = ""
    turns: int = 35  # how many turns to give writer next (10-50)


# ─── State machine (for gen_mermaid.py + frontend visualization) ──────────────
#
# stateDiagram-v2
#     [*] --> init
#     init --> select : registered
#     init --> failed : blocked
#     select --> prove : picked
#     select --> failed : blocked
#     prove --> update : proved / contradictory
#     prove --> extract : has_sorry
#     extract --> detect : extracted
#     extract --> update : extract_failed
#     detect --> update : cycle_found / no_cycle
#     update --> check : checked
#     check --> assembling : all_proved
#     check --> select : has_pending
#     check --> failed : blocked
#     assembling --> done : assembled
#     assembling --> failed : assembly_failed
#
# Phases:
#   init    — register root in ledger, split Stub/Def
#   select  — pick most pressing pending lemma (highest indegree)
#   prove   — attempt proof with guide + writer (phase 1: direct, phase 2: grace/factor)
#   extract — MoveSession + decl_extractor → decomposed/lemma_helper_*.lean files
#   detect  — run cycle detection on each helper (fast hash + soft agent + hard Lean)
#   update  — apply verdicts to DAG (3 passes):
#             1. Register entries / mark CYCLE / mark REUSE
#             2. Propagate cycles up to ancestor (mark chain as CYCLE)
#             3. Prune siblings of dead nodes, re-activate parents
#   check   — read-only: all_proved → assemble, has_pending → select, else → failed
#   assembling — all proved, mechanical import rewriting + lake build
#   done/failed — terminal
#

class Phase(str, Enum):
    INIT = "init"
    SELECT = "select"        # pick most pressing lemma from DAG
    PROVE = "prove"          # attempt proof with guide + writer
    EXTRACT = "extract"      # decompose into helpers
    DETECT = "detect"        # run cycle detection on new helpers
    UPDATE = "update"        # update ledger + DAG, prune if needed
    CHECK = "check"          # check DAG: all proved? anything pending?
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
    EXTRACT_FAILED = "extract_failed"
    CHECKED = "checked"
    CYCLE_FOUND = "cycle_found"
    NO_CYCLE = "no_cycle"
    ALL_PROVED = "all_proved"
    HAS_PENDING = "has_pending"
    BLOCKED = "blocked"
    ASSEMBLED = "assembled"
    ASSEMBLY_FAILED = "assembly_failed"


TRANSITIONS: dict[tuple[str, str], str] = {
    (Phase.INIT, Trans.REGISTERED):        Phase.SELECT,
    (Phase.INIT, Trans.BLOCKED):           Phase.FAILED,

    (Phase.SELECT, Trans.PICKED):          Phase.PROVE,
    (Phase.SELECT, Trans.BLOCKED):         Phase.FAILED,

    (Phase.PROVE, Trans.PROVED):           Phase.UPDATE,
    (Phase.PROVE, Trans.HAS_SORRY):        Phase.EXTRACT,
    (Phase.PROVE, Trans.CONTRADICTORY):    Phase.UPDATE,

    (Phase.EXTRACT, Trans.EXTRACTED):      Phase.DETECT,
    (Phase.EXTRACT, Trans.EXTRACT_FAILED): Phase.UPDATE,

    (Phase.DETECT, Trans.CYCLE_FOUND):     Phase.UPDATE,
    (Phase.DETECT, Trans.NO_CYCLE):        Phase.UPDATE,

    (Phase.UPDATE, Trans.CHECKED):         Phase.CHECK,

    (Phase.CHECK, Trans.ALL_PROVED):       Phase.ASSEMBLING,
    (Phase.CHECK, Trans.HAS_PENDING):      Phase.SELECT,
    (Phase.CHECK, Trans.BLOCKED):          Phase.FAILED,

    (Phase.ASSEMBLING, Trans.ASSEMBLED):   Phase.DONE,
    (Phase.ASSEMBLING, Trans.ASSEMBLY_FAILED): Phase.FAILED,
}


# ─── State ────────────────────────────────────────────────────────────────────

@dataclass
class PO4State:
    root_workspace: str = ""
    root_theorem_name: str = ""
    root_theorem_file: str = ""
    root_id: str = ""
    stage: str = "init"  # init | proving | assembling | done | failed
    current_lemma_id: str = ""
    skip_soundness: bool = False
    agent_registry: dict = field(default_factory=dict)  # lemma_id → {writer, guide}
    total_attempts: int = 0
    lemmas_proved: int = 0
    cycles_detected: int = 0


# ─── Main entry point ─────────────────────────────────────────────────────────

async def run_workflow(agent, inp: Any, result_type: type[T] | None = None):
    import time as _time
    from .._types import AgentResult, AgentStatus

    _start_time = _time.time()
    await agent._emit("status_change", "running")
    agent._po4_start_time = _start_time

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

    # Load or create state
    state = _load_state(cwd, workspace_rel)
    if not state:
        state = PO4State(
            root_workspace=workspace_rel,
            root_theorem_name=theorem_name,
            root_theorem_file=theorem_file,
            skip_soundness=skip_soundness,
        )

    # Load or create ledger
    ledger = LemmaLedger(cwd / workspace_rel / "lemma_ledger.json")
    agent._workflow_state = state

    await agent._emit("message", f"[PO4] Starting: {theorem_name} in {workspace_rel} (phase={state.stage})")

    # ─── Phase: INIT ──────────────────────────────────────────────────────
    if state.stage == "init":
        await agent._emit("message", "[PO4] Phase: INIT")

        # Ensure Stub/Def split
        stub_rel = f"{workspace_rel}/Stub.lean"
        if not (cwd / workspace_rel / "Stub" / "Def.lean").exists():
            await run_splitter(agent, workspace_rel, stub_rel)

        # Create clean backup for retry restoration
        stub_clean = cwd / workspace_rel / "Stub.clean.lean"
        if not stub_clean.exists():
            shutil.copy2(cwd / stub_rel, stub_clean)

        # Copy cheat sheet into workspace for guide access
        cheat_src = cwd / "StrataAgent" / "strataswarm" / "agent_specs" / "StrataProofCheatSheet.md"
        cheat_dst = cwd / workspace_rel / "StrataProofCheatSheet.md"
        if cheat_src.exists() and not cheat_dst.exists():
            shutil.copy2(cheat_src, cheat_dst)

        # Register root in ledger
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

        # Clean up theorem name (TM sometimes passes "Theorems: ['name']" format)
        import re as _re
        if state.root_theorem_name and "'" in state.root_theorem_name:
            _match = _re.search(r"'([^']+)'", state.root_theorem_name)
            if _match:
                state.root_theorem_name = _match.group(1)

        sig_hash = LemmaLedger.compute_signature_hash(root_block.text)
        root_entry = ledger.add_lemma(
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

    # Reset any PROVING entries to PENDING (handles crash recovery)
    for e in ledger.entries():
        if e.status == LemmaStatus.PROVING:
            e.status = LemmaStatus.PENDING

    # Handler registry: each handler returns a Trans value
    HANDLERS = {
        Phase.SELECT:     lambda: _do_select(agent, state, ledger),
        Phase.PROVE:      lambda: _do_prove(agent, state, ledger, cwd),
        Phase.EXTRACT:    lambda: _do_extract_phase(agent, state, ledger, cwd),
        Phase.DETECT:     lambda: _do_detect_phase(agent, state, ledger, cwd),
        Phase.UPDATE:     lambda: _do_update_phase(agent, state, ledger, cwd),
        Phase.CHECK:      lambda: _do_check(agent, state, ledger),
        Phase.ASSEMBLING: lambda: _do_assemble_phase(agent, state, ledger, cwd),
    }

    # ─── Main state machine loop ─────────────────────────────────────────
    while state.stage not in ("done", "failed") and not agent.cancellation.is_cancelled:
        try:
            phase = Phase(state.stage)
        except ValueError:
            await agent._emit("message", f"[PO4] ERROR: invalid stage '{state.stage}'")
            state.stage = "failed"
            break

        handler = HANDLERS.get(phase)
        if not handler:
            state.stage = "failed"
            break

        transition = await handler()
        next_stage = TRANSITIONS.get((phase, transition))
        if next_stage is None:
            await agent._emit("message", f"[PO4] ERROR: no transition from {state.stage} via {transition.value}")
            state.stage = "failed"
            break

        await agent._emit("state_transition", {
            "from": state.stage, "transition": transition.value, "to": next_stage.value})
        state.stage = next_stage.value

        ledger.save()
        _write_progress(cwd, state, ledger)
        _save_state(cwd, state)

    # ─── Done ─────────────────────────────────────────────────────────────
    elapsed = _time.time() - _start_time
    elapsed_str = f"{elapsed/60:.1f}min" if elapsed >= 60 else f"{elapsed:.0f}s"
    total_cost = getattr(agent.swarm, '_total_cost', 0.0) if hasattr(agent, 'swarm') else 0.0
    await agent._emit("message",
        f"[PO4] Finished: stage={state.stage}, proved={state.lemmas_proved}, "
        f"cycles={state.cycles_detected}, time={elapsed_str}, cost=${total_cost:.2f}")
    ledger.save()

    # Write session summary to the session folder for replay/reporting
    _write_session_summary(cwd, state, ledger, elapsed, total_cost)

    status = AgentStatus.COMPLETED if state.stage == "done" else AgentStatus.FAILED
    return AgentResult(name=agent.spec.name, status=status,
                       output={"stage": state.stage, "proved": state.lemmas_proved,
                               "cycles": state.cycles_detected, "time_seconds": round(elapsed),
                               "cost_usd": round(total_cost, 4)})


# ─── Phase handlers (each returns a Trans value) ─────────────────────────────

async def _do_select(agent, state: PO4State, ledger: LemmaLedger) -> Trans:
    """DFS selection: ask the parent's guide to pick among its PENDING children.

    Flow:
    1. Find the nearest ancestor (starting from current) that has PENDING children
    2. If only one child → pick it directly (no agent call needed)
    3. If multiple → ask that ancestor's guide which child is hardest/most general
    4. Fallback to mechanical pick_next() if guide can't decide
    """
    if not ledger.has_pending():
        return Trans.BLOCKED

    # Find nearest ancestor with PENDING children (DFS: stay in current subtree)
    parent_entry, pending_kids = _find_dfs_candidates(ledger, state.current_lemma_id)

    if not pending_kids:
        # Nothing in current subtree — fall back to mechanical
        lemma = ledger.pick_next()
        if lemma is None:
            return Trans.BLOCKED
        state.current_lemma_id = lemma.id
        ledger.mark_proving(lemma.id)
        await agent._emit("message",
            f"[PO4] Selected (fallback): {lemma.name} (depth={lemma.depth})")
        return Trans.PICKED

    # Single child — no need to ask
    if len(pending_kids) == 1:
        winner = pending_kids[0]
        state.current_lemma_id = winner.id
        ledger.mark_proving(winner.id)
        await agent._emit("message",
            f"[PO4] Selected (only child): {winner.name} (depth={winner.depth})")
        return Trans.PICKED

    # Multiple children — ask parent's guide which is hardest
    selected = await _guide_pick_child(agent, state, ledger, parent_entry, pending_kids)
    if selected:
        state.current_lemma_id = selected.id
        ledger.mark_proving(selected.id)
        await agent._emit("message",
            f"[PO4] Guide selected: {selected.name} (depth={selected.depth}, "
            f"indegree={ledger.indegree(selected.id)})")
        return Trans.PICKED

    # Guide failed — pick first by depth (deepest = continue DFS)
    pending_kids.sort(key=lambda e: (e.depth, -e.attempts), reverse=True)
    winner = pending_kids[0]
    state.current_lemma_id = winner.id
    ledger.mark_proving(winner.id)
    await agent._emit("message",
        f"[PO4] Selected (depth fallback): {winner.name} (depth={winner.depth})")
    return Trans.PICKED


def _find_dfs_candidates(
    ledger: LemmaLedger, start_id: str
) -> tuple[LemmaEntry | None, list[LemmaEntry]]:
    """Walk up from start_id to find nearest ancestor with PENDING children.

    Returns (parent_entry, pending_children). DFS: we stay in the current
    subtree as long as there's work there.
    """
    if not start_id:
        pending = [e for e in ledger.entries() if e.status == LemmaStatus.PENDING]
        return (None, pending[:8])

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

    # Nothing in ancestry — return all pending
    pending = [e for e in ledger.entries() if e.status == LemmaStatus.PENDING]
    return (None, pending[:8])


async def _guide_pick_child(
    agent, state: PO4State, ledger: LemmaLedger,
    parent_entry: LemmaEntry | None, candidates: list[LemmaEntry]
) -> LemmaEntry | None:
    """Ask the parent's guide to pick the hardest/most general child."""
    import re

    if not parent_entry:
        return None

    guide = await _get_guide(agent, parent_entry, state, ledger)

    children_desc = ""
    for i, c in enumerate(candidates):
        snippet = (c.statement or "")[:150].replace("\n", " ")
        children_desc += f"  {i+1}. ID={c.id} | {c.name} | depth={c.depth} | {snippet}\n"

    prompt = (
        f"Your lemma '{parent_entry.name}' was decomposed into sub-lemmas.\n"
        f"These children are PENDING (not yet attempted):\n"
        f"{children_desc}\n"
        f"Which one should we prove NEXT?\n\n"
        f"Pick the MOST GENERAL / HARDEST one — it will likely produce reusable "
        f"sub-results that help prove the others. The easier/more specific ones "
        f"can often be closed trivially once the hard one is done.\n\n"
        f"Consider:\n"
        f"- Which has the most complex conclusion type?\n"
        f"- Which involves recursion or induction?\n"
        f"- Which is most likely to need further decomposition?\n\n"
        f"Reply with: PICK: <id>"
    )

    result = await guide.run_ai(inp=prompt)
    raw = result.raw_result or ""

    match = re.search(r'PICK:\s*([a-f0-9]+)', raw)
    if match:
        picked_id = match.group(1)
        for c in candidates:
            if c.id == picked_id or c.id.startswith(picked_id):
                return c

    return None


async def _do_prove(agent, state: PO4State, ledger: LemmaLedger, cwd: Path) -> Trans:
    """Attempt proof of selected lemma."""
    lemma = ledger.get(state.current_lemma_id)
    result = await _attempt_prove(agent, state, ledger, lemma, cwd)
    state.total_attempts += 1

    if result == "proved":
        state.lemmas_proved += 1
        return Trans.PROVED
    elif result == "has_sorry":
        return Trans.HAS_SORRY
    elif result == "contradictory":
        ledger.mark_failed(lemma.id, "contradictory")
        return Trans.CONTRADICTORY
    else:
        if lemma.status != LemmaStatus.FAILED:
            ledger.mark_failed(lemma.id, result)
        return Trans.CONTRADICTORY


async def _do_extract_phase(agent, state: PO4State, ledger: LemmaLedger, cwd: Path) -> Trans:
    """Run extraction (MoveSession + decl_extractor)."""
    lemma = ledger.get(state.current_lemma_id)
    result = await _do_extract(agent, state, ledger, lemma, cwd)
    if result == "extracted":
        return Trans.EXTRACTED
    ledger.mark_failed(lemma.id, "extraction failed")
    return Trans.EXTRACT_FAILED


async def _do_detect_phase(agent, state: PO4State, ledger: LemmaLedger, cwd: Path) -> Trans:
    """Run cycle detection on extracted helpers."""
    lemma = ledger.get(state.current_lemma_id)
    result = await _do_detect(agent, state, ledger, lemma, cwd)
    if result == "rejected":
        # Decomposition identical to previous failed one — mark failed, guide retries
        ledger.mark_failed(lemma.id, "Decomposition rejected: identical to previously failed attempt")
        return Trans.EXTRACT_FAILED
    return Trans.CYCLE_FOUND if result == "cycle_found" else Trans.NO_CYCLE


async def _do_update_phase(agent, state: PO4State, ledger: LemmaLedger, cwd: Path) -> Trans:
    """Apply verdicts to ledger, prune siblings of dead nodes, assemble proved."""
    lemma = ledger.get(state.current_lemma_id)
    _do_update(state, ledger, lemma, cwd)

    # Assemble any newly proved entries (copy Stub.lean → .lean)
    proved_entries = [e for e in ledger.entries() if e.status == LemmaStatus.PROVED]
    if proved_entries:
        await _assemble(agent, state, ledger, cwd)

    return Trans.CHECKED


async def _do_check(agent, state: PO4State, ledger: LemmaLedger) -> Trans:
    """Read-only inspection: all proved? pending? blocked?"""
    if ledger.all_proved():
        return Trans.ALL_PROVED
    elif ledger.pick_next() is not None:
        return Trans.HAS_PENDING
    else:
        return Trans.BLOCKED


async def _do_assemble_phase(agent, state: PO4State, ledger: LemmaLedger, cwd: Path) -> Trans:
    """Bottom-up topological assembly."""
    await agent._emit("message", "[PO4] Assembling...")
    success = await _assemble(agent, state, ledger, cwd)
    return Trans.ASSEMBLED if success else Trans.ASSEMBLY_FAILED




# ─── Prove a single lemma ─────────────────────────────────────────────────────

CHUNK_TURNS = 35           # default turns per writer chunk
MIN_CHUNK_TURNS = 20       # minimum turns guide can assign
MAX_CHUNK_TURNS = 100      # maximum turns guide can assign
CONTEXT_THRESHOLD = 65.0   # % — guide can recommend decompose after this
GRACE_TURNS = 20           # turns per grace extraction attempt
WRITER_CLEANUP_TURNS = 10


async def _attempt_prove(agent, state: PO4State, ledger: LemmaLedger,
                         entry: LemmaEntry, cwd: Path) -> str:
    """Attempt to prove a single lemma.

    Simple loop: guide advises → writer works → guide reviews → repeat.
    Exits when: proved, guide says decompose, or guide says give_up.

    Returns: 'proved' | 'has_sorry' | 'failed'
    """
    tools = get_lean_tools()
    stub_rel = f"{entry.workspace}/Stub.lean" if "/Stub.lean" not in entry.file_path else entry.file_path

    # Ensure workspace exists
    if not (cwd / stub_rel).exists():
        setup_child_workspace(cwd, entry.file_path, state.root_workspace)
        stub_rel = f"{entry.workspace}/Stub.lean"
        if not (cwd / stub_rel).exists():
            stub_rel = entry.file_path

    original_content = (cwd / stub_rel).read_text()

    # Get or create writer + guide
    writer = await _get_writer(agent, entry, state, ledger)
    guide = await _get_guide(agent, entry, state, ledger)

    # Build verifier
    ancestor_modules = []
    for anc_id in ledger.get_ancestry(entry.id):
        anc = ledger.get(anc_id)
        if anc:
            ancestor_modules.append(anc.workspace.replace("/", "."))

    verify_fn = make_proof_writer_verifier(
        stub_rel, original_content, entry.workspace, entry.name,
        ancestor_modules=ancestor_modules)

    # Detect mutual block membership
    init_split = tools.split_theorems(stub_rel)
    protected_names = {entry.name}
    for block in init_split.blocks:
        if block.name == entry.name and block.mutual_group is not None:
            protected_names = set(init_split.mutual_groups.get(block.mutual_group, [entry.name]))
            break

    # ── Main loop: guide ↔ writer ──
    total_turns_used = 0
    prev_sorry_count = None
    chunk_budget = CHUNK_TURNS  # guide can adjust this (10-50) each cycle
    guide_state_file = cwd / entry.workspace / "guide_state" / f"{entry.name}.md"

    # Initial guide consultation
    ledger_summary = _build_ledger_summary(ledger, entry)
    state_reminder = ""
    if guide_state_file.exists():
        state_reminder = (
            f"\nNOTE: Your prior state is saved at {entry.workspace}/guide_state/{entry.name}.md — "
            f"re-read it if you've lost context."
        )

    await agent._emit("message", f"[PO4] Guide: initial strategy for {entry.name}")
    initial_result = await guide.run_ai(
        inp=(
            f"CONTEXT:\n{ledger_summary}\n\n"
            f"We are about to prove theorem '{entry.name}' in {stub_rel}.\n"
            f"Read the cheat sheet, then advise on the best approach.\n"
            f"What proof technique fits? What pitfalls to avoid?"
            f"{state_reminder}"
        ),
    )
    action = _build_initial_action(entry, stub_rel, initial_result.raw_result or "", protected_names)

    while True:
        ledger.increment_attempts(entry.id)

        # Log context usage + elapsed time
        import time as _time
        elapsed = _time.time() - getattr(agent, '_po4_start_time', _time.time())
        elapsed_str = f"{elapsed/60:.1f}min" if elapsed >= 60 else f"{elapsed:.0f}s"
        writer_pct = await writer.get_context_percentage()
        guide_pct = await guide.get_context_percentage()
        pct_str = ""
        if writer_pct is not None and guide_pct is not None:
            pct_str = f" | writer: {writer_pct:.0f}% | guide: {guide_pct:.0f}%"
        await agent._emit("message",
            f"[PO4] Chunk {entry.attempts} ({chunk_budget}t, "
            f"total={total_turns_used}) [{elapsed_str}]{pct_str}")

        # Guide at 75%: dump state + compact
        if guide_pct is not None and guide_pct >= 75.0:
            await agent._emit("message", f"[PO4] Guide at {guide_pct:.0f}% — dump + compact")
            await _dump_guide_state(guide, entry, cwd)
            await guide.backend.compact()

        # ── Writer works (verified_loop ensures file compiles on exit) ──
        chunk_turns = min(MAX_CHUNK_TURNS, max(MIN_CHUNK_TURNS, chunk_budget))
        writer_instruction = (
            f"{action}\n\n"
            f"You have {chunk_turns} turns. "
            f"The file MUST compile when you hand off (sorry is allowed)."
        )
        await verified_loop(
            agent_ctx=writer,
            initial_input=writer_instruction,
            verify=verify_fn,
            max_rounds=5,
            max_turns=chunk_turns,
            use_run_ai=True,
        )
        total_turns_used += chunk_turns

        # ── Check: proved? ──
        if not tools.has_sorry(stub_rel) and tools.check_compiles(stub_rel).success:
            cr = tools.check_compiles(stub_rel)
            if cr.has_sorry:
                ledger.mark_contingent(entry.id)
                await agent._emit("message", "[PO4] Contingent: no local sorry, waiting on deps")
                return "has_sorry"
            else:
                ledger.mark_proved(entry.id, stub_rel.replace("/", ".").removesuffix(".lean"))
                return "proved"

        # ── Gather state for guide ──
        writer_pct = await writer.get_context_percentage()
        sorry_info = tools.get_sorries_by_theorem(stub_rel)
        sorry_count = sum(len(v) for v in sorry_info.values())

        progress_note = f"Sorry count: {sorry_count}."
        if prev_sorry_count is not None:
            if sorry_count < prev_sorry_count:
                progress_note = f"PROGRESS: sorry {prev_sorry_count} → {sorry_count}."
            elif sorry_count == prev_sorry_count:
                progress_note = f"NO REDUCTION: still {sorry_count} sorry."
        prev_sorry_count = sorry_count

        state_reminder = ""
        if guide_state_file.exists():
            state_reminder = (
                f"\nNOTE: Your prior state is at {entry.workspace}/guide_state/{entry.name}.md — "
                f"re-read it if you've lost context."
            )

        first_thm = next(iter(sorry_info), None)
        sorry_detail = ""
        if first_thm and sorry_info[first_thm]:
            pos = sorry_info[first_thm][0]
            sorry_detail = f"\nUse lean_goal at {stub_rel} line {pos['line']} col {pos['col']} to see a stuck goal."

        # ── Guide reviews + advises ──
        await agent._emit("message", f"[PO4] Guide reviews: {progress_note}")
        advice_result = await guide.run_ai(
            inp=(
                f"Writer completed chunk {entry.attempts} ({total_turns_used} total turns).\n"
                f"Writer context: {writer_pct:.0f}%\n"
                f"{progress_note}\n"
                f"File: {stub_rel}\n"
                f"Sorries: {sorry_info}\n"
                f"{sorry_detail}\n"
                f"Diagnose and advise what to try next."
                f"{state_reminder}"
            ),
        )
        advice = advice_result.raw_result or "Try a different approach."

        # ── Guide verdict: continue / decompose / give_up + turns budget ──
        verdict_result = await guide.run_ai(
            inp=(
                "What should happen next?\n"
                f"Writer context: {writer_pct:.0f}%\n\n"
                "- continue: Keep trying. Theorem is provable in this file.\n"
                "- decompose: Needs helper lemmas in separate files. Move to extraction.\n"
                "- give_up: Statement is mathematically false.\n\n"
                "'Needs mutual recursion' or 'needs helpers' = decompose, NOT give_up.\n"
                "Do NOT choose decompose unless writer context ≥ 65%.\n\n"
                "If continue: set 'turns' (10-50) for how many turns the writer gets next.\n"
                "More turns = writer explores deeper. Fewer = check in sooner."
            ),
            result_type=GuideVerdict,
            max_turns=1,
        )

        if verdict_result.output:
            verdict = verdict_result.output
            if verdict.action == GuideAction.GIVE_UP:
                await agent._emit("message", f"[PO4] Statement false: {verdict.reason}")
                ledger.mark_failed(entry.id, f"Statement false: {verdict.reason}")
                return "failed"
            elif verdict.action == GuideAction.DECOMPOSE:
                await agent._emit("message", f"[PO4] Decompose: {verdict.reason}")
                await _dump_guide_state(guide, entry, cwd)
                break  # → grace phase → extraction
            chunk_budget = verdict.turns

        action = f"STRATEGY ADVICE from your proof guide:\n{advice}\n\nApply this advice and continue the proof."

    # ── At max depth: no extraction, prove everything in one file ──
    if entry.depth >= MAX_DEPTH:
        await agent._emit("message",
            f"[PO4] MAX DEPTH — no extraction. Must prove all sorry in-file.")

        prev_sorry = sum(len(v) for v in tools.get_sorries_by_theorem(stub_rel).values())
        deep_attempt = 0
        while True:
            deep_attempt += 1
            turns = 50
            await agent._emit("message",
                f"[PO4] Deep attempt {deep_attempt} ({turns} turns)")

            deep_action = (
                f"You are at MAX RECURSION DEPTH. There will be NO further decomposition.\n"
                f"You MUST close ALL sorry in this file: {stub_rel}\n\n"
                f"You CAN create helper theorems within the same file (above the main theorem).\n"
                f"But ALL of them must be fully proved — no sorry anywhere.\n\n"
                f"Use induction, structural recursion, mutual recursion, or any tactic.\n"
                f"Ask SearchAgent for relevant lemmas. Use lean_goal to inspect goals.\n"
                f"The file must compile with ZERO sorry when you are done."
            )

            outcome = await verified_loop(
                agent_ctx=writer,
                initial_input=f"{deep_action}\n\nYou have {turns} turns.",
                verify=verify_fn,
                max_rounds=2,
                max_turns=turns,
                use_run_ai=True,
            )

            if not tools.has_sorry(stub_rel) and tools.check_compiles(stub_rel).success:
                cr = tools.check_compiles(stub_rel)
                if not cr.has_sorry:
                    ledger.mark_proved(entry.id, stub_rel.replace("/", ".").removesuffix(".lean"))
                    return "proved"
                else:
                    ledger.mark_contingent(entry.id)
                    return "has_sorry"

            cur_sorry = sum(len(v) for v in tools.get_sorries_by_theorem(stub_rel).values())
            if cur_sorry >= prev_sorry:
                await agent._emit("message", f"[PO4] No progress ({cur_sorry} sorry) — consulting guide")
                advice_result = await guide.run_ai(
                    inp=f"Writer stuck at max depth. File: {stub_rel}\n"
                        f"Sorry count: {cur_sorry}. Advise a different approach.",
                )
                advice = advice_result.raw_result or ""
                deep_action = f"STRATEGY ADVICE:\n{advice}\n\n{deep_action}"
                # If no progress for 3 consecutive attempts, give up
                if deep_attempt >= 10 and cur_sorry >= prev_sorry:
                    ledger.mark_failed(entry.id, f"Max depth, no progress after {deep_attempt} attempts")
                    return "failed"
            else:
                await agent._emit("message", f"[PO4] Sorry: {prev_sorry} → {cur_sorry}")
            prev_sorry = cur_sorry

    # ── Phase 2: Grace — factor remaining sorry into helpers (for extraction) ──
    #
    # Rule: the "protected block" (main theorem, or entire mutual group) must be
    # sorry-free. Only standalone helpers OUTSIDE the protected block can have sorry.
    # Those get extracted as child obligations.

    split = tools.split_theorems(stub_rel)
    # Identify the protected names: main theorem + all its mutual partners
    protected_names = {entry.name}
    for block in split.blocks:
        if block.name == entry.name and block.mutual_group is not None:
            protected_names = set(split.mutual_groups.get(block.mutual_group, [entry.name]))
            break

    sorry_info = tools.get_sorries_by_theorem(stub_rel)
    protected_sorry_count = sum(len(sorry_info.get(n, [])) for n in protected_names)

    if protected_sorry_count == 0:
        await agent._emit("message", "[PO4] Protected block sorry-free → ready to extract")
        return "has_sorry"

    is_mutual = len(protected_names) > 1
    mutual_note = ""
    if is_mutual:
        mutual_note = (
            f"\n\nIMPORTANT — MUTUAL BLOCK RULE:\n"
            f"The mutual block contains: {sorted(protected_names)}\n"
            f"ALL theorems in this mutual block must be sorry-free.\n"
            f"Helper lemmas MUST be placed OUTSIDE and ABOVE the `mutual` keyword.\n"
            f"Helpers must be standalone (not `mutual`), public, and can have sorry.\n"
            f"Do NOT put helper theorems inside the mutual...end block.\n"
        )

    await agent._emit("message",
        f"[PO4] Grace phase: {protected_sorry_count} sorry in protected block "
        f"({'mutual: ' + str(sorted(protected_names)) if is_mutual else entry.name})")

    prev_protected_sorry = protected_sorry_count
    for grace in range(max(protected_sorry_count, 3)):
        await agent._emit("message", f"[PO4] Grace {grace + 1} ({GRACE_TURNS} turns)")

        sorry_info = tools.get_sorries_by_theorem(stub_rel)
        protected_sorry_positions = {n: sorry_info.get(n, []) for n in protected_names if sorry_info.get(n)}
        grace_action = (
            f"WRAP UP — grace attempt {grace + 1}.\n\n"
            f"Remaining sorry in protected block: {protected_sorry_positions}\n\n"
            f"For each sorry you cannot close directly, factor it into a STANDALONE helper:\n"
            f"  theorem helper_<name> (<params>) : <goal_type> := by sorry\n"
            f"Then use `exact helper_<name> ...` in the proof.\n\n"
            f"The protected block ({sorted(protected_names)}) must be sorry-free when you're done.\n"
            f"Standalone helpers outside the block CAN have sorry — they will be extracted."
            f"{mutual_note}"
        )

        outcome = await verified_loop(
            agent_ctx=writer,
            initial_input=f"{grace_action}\n\nYou have {GRACE_TURNS} turns.",
            verify=verify_fn,
            max_rounds=2,
            max_turns=GRACE_TURNS,
            use_run_ai=True,
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
        current_protected_sorry = sum(len(sorry_info.get(n, [])) for n in protected_names)

        if current_protected_sorry == 0:
            await agent._emit("message", "[PO4] Protected block sorry-free → ready to extract")
            return "has_sorry"

        if current_protected_sorry >= prev_protected_sorry:
            await agent._emit("message",
                f"[PO4] No reduction in protected sorry ({current_protected_sorry} remaining) — stopping")
            break

        await agent._emit("message", f"[PO4] Protected sorry: {prev_protected_sorry} → {current_protected_sorry}")
        prev_protected_sorry = current_protected_sorry

    # Final check: are there standalone helpers outside the protected block to extract?
    if tools.check_compiles(stub_rel).success:
        split = tools.split_theorems(stub_rel)
        extractable = [b for b in split.blocks
                       if b.name not in protected_names and b.mutual_group is None]
        if extractable:
            return "has_sorry"

    ledger.mark_failed(entry.id, "Exhausted attempts, protected block still has sorry")
    return "failed"


# ─── Extraction (decompose into helper files) ────────────────────────────────

async def _do_extract(agent, state: PO4State, ledger: LemmaLedger,
                      entry: LemmaEntry, cwd: Path) -> str:
    """Run MoveSession + decl_extractor to decompose helpers into files.

    Returns: 'extracted' | 'extract_failed'
    """
    tools = get_lean_tools()
    stub_rel = f"{entry.workspace}/Stub.lean" if "/Stub.lean" not in entry.file_path else entry.file_path

    # Stage extraction into new_decomposition/ (not decomposed/ directly)
    new_decomp_dir = cwd / entry.workspace / "new_decomposition"
    if new_decomp_dir.exists():
        shutil.rmtree(new_decomp_dir)

    session = MoveSession(tools, stub_rel, entry.name, entry.workspace,
                          output_subdir="new_decomposition")
    extractor_mcp = create_extractor_mcp_server(session)

    split = tools.split_theorems(stub_rel)
    # Identify protected names (main + mutual partners) — these stay in Stub.lean
    protected_names = {entry.name}
    for block in split.blocks:
        if block.name == entry.name and block.mutual_group is not None:
            protected_names = set(split.mutual_groups.get(block.mutual_group, [entry.name]))
            break

    extractable = [b for b in split.blocks
                   if b.name not in protected_names and b.mutual_group is None]
    await agent._emit("message", f"[PO4] Extracting {len(extractable)} standalone helpers from {stub_rel}...")

    do_not_move_note = ""
    if len(protected_names) > 1:
        do_not_move_note = (
            f"\nDo NOT move any of these (they are in a mutual block): {sorted(protected_names)}\n"
            f"Only move standalone helpers that are OUTSIDE the mutual...end block.\n"
        )

    async with swarm_agent("decl_extractor", swarm=agent.swarm, cwd=agent._cwd,
                           workspace=entry.workspace,
                           extra_mcp_servers={"extractor_tools": extractor_mcp}) as extractor:
        outcome = await verified_loop(
            agent_ctx=extractor,
            initial_input=(
                f"Extract standalone helper declarations from {stub_rel} into separate files.\n"
                f"Main theorem: '{entry.name}' (do NOT move this).\n"
                f"{do_not_move_note}"
                f"Call get_declarations first, then move_decl for each eligible helper, then commit."
            ),
            verify=lambda: _verify_extraction(tools, stub_rel, entry),
            max_rounds=3,
            max_turns=30,
            use_run_ai=False,
        )

    if not outcome.success:
        session.revert()
        return "extract_failed"

    session.finalize()
    new_files = list(new_decomp_dir.glob("lemma_helper_*.lean")) if new_decomp_dir.exists() else []
    await agent._emit("message", f"[PO4] Extraction done: {len(new_files)} files staged")
    return "extracted"


def _rewrite_imports_after_rename(cwd: Path, workspace: str, old_name: str, new_name: str):
    """After renaming a folder, rewrite imports in all .lean files in the workspace.

    Replaces 'old_name' with 'new_name' in import statements of:
    - Stub.lean (the main file that imports the helpers)
    - All .lean files inside the renamed directory (cross-references)
    """
    old_module = old_name.replace("/", ".")
    new_module = new_name.replace("/", ".")

    # Rewrite Stub.lean
    stub = cwd / workspace / "Stub.lean"
    if stub.exists():
        content = stub.read_text()
        if old_module in content:
            stub.write_text(content.replace(old_module, new_module))

    # Rewrite all .lean files in the renamed directory
    renamed_dir = cwd / workspace / new_name
    if renamed_dir.exists():
        for f in renamed_dir.rglob("*.lean"):
            content = f.read_text()
            if old_module in content:
                f.write_text(content.replace(old_module, new_module))


def _verify_extraction(tools, stub_rel: str, entry: LemmaEntry) -> str | None:
    """Verify extraction succeeded: Stub compiles, no sorry in protected block.

    Protected block = main theorem + all mutual partners. After extraction,
    only standalone helpers outside the mutual block should have been moved.
    The protected block must remain sorry-free.
    """
    cr = tools.check_compiles(stub_rel)
    if not cr.success:
        return "Stub.lean doesn't compile after extraction"

    split = tools.split_theorems(stub_rel)
    protected_names = {entry.name}
    for block in split.blocks:
        if block.name == entry.name and block.mutual_group is not None:
            protected_names = set(split.mutual_groups.get(block.mutual_group, [entry.name]))
            break

    sorry_info = tools.get_sorries_by_theorem(stub_rel)
    sorry_in_protected = [n for n in protected_names if n in sorry_info]
    if sorry_in_protected:
        return f"Protected block still has sorry: {sorry_in_protected}"
    return None


# ─── Detection (cycle check only — produces verdicts) ────────────────────────

@dataclass
class DetectVerdict:
    file_path: str
    name: str
    signature_hash: str
    statement: str
    match_type: str  # "cycle" | "reuse" | "shared" | "none"
    matched_id: str = ""
    matched_name: str = ""
    import_path: str = ""
    reason: str = ""


async def _do_detect(agent, state: PO4State, ledger: LemmaLedger,
                     entry: LemmaEntry, cwd: Path) -> str:
    """Run cycle detection on staged helpers in new_decomposition/.

    Checks each helper against:
    1. Ancestors (cycle detection via BFS)
    2. Pruned siblings from same parent (repeated failed decomposition)

    If ALL helpers match pruned siblings → REJECT decomposition entirely.
    Otherwise: commit (rename new_decomposition/ → decomposed/) and produce verdicts.

    Returns: 'no_cycle' | 'cycle_found' | 'rejected'
    """
    tools = get_lean_tools()
    new_decomp_dir = cwd / entry.workspace / "new_decomposition"
    if not new_decomp_dir.exists():
        state._detect_verdicts = []
        return "no_cycle"

    new_files = sorted(new_decomp_dir.glob("lemma_helper_*.lean"))
    if not new_files:
        state._detect_verdicts = []
        return "no_cycle"

    await agent._emit("message", f"[PO4] Running cycle detection on {len(new_files)} helpers...")

    # Gather pruned siblings' signature hashes for dedup check
    pruned_hashes = set()
    for child_id in entry.children:
        child = ledger.get(child_id)
        if child and child.status in (LemmaStatus.PRUNED, LemmaStatus.CYCLE, LemmaStatus.FAILED):
            pruned_hashes.add(child.signature_hash)

    verdicts = []
    cycles_found = False
    matched_pruned_count = 0

    for f in new_files:
        rel = str(f.relative_to(cwd))
        split = tools.split_theorems(rel)
        if not split.blocks:
            continue
        block = split.blocks[0]
        sig_hash = LemmaLedger.compute_signature_hash(block.text)

        # Check against pruned siblings (fast hash match)
        if sig_hash in pruned_hashes:
            matched_pruned_count += 1

        # Depth limit
        if entry.depth + 1 > MAX_DEPTH:
            await agent._emit("message", f"[PO4] Depth limit for {block.name}")
            continue

        # Run cycle detection
        det_result = await detect(
            agent=agent, ledger=ledger, name=block.name,
            file_path=rel, signature_hash=sig_hash,
            parent_id=entry.id, cwd=cwd,
        )

        verdict = DetectVerdict(
            file_path=rel,
            name=block.name,
            signature_hash=sig_hash,
            statement=block.text,
            match_type=det_result.match_type.value,
            matched_id=det_result.matched_id,
            matched_name=det_result.matched_name,
            import_path=det_result.import_path,
            reason=det_result.reason,
        )
        verdicts.append(verdict)

        if det_result.match_type == MatchType.CYCLE:
            cycles_found = True
            await agent._emit("message", f"[PO4] CYCLE: {block.name} ↔ {det_result.matched_name}")
        elif det_result.match_type == MatchType.REUSE:
            await agent._emit("message", f"[PO4] REUSE: {block.name} ← {det_result.matched_name}")
        elif det_result.match_type == MatchType.SHARED:
            pass  # no longer create dependencies on unproved entries

    # Check: if ALL new helpers match pruned siblings → reject decomposition
    if matched_pruned_count > 0 and matched_pruned_count >= len(new_files):
        await agent._emit("message",
            f"[PO4] REJECTED: all {matched_pruned_count} helpers match previously failed decomposition")
        # Delete staged files, restore Stub.lean from clean
        shutil.rmtree(new_decomp_dir)
        clean = cwd / entry.workspace / "Stub.clean.lean"
        stub = cwd / entry.workspace / "Stub.lean"
        if clean.exists():
            shutil.copy2(clean, stub)
        state._detect_verdicts = []
        return "rejected"

    # Accept: commit staged decomposition
    # Archive old decomposed/ if exists
    decomposed_dir = cwd / entry.workspace / "decomposed"
    if decomposed_dir.exists():
        idx = 0
        while (cwd / entry.workspace / f"decomposed_old_{idx}").exists():
            idx += 1
        decomposed_dir.rename(cwd / entry.workspace / f"decomposed_old_{idx}")

    # Rename new_decomposition/ → decomposed/
    new_decomp_dir.rename(decomposed_dir)

    # Rewrite imports: replace "new_decomposition" with "decomposed" in all affected files
    _rewrite_imports_after_rename(cwd, entry.workspace, "new_decomposition", "decomposed")

    # Update file paths in verdicts to point to decomposed/ (not new_decomposition/)
    for v in verdicts:
        v.file_path = v.file_path.replace("/new_decomposition/", "/decomposed/")

    state._detect_verdicts = verdicts
    await agent._emit("message",
        f"[PO4] Detection done: {len(verdicts)} verdicts, cycles={'yes' if cycles_found else 'no'}, "
        f"pruned_matches={matched_pruned_count}/{len(new_files)}")
    return "cycle_found" if cycles_found else "no_cycle"


# ─── Update (apply verdicts to ledger + handle failures) ─────────────────────

def _do_update(state: PO4State, ledger: LemmaLedger, entry: LemmaEntry, cwd: Path):
    """Apply all pending changes to the ledger.

    Handles:
    1. Detect verdicts (if coming from DETECT phase) — register/cycle/reuse
    2. Failed lemma propagation — if entry is FAILED, prune siblings + re-activate parent

    All DAG mutations happen here and only here.
    """
    # 1. Apply detect verdicts if any
    verdicts = getattr(state, '_detect_verdicts', None)
    if verdicts:
        for v in verdicts:
            if v.match_type == "cycle":
                cycle_entry = ledger.add_lemma(
                    name=v.name, file_path=v.file_path,
                    workspace=v.file_path.removesuffix(".lean"),
                    signature_hash=v.signature_hash, statement=v.statement,
                    parent_id=entry.id,
                )
                if not isinstance(cycle_entry, str):
                    ledger.mark_cycle(cycle_entry.id, v.matched_id)
                state.cycles_detected += 1

            elif v.match_type == "reuse":
                new_entry = ledger.add_lemma(
                    name=v.name, file_path=v.file_path,
                    workspace=v.file_path.removesuffix(".lean"),
                    signature_hash=v.signature_hash, statement=v.statement,
                    parent_id=entry.id,
                )
                if not isinstance(new_entry, str):
                    ledger.add_parent(new_entry.id, v.matched_id)
                    ledger.mark_proved(new_entry.id, v.import_path, proved_by="shortcut")

            else:
                ledger.add_lemma(
                    name=v.name, file_path=v.file_path,
                    workspace=v.file_path.removesuffix(".lean"),
                    signature_hash=v.signature_hash, statement=v.statement,
                    parent_id=entry.id,
                )

        state._detect_verdicts = None

        # Entry just decomposed — mark as contingent (waiting for children)
        if entry.status == LemmaStatus.PROVING:
            ledger.mark_contingent(entry.id)

    # 2. Prune all children of parents with dead nodes + re-activate parents + restore Stub
    from .cycle_detection import prune_siblings_of_dead
    prune_siblings_of_dead(ledger, cwd)

    # 3. Propagate proved upward: if all children of a CONTINGENT node are proved, mark it proved
    changed = True
    while changed:
        changed = False
        for e in ledger.entries():
            if e.status != LemmaStatus.CONTINGENT:
                continue
            if not e.children:
                continue
            children = ledger.get_children(e.id)
            if children and all(c.status == LemmaStatus.PROVED for c in children):
                ledger.mark_proved(e.id, e.file_path.replace("/", ".").removesuffix(".lean"),
                                   proved_by="assembly")
                changed = True


# ─── Assembly ─────────────────────────────────────────────────────────────────

async def _assemble(agent, state: PO4State, ledger: LemmaLedger, cwd: Path) -> bool:
    """Assemble proved lemmas by copying Stub.lean back to the original .lean file.

    For each proved entry with a workspace:
      <workspace>/Stub.lean → <workspace>.lean (overwrite the sorry version)

    Build order: leaves first (topo sort) so .olean files cascade correctly.
    """
    import subprocess

    topo_order = _topo_sort(ledger)
    assembled_count = 0

    for entry_id in topo_order:
        entry = ledger.get(entry_id)
        if not entry or entry.status != LemmaStatus.PROVED:
            continue

        stub_path = cwd / entry.workspace / "Stub.lean"
        target_path = cwd / f"{entry.workspace}.lean"

        if not stub_path.exists():
            continue
        if not target_path.exists():
            continue

        # Copy proved Stub.lean → original .lean file
        shutil.copy2(stub_path, target_path)
        assembled_count += 1

    if assembled_count == 0:
        return True  # nothing to assemble

    await agent._emit("message", f"[PO4] Assembled {assembled_count} files, rebuilding...")

    # Build from root to validate
    root_module = f"{state.root_workspace}.Stub".replace("/", ".")
    result = subprocess.run(
        ["lake", "build", root_module], cwd=str(cwd),
        capture_output=True, text=True, timeout=180,
    )
    output = result.stdout + "\n" + result.stderr
    has_error = any(": error:" in l and "sorry" not in l for l in output.splitlines())
    if has_error:
        await agent._emit("message", f"[PO4] Assembly build error: {output[-300:]}")
        return False

    # Clean up: remove Stub.lean from child workspaces (not the root)
    for entry_id in topo_order:
        entry = ledger.get(entry_id)
        if not entry or entry.status != LemmaStatus.PROVED:
            continue
        if entry_id == ledger.root_id:
            continue  # never clean root's Stub.lean
        stub_path = cwd / entry.workspace / "Stub.lean"
        target_path = cwd / f"{entry.workspace}.lean"
        if stub_path.exists() and target_path.exists():
            stub_path.unlink()

    # Check root sorry-free
    tools = get_lean_tools()
    root_stub = f"{state.root_workspace}/Stub.lean"
    cr = tools.check_compiles(root_stub)
    if cr.success and not cr.has_sorry:
        await agent._emit("message", "[PO4] Assembly complete: root sorry-free ✅")
        ledger.mark_proved(state.root_id, root_stub.replace("/", ".").removesuffix(".lean"))
        return True

    await agent._emit("message", "[PO4] Assembly done (root still has transitive sorry)")
    return True


def _topo_sort(ledger: LemmaLedger) -> list[str]:
    """Topological sort of DAG: leaves first, root last."""
    entries = {e.id: e for e in ledger.entries()}
    in_progress = set()
    visited = set()
    result = []

    def visit(entry_id: str):
        if entry_id in visited:
            return
        if entry_id in in_progress:
            return  # cycle — skip
        in_progress.add(entry_id)
        entry = entries.get(entry_id)
        if entry:
            for child_id in entry.children:
                visit(child_id)
        in_progress.discard(entry_id)
        visited.add(entry_id)
        result.append(entry_id)

    # Start from root
    if ledger.root_id:
        visit(ledger.root_id)

    return result  # leaves first, root last


# ─── Per-lemma agents ─────────────────────────────────────────────────────────

async def _get_writer(agent, entry: LemmaEntry, state: PO4State, ledger: LemmaLedger):
    """Get or create persistent proof_writer for this lemma."""
    from .._ledger_mcp import create_ledger_mcp_server
    attr = f"_writer_{entry.id}"
    if getattr(agent, attr, None) is None:
        ledger_mcp = create_ledger_mcp_server(ledger)
        ctx = swarm_agent(
            "proof_writer_v2", swarm=agent.swarm, cwd=agent._cwd,
            workspace=entry.workspace, can_see=["SearchAgent"],
            extra_mcp_servers={"ledger": ledger_mcp},
        )
        internal = await ctx.__aenter__()
        setattr(agent, f"{attr}_ctx", ctx)
        setattr(agent, attr, internal)
        state.agent_registry[entry.id] = state.agent_registry.get(entry.id, {})
        state.agent_registry[entry.id]["writer"] = internal.spec.name
    return getattr(agent, attr)


async def _get_guide(agent, entry: LemmaEntry, state: PO4State, ledger: LemmaLedger):
    """Get or create persistent proof_guide for this lemma.

    - Compaction disabled: guide accumulates full context across all consultations.
    - Prior state: if a guide_state file exists from a previous session, it's
      injected as the first message so the guide "remembers" past strategies.
    """
    from .._ledger_mcp import create_ledger_mcp_server
    attr = f"_guide_{entry.id}"
    if getattr(agent, attr, None) is None:
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

        # Inject prior guide state if it exists (from a previous session/compaction dump)
        cwd = Path(agent._cwd) if agent._cwd else Path.cwd()
        guide_state_path = cwd / entry.workspace / "guide_state" / f"{entry.name}.md"
        if guide_state_path.exists():
            prior_state = guide_state_path.read_text()
            await internal.run_ai(
                inp=(
                    f"PRIOR SESSION STATE (from your previous work on this lemma):\n\n"
                    f"{prior_state}\n\n"
                    f"Use this as context. You've seen this problem before."
                ),
                max_turns=1,
            )

    return getattr(agent, attr)


async def _dump_guide_state(guide, entry: LemmaEntry, cwd: Path):
    """Ask guide to summarize its accumulated knowledge and save to disk.

    Called when writer hits context threshold. The dump persists across sessions
    so a fresh guide can reload it.
    """
    result = await guide.run_ai(
        inp=(
            "DUMP YOUR STATE: Summarize everything you've learned about this proof.\n"
            "Include:\n"
            "- What strategies were tried and their outcomes\n"
            "- What proof techniques worked vs failed\n"
            "- Key insights about the theorem structure\n"
            "- What you would advise a fresh attempt to do differently\n"
            "- Specific Lean tactics or lemmas that were useful\n\n"
            "Be concise but complete. This will be your memory for next session."
        ),
        max_turns=3,
    )
    state_text = result.raw_result or ""
    if state_text.strip():
        guide_dir = cwd / entry.workspace / "guide_state"
        guide_dir.mkdir(parents=True, exist_ok=True)
        (guide_dir / f"{entry.name}.md").write_text(state_text)


# ─── Initial action for writer ─────────────────────────────────────────────────

def _build_initial_action(entry: LemmaEntry, stub_rel: str, guide_advice: str,
                          protected_names: set[str] | None = None) -> str:
    """Build the first action message for proof_writer (mirrors v3's pattern)."""
    if protected_names is None:
        protected_names = {entry.name}

    is_mutual = len(protected_names) > 1
    mutual_instruction = ""
    if is_mutual:
        mutual_instruction = (
            f"\n\nMUTUAL BLOCK RULE:\n"
            f"This file contains a mutual block: {sorted(protected_names)}\n"
            f"The ENTIRE mutual block must be sorry-free.\n"
            f"If you need helper lemmas, place them OUTSIDE and ABOVE the `mutual` keyword.\n"
            f"Helpers must be standalone (not inside mutual...end) and can have sorry.\n"
            f"Do NOT put new theorems inside the mutual block.\n"
        )

    msg = (
        f"Prove the theorem in {stub_rel}.\n"
        f"Theorem name: {entry.name}\n\n"
        f"MANDATORY FIRST STEPS (do ALL of these IN ORDER before writing any tactic):\n\n"
        f"Step 1. Read {stub_rel} to see the theorem statement\n\n"
        f"Step 2. Use lean_goal at the sorry to see the exact goal and context\n\n"
        f"Step 3. Ask SearchAgent about the types in the goal:\n"
        f"   send_message(to=\"SearchAgent\", message=\"What is the definition of <TYPE>? What lemmas exist about it?\")\n"
        f"   check_messages(timeout=60)\n\n"
        f"Step 4. Read Stub/Def.lean for available definitions\n\n"
        f"DO NOT write any proof tactics until you have completed steps 1-4.\n\n"
        f"THEN write the proof:\n"
        f"5. Factor hard sub-goals into helper theorems with sorry above the main theorem\n"
        f"6. The main theorem's proof body must be sorry-free (helpers can have sorry)\n"
        f"7. Verify with lean_verify after every change\n"
        f"{mutual_instruction}"
    )
    if guide_advice:
        msg = f"STRATEGY ADVICE from your proof guide:\n{guide_advice}\n\n{msg}"
    if entry.attempts > 0:
        msg += (
            f"\nThis is attempt {entry.attempts + 1}. Previous approaches failed.\n"
            f"Try a DIFFERENT approach.\n"
        )
    return msg


# ─── Ledger summary for guide ─────────────────────────────────────────────────

def _find_failure_paths(ledger: LemmaLedger, entry_id: str) -> str:
    """Recursively find FAILED/CYCLE entries and show the path from entry to each failure.

    Returns a formatted string showing the decomposition chain leading to failure:
      immediate_child (statement snippet)
        next_child (statement snippet)
          ... (trimmed if deep)
        failed_leaf [FAILED: reason]
    """
    lines = []

    def _walk(node_id: str, depth: int):
        node = ledger.get(node_id)
        if not node:
            return
        indent = "  " * depth

        if node.status == LemmaStatus.FAILED:
            lines.append(f"{indent}{node.name} [FAILED: {node.failure_reason[:100]}]")
            return
        if node.status == LemmaStatus.CYCLE:
            ancestor = ledger.get(node.cycle_ancestor_id)
            anc_name = ancestor.name if ancestor else "?"
            lines.append(f"{indent}{node.name} [CYCLE: ≈ {anc_name}]")
            return

        # Show this node in the path
        snippet = (node.statement or "")[:60].replace("\n", " ")
        lines.append(f"{indent}{node.name} ({snippet})")

        # If too deep, trim
        if depth >= 4:
            lines.append(f"{indent}  ... (trimmed)")
            # Jump to the leaf failure
            _find_leaf_failure(node_id, depth + 1)
            return

        # Recurse into failed/cycle/pruned children only
        for child_id in node.children:
            child = ledger.get(child_id)
            if child and child.status in (LemmaStatus.FAILED, LemmaStatus.CYCLE, LemmaStatus.PRUNED):
                _walk(child_id, depth + 1)

    def _find_leaf_failure(node_id: str, depth: int):
        """Find the deepest FAILED/CYCLE node in this subtree."""
        node = ledger.get(node_id)
        if not node:
            return
        if node.status == LemmaStatus.FAILED:
            indent = "  " * depth
            lines.append(f"{indent}{node.name} [FAILED: {node.failure_reason[:100]}]")
            return
        if node.status == LemmaStatus.CYCLE:
            indent = "  " * depth
            ancestor = ledger.get(node.cycle_ancestor_id)
            lines.append(f"{indent}{node.name} [CYCLE: ≈ {ancestor.name if ancestor else '?'}]")
            return
        for child_id in node.children:
            child = ledger.get(child_id)
            if child and child.status in (LemmaStatus.FAILED, LemmaStatus.CYCLE):
                _find_leaf_failure(child_id, depth)
                return
            if child and child.status == LemmaStatus.PRUNED:
                _find_leaf_failure(child_id, depth)
                return

    entry = ledger.get(entry_id)
    if not entry:
        return ""

    for child_id in entry.children:
        child = ledger.get(child_id)
        if child and child.status in (LemmaStatus.FAILED, LemmaStatus.CYCLE, LemmaStatus.PRUNED):
            _walk(child_id, 0)

    return "\n".join(lines) if lines else ""


def _build_ledger_summary(ledger: LemmaLedger, entry: LemmaEntry) -> str:
    """Build a targeted summary of ledger state for the proof guide.

    Called at prove time. Includes:
    - Current status (normal vs contingent needing re-decomposition)
    - Previous failed/pruned/cycle children (what decompositions failed)
    - Active children still pending
    - Ancestry (who depends on us)
    """
    proved_count = sum(1 for e in ledger.entries() if e.status == LemmaStatus.PROVED)
    contingent_count = sum(1 for e in ledger.entries() if e.status == LemmaStatus.CONTINGENT)
    total_count = len(ledger.entries())

    lines = [
        f"You are proving: {entry.name} (depth={entry.depth}, indegree={ledger.indegree(entry.id)})",
        f"DAG progress: {proved_count}/{total_count} proved, {contingent_count} contingent",
        f"\nTo find proved lemmas you can import, use: ledger_search(query=..., status_filter=['proved'])",
    ]

    # If this entry was CONTINGENT (re-activated because child failed), tell guide
    if entry.status == LemmaStatus.PENDING and entry.children:
        failure_trace = _find_failure_paths(ledger, entry.id)
        if failure_trace:
            lines.append(f"\n⚠️  THIS LEMMA WAS PREVIOUSLY CONTINGENT (decomposed, waiting on children).")
            lines.append(f"The decomposition FAILED. Decomposition path to failure:")
            lines.append(failure_trace)
            lines.append(f"\nYou need a DIFFERENT decomposition strategy.")
            lines.append(f"Consider: mutual recursion, induction, or a completely different approach.")

    # THIS lemma's pruned/failed children = previous decomposition attempts
    children = ledger.get_children(entry.id)
    pruned_children = [c for c in children if c.status == LemmaStatus.PRUNED]
    cycle_children = [c for c in children if c.status == LemmaStatus.CYCLE]

    if pruned_children:
        lines.append(f"\nYOUR PREVIOUS FAILED DECOMPOSITIONS ({len(pruned_children)}) — DO NOT repeat:")
        for c in pruned_children[:5]:
            lines.append(f"  - {c.name}: {c.pruned_reason}")
        if len(pruned_children) > 5:
            lines.append(f"  ... and {len(pruned_children) - 5} more")

    if cycle_children:
        lines.append(f"\nCYCLES DETECTED ({len(cycle_children)}) — these helpers recreated an ancestor:")
        for c in cycle_children:
            ancestor = ledger.get(c.cycle_ancestor_id)
            ancestor_name = ancestor.name if ancestor else "unknown"
            lines.append(f"  - {c.name} ≈ {ancestor_name} — the lemma decomposes recursively to a "
                         f"very similar signature. Possibly INDUCTION will be more helpful here.")

    # Active children still pending/contingent
    active_children = [c for c in children
                       if c.status in (LemmaStatus.PENDING, LemmaStatus.PROVING, LemmaStatus.CONTINGENT)]
    if active_children:
        lines.append(f"\nYour current sub-lemmas ({len(active_children)}):")
        for c in active_children:
            lines.append(f"  - {c.name} [{c.status.value}]")

    # Ancestry (who depends on us)
    ancestry = ledger.get_ancestry(entry.id)
    if ancestry:
        ancestor_names = [ledger.get(aid).name for aid in ancestry if ledger.get(aid)]
        lines.append(f"\nBlocked on you (ancestry): {' → '.join(reversed(ancestor_names))} → {entry.name}")

    return "\n".join(lines)


# ─── Progress ─────────────────────────────────────────────────────────────────

def _write_progress(cwd: Path, state: PO4State, ledger: LemmaLedger):
    """Write progress.md for TaskManager monitoring."""
    workspace_abs = cwd / state.root_workspace
    workspace_abs.mkdir(parents=True, exist_ok=True)
    progress = workspace_abs / "progress.md"

    entries = ledger.entries()
    proved = [e for e in entries if e.status == LemmaStatus.PROVED]
    pending = [e for e in entries if e.status == LemmaStatus.PENDING]
    failed = [e for e in entries if e.status == LemmaStatus.FAILED]
    cycles = [e for e in entries if e.status == LemmaStatus.CYCLE]
    pruned = [e for e in entries if e.status == LemmaStatus.PRUNED]

    current = ledger.get(state.current_lemma_id) if state.current_lemma_id else None
    current_name = current.name if current else "none"

    content = (
        f"# Proof Progress (v4)\n\n"
        f"- **Stage**: {state.stage}\n"
        f"- **Root theorem**: {state.root_theorem_name}\n"
        f"- **Current lemma**: {current_name}\n"
        f"- **Total attempts**: {state.total_attempts}\n"
        f"- **Proved**: {len(proved)}/{len(entries)}\n"
        f"- **Pending**: {len(pending)}\n"
        f"- **Failed**: {len(failed)}\n"
        f"- **Cycles**: {len(cycles)}\n"
        f"- **Pruned**: {len(pruned)}\n\n"
    )

    if proved:
        content += "## Proved\n"
        for e in proved:
            content += f"- ✅ `{e.name}`\n"
        content += "\n"

    if pending:
        content += "## Pending\n"
        for e in pending:
            content += f"- ⏳ `{e.name}` (depth={e.depth})\n"
        content += "\n"

    if failed or cycles:
        content += "## Failed/Cycles\n"
        for e in failed:
            content += f"- ❌ `{e.name}`: {e.failure_reason}\n"
        for e in cycles:
            ancestor = ledger.get(e.cycle_ancestor_id)
            content += f"- ⟳ `{e.name}` → {ancestor.name if ancestor else '?'}\n"
        content += "\n"

    progress.write_text(content)


# ─── Checkpoint ───────────────────────────────────────────────────────────────

def _save_state(cwd: Path, state: PO4State):
    workspace = cwd / state.root_workspace
    workspace.mkdir(parents=True, exist_ok=True)
    (workspace / "po4_checkpoint.json").write_text(json.dumps(asdict(state), indent=2))


def _load_state(cwd: Path, workspace_rel: str) -> PO4State | None:
    cp = cwd / workspace_rel / "po4_checkpoint.json"
    if not cp.exists():
        return None
    try:
        data = json.loads(cp.read_text())
        return PO4State(**{k: v for k, v in data.items() if k in PO4State.__dataclass_fields__})
    except (json.JSONDecodeError, TypeError):
        return None


def _write_session_summary(cwd: Path, state: PO4State, ledger: LemmaLedger,
                           elapsed: float, total_cost: float):
    """Write session_summary.json to the session folder for replay/reporting."""
    from datetime import datetime

    sessions_dir = cwd / "StrataAgent" / "strataswarm" / "temp" / "sessions"
    if not sessions_dir.exists():
        return

    # Find the latest session folder
    session_dirs = sorted(sessions_dir.iterdir(), reverse=True)
    if not session_dirs:
        return
    session_dir = session_dirs[0]

    entries = ledger.entries()
    summary = {
        "timestamp": datetime.now().isoformat(),
        "theorem": state.root_theorem_name,
        "workspace": state.root_workspace,
        "stage": state.stage,
        "time_seconds": round(elapsed),
        "cost_usd": round(total_cost, 4),
        "total_lemmas": len(entries),
        "proved": sum(1 for e in entries if e.status == LemmaStatus.PROVED),
        "failed": sum(1 for e in entries if e.status == LemmaStatus.FAILED),
        "cycles": sum(1 for e in entries if e.status == LemmaStatus.CYCLE),
        "pending": sum(1 for e in entries if e.status == LemmaStatus.PENDING),
        "total_attempts": state.total_attempts,
    }

    (session_dir / "session_summary.json").write_text(json.dumps(summary, indent=2))
