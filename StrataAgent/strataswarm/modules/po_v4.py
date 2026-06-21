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

MAX_DEPTH = 4


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
    from .._types import AgentResult, AgentStatus

    await agent._emit("status_change", "running")

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
    await agent._emit("message", f"[PO4] Finished: stage={state.stage}, proved={state.lemmas_proved}, cycles={state.cycles_detected}")
    ledger.save()

    status = AgentStatus.COMPLETED if state.stage == "done" else AgentStatus.FAILED
    return AgentResult(name=agent.spec.name, status=status,
                       output={"stage": state.stage, "proved": state.lemmas_proved,
                               "cycles": state.cycles_detected})


# ─── Phase handlers (each returns a Trans value) ─────────────────────────────

async def _do_select(agent, state: PO4State, ledger: LemmaLedger) -> Trans:
    """Pick the most pressing pending lemma from the DAG."""
    lemma = ledger.pick_next()
    if lemma is None:
        return Trans.BLOCKED
    state.current_lemma_id = lemma.id
    ledger.mark_proving(lemma.id)
    await agent._emit("message",
        f"[PO4] Selected: {lemma.name} (depth={lemma.depth}, "
        f"indegree={ledger.indegree(lemma.id)}, budget={lemma.turn_budget})")
    return Trans.PICKED


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
    return Trans.CYCLE_FOUND if result == "cycle_found" else Trans.NO_CYCLE


async def _do_update_phase(agent, state: PO4State, ledger: LemmaLedger, cwd: Path) -> Trans:
    """Apply verdicts to ledger, prune siblings of dead nodes."""
    lemma = ledger.get(state.current_lemma_id)
    _do_update(state, ledger, lemma, cwd)
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

WRITER_TURNS = [25, 12, 6]
GRACE_TURNS = 20
WRITER_CLEANUP_TURNS = 10


async def _attempt_prove(agent, state: PO4State, ledger: LemmaLedger,
                         entry: LemmaEntry, cwd: Path) -> str:
    """Attempt to prove a single lemma.

    Two phases (same as v3):
    1. Initial attempts — try to close all sorry directly (decreasing budget)
    2. Grace attempts — if main theorem still has sorry, factor into helpers
       until main is sorry-free (helpers can keep sorry → extract phase)

    Returns: 'proved' | 'has_sorry' | 'failed' | 'contradictory'
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

    # Brief guide with ledger context
    ledger_summary = _build_ledger_summary(ledger, entry)
    # Get initial strategy from guide (same pattern as v3)
    await agent._emit("message", f"[PO4] Consulting guide for {entry.name}...")
    initial_advice = await guide.run_ai(
        inp=(
            f"CONTEXT:\n{ledger_summary}\n\n"
            f"A proof_writer is about to prove theorem '{entry.name}' in {stub_rel}.\n"
            f"Read the cheat sheet and then advise on the best approach.\n"
            f"Consider: what proof technique fits this theorem's structure? "
            f"What common pitfalls should the writer avoid?\n"
            f"If the theorem statement looks contradictory or not provable as stated, "
            f"say so clearly."
        ),
    )
    guide_advice = initial_advice.raw_result or ""

    # Check for contradictory diagnosis
    if "contradictory" in guide_advice.lower() and "not provable" in guide_advice.lower():
        await agent._emit("message", f"[PO4] Guide hints at contradiction for {entry.name}")
        # TODO: structured contradictory confirmation

    # Build verifier
    verify_fn = make_proof_writer_verifier(stub_rel, original_content, entry.workspace, entry.name)

    # Build initial action for writer (same pattern as v3 — explicit SearchAgent instructions)
    action = _build_initial_action(entry, stub_rel, guide_advice)

    # ── Phase 1: Initial attempts (try to close all sorry directly) ──
    for attempt_idx in range(len(WRITER_TURNS)):
        turns = WRITER_TURNS[attempt_idx]
        ledger.increment_attempts(entry.id)
        await agent._emit("message",
            f"[PO4] Attempt {entry.attempts}/{entry.max_attempts} ({turns} turns)")

        outcome = await verified_loop(
            agent_ctx=writer,
            initial_input=f"{action}\n\nYou have {turns} turns.",
            verify=verify_fn,
            max_rounds=2,
            max_turns=turns,
            use_run_ai=True,
        )

        # Proved: this file has no sorry (text check — transitive check is for assembly only)
        if not tools.has_sorry(stub_rel) and tools.check_compiles(stub_rel).success:
            ledger.mark_proved(entry.id, stub_rel.replace("/", ".").removesuffix(".lean"))
            return "proved"

        # Check progress
        current = (cwd / stub_rel).read_text()
        if current.strip() == original_content.strip():
            await agent._emit("message", "[PO4] No progress — file unchanged")
            continue

        if not tools.check_compiles(stub_rel).success:
            await agent._emit("message", "[PO4] File broken — cleanup round")
            await writer.run_ai(
                inp="Your file does not compile. Fix compilation errors ONLY. "
                    "Do not add new proof content. Just make it compile (sorry is fine).",
                max_turns=WRITER_CLEANUP_TURNS,
            )
            if not tools.check_compiles(stub_rel).success:
                (cwd / stub_rel).write_text(original_content)
                continue

        # Consult guide between attempts — skip on last iteration (no next attempt)
        if attempt_idx >= len(WRITER_TURNS) - 1:
            break

        sorry_info = tools.get_sorries_by_theorem(stub_rel)
        sorry_count = sum(len(v) for v in sorry_info.values())
        await agent._emit("message", f"[PO4] Still has {sorry_count} sorry. Consulting guide...")

        first_thm = next(iter(sorry_info), None)
        sorry_detail = ""
        if first_thm and sorry_info[first_thm]:
            pos = sorry_info[first_thm][0]
            sorry_detail = f"\nUse lean_goal at {stub_rel} line {pos['line']} col {pos['col']} to see the stuck goal."

        advice_result = await guide.run_ai(
            inp=(
                f"Writer is stuck after attempt {entry.attempts}.\n"
                f"File: {stub_rel}\n"
                f"Goals with sorry: {sorry_info}\n"
                f"{sorry_detail}\n"
                f"Diagnose the stuck goals (use lean_goal) and advise what to try next.\n"
                f"If a goal looks contradictory or needs strengthening, say so clearly."
            ),
        )
        advice = advice_result.raw_result or "Try a different approach."
        action = f"STRATEGY ADVICE from your proof guide:\n{advice}\n\nApply this advice and continue the proof."

    # ── Phase 2: Grace — factor remaining sorry into helpers ──
    sorry_info = tools.get_sorries_by_theorem(stub_rel)
    main_sorry_count = len(sorry_info.get(entry.name, []))

    if main_sorry_count == 0:
        # Main theorem already sorry-free, helpers have sorry → ready to extract
        await agent._emit("message", "[PO4] Main theorem sorry-free → ready to extract")
        return "has_sorry"

    await agent._emit("message",
        f"[PO4] Grace phase: {main_sorry_count} sorry in main, factoring into helpers...")

    prev_main_sorry = main_sorry_count
    for grace in range(main_sorry_count):
        await agent._emit("message", f"[PO4] Grace {grace + 1}/{main_sorry_count} ({GRACE_TURNS} turns)")

        sorry_info = tools.get_sorries_by_theorem(stub_rel)
        grace_action = (
            f"WRAP UP — grace attempt {grace + 1}.\n\n"
            f"Remaining sorry in main theorem '{entry.name}': {sorry_info.get(entry.name, [])}\n\n"
            f"For each sorry you cannot close directly, factor it into a helper:\n"
            f"  theorem helper_<name> (<params>) : <goal_type> := by sorry\n"
            f"Then use `exact helper_<name> ...` in the main proof.\n\n"
            f"The MAIN theorem '{entry.name}' must be sorry-free when you're done.\n"
            f"Helpers CAN have sorry. Keep everything in one file. Make it compile."
        )

        outcome = await verified_loop(
            agent_ctx=writer,
            initial_input=f"{grace_action}\n\nYou have {GRACE_TURNS} turns.",
            verify=verify_fn,
            max_rounds=2,
            max_turns=GRACE_TURNS,
            use_run_ai=True,
        )

        # Check if fully proved (transitively — no sorry in imports either)
        cr = tools.check_compiles(stub_rel)
        if cr.success and not cr.has_sorry:
            ledger.mark_proved(entry.id, stub_rel.replace("/", ".").removesuffix(".lean"))
            return "proved"

        sorry_info = tools.get_sorries_by_theorem(stub_rel)
        current_main_sorry = len(sorry_info.get(entry.name, []))

        if current_main_sorry == 0:
            await agent._emit("message", "[PO4] Main theorem sorry-free → ready to extract")
            return "has_sorry"

        if current_main_sorry >= prev_main_sorry:
            await agent._emit("message",
                f"[PO4] No reduction in main sorry ({current_main_sorry} remaining) — stopping")
            break

        await agent._emit("message", f"[PO4] Main sorry: {prev_main_sorry} → {current_main_sorry}")
        prev_main_sorry = current_main_sorry

    # Final check: is there anything to extract?
    if tools.check_compiles(stub_rel).success:
        split = tools.split_theorems(stub_rel)
        helpers = [b for b in split.blocks if b.name != entry.name]
        if helpers:
            return "has_sorry"

    ledger.mark_failed(entry.id, "Exhausted attempts, sorry count not reducing")
    return "failed"


# ─── Extraction (decompose into helper files) ────────────────────────────────

async def _do_extract(agent, state: PO4State, ledger: LemmaLedger,
                      entry: LemmaEntry, cwd: Path) -> str:
    """Run MoveSession + decl_extractor to decompose helpers into files.

    Returns: 'extracted' | 'extract_failed'
    """
    tools = get_lean_tools()
    stub_rel = f"{entry.workspace}/Stub.lean" if "/Stub.lean" not in entry.file_path else entry.file_path

    session = MoveSession(tools, stub_rel, entry.name, entry.workspace)
    extractor_mcp = create_extractor_mcp_server(session)

    split = tools.split_theorems(stub_rel)
    helper_count = len([b for b in split.blocks if b.name != entry.name])
    await agent._emit("message", f"[PO4] Extracting {helper_count} helpers from {stub_rel}...")

    async with swarm_agent("decl_extractor", swarm=agent.swarm, cwd=agent._cwd,
                           workspace=entry.workspace,
                           extra_mcp_servers={"extractor_tools": extractor_mcp}) as extractor:
        outcome = await verified_loop(
            agent_ctx=extractor,
            initial_input=(
                f"Extract all helper declarations from {stub_rel} into separate files.\n"
                f"Main theorem: '{entry.name}' (do NOT move this).\n"
                f"Call get_declarations first, then move_decl for each helper, then commit."
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
    decomposed_dir = cwd / entry.workspace / "decomposed"
    new_files = list(decomposed_dir.glob("lemma_helper_*.lean")) if decomposed_dir.exists() else []
    await agent._emit("message", f"[PO4] Extraction done: {len(new_files)} files created")
    return "extracted"


def _verify_extraction(tools, stub_rel: str, entry: LemmaEntry) -> str | None:
    """Verify extraction succeeded: Stub compiles, no sorry in main theorem."""
    cr = tools.check_compiles(stub_rel)
    if not cr.success:
        return "Stub.lean doesn't compile after extraction"
    sorry_info = tools.get_sorries_by_theorem(stub_rel)
    if entry.name in sorry_info:
        return f"Main theorem '{entry.name}' still has sorry"
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
    """Run cycle detection on each extracted helper. Produces verdicts stored in state.

    Does NOT modify the ledger — that's _do_update's job.
    Returns: 'no_cycle' | 'cycle_found'
    """
    tools = get_lean_tools()
    decomposed_dir = cwd / entry.workspace / "decomposed"
    if not decomposed_dir.exists():
        state._detect_verdicts = []
        return "no_cycle"

    new_files = sorted(decomposed_dir.glob("lemma_helper_*.lean"))
    await agent._emit("message", f"[PO4] Running cycle detection on {len(new_files)} helpers...")

    verdicts = []
    cycles_found = False

    for f in new_files:
        rel = str(f.relative_to(cwd))
        split = tools.split_theorems(rel)
        if not split.blocks:
            continue
        block = split.blocks[0]
        sig_hash = LemmaLedger.compute_signature_hash(block.text)

        # Depth limit
        if entry.depth + 1 > MAX_DEPTH:
            await agent._emit("message", f"[PO4] Depth limit for {block.name}")
            continue

        # Run detection
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
            await agent._emit("message", f"[PO4] SHARED: {block.name} ↔ {det_result.matched_name}")

    # Store verdicts for _do_update to consume
    state._detect_verdicts = verdicts
    await agent._emit("message", f"[PO4] Detection done: {len(verdicts)} verdicts, cycles={'yes' if cycles_found else 'no'}")
    return "cycle_found" if cycles_found else "no_cycle"


# ─── Update (apply verdicts to ledger + handle failures) ─────────────────────

def _do_update(state: PO4State, ledger: LemmaLedger, entry: LemmaEntry, cwd: Path):
    """Apply all pending changes to the ledger.

    Handles:
    1. Detect verdicts (if coming from DETECT phase) — register/cycle/reuse/shared
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

            elif v.match_type == "shared":
                new_entry = ledger.add_lemma(
                    name=v.name, file_path=v.file_path,
                    workspace=v.file_path.removesuffix(".lean"),
                    signature_hash=v.signature_hash, statement=v.statement,
                    parent_id=entry.id,
                )
                if not isinstance(new_entry, str):
                    ledger.add_parent(v.matched_id, new_entry.id)

            else:
                ledger.add_lemma(
                    name=v.name, file_path=v.file_path,
                    workspace=v.file_path.removesuffix(".lean"),
                    signature_hash=v.signature_hash, statement=v.statement,
                    parent_id=entry.id,
                )

        state._detect_verdicts = None

    # 2. Prune all children of parents with dead nodes + re-activate parents + restore Stub
    from .cycle_detection import prune_siblings_of_dead
    prune_siblings_of_dead(ledger, cwd)


# ─── Assembly ─────────────────────────────────────────────────────────────────

async def _assemble(agent, state: PO4State, ledger: LemmaLedger, cwd: Path) -> bool:
    """Bottom-up topological assembly.

    Walks the DAG from leaves to root. At each node that has proved children:
    rewrites imports in Stub.lean to point to the proved child's module, then builds.
    """
    import subprocess
    tools = get_lean_tools()

    # Get topological order (leaves first, root last)
    topo_order = _topo_sort(ledger)
    await agent._emit("message", f"[PO4] Assembly: {len(topo_order)} nodes in topo order")

    for entry_id in topo_order:
        entry = ledger.get(entry_id)
        if not entry or entry.status != LemmaStatus.PROVED:
            continue

        children = ledger.get_children(entry_id)
        proved_children = [c for c in children if c.status == LemmaStatus.PROVED]
        if not proved_children:
            continue

        # Rewrite imports: for each proved child, point to its module
        stub_path = cwd / entry.workspace / "Stub.lean"
        if not stub_path.exists():
            continue

        content = stub_path.read_text()
        changed = False
        for child in proved_children:
            child_module = child.file_path.replace("/", ".").removesuffix(".lean")
            # If Stub.lean imports the decomposed helper file, rewrite to import proved Stub
            child_workspace_module = child.workspace.replace("/", ".")
            if f"import {child_workspace_module}" in content and f"import {child_workspace_module}.Stub" not in content:
                content = content.replace(
                    f"import {child_workspace_module}",
                    f"import {child_workspace_module}.Stub"
                )
                changed = True

        if changed:
            stub_path.write_text(content)

        # Build this module
        module = f"{entry.workspace}.Stub".replace("/", ".")
        result = subprocess.run(
            ["lake", "build", module], cwd=str(cwd),
            capture_output=True, text=True, timeout=120,
        )
        output = result.stdout + "\n" + result.stderr
        has_error = any(": error:" in l and "sorry" not in l for l in output.splitlines())
        if has_error:
            await agent._emit("message", f"[PO4] Assembly error at {entry.name}: {output[-200:]}")
            return False

    # Final check: root sorry-free (transitive — lake build catches sorry in imports)
    root_stub = f"{state.root_workspace}/Stub.lean"
    cr = tools.check_compiles(root_stub)
    if cr.success and not cr.has_sorry:
        await agent._emit("message", "[PO4] Assembly complete: root sorry-free ✅")
        ledger.mark_proved(state.root_id, root_stub.replace("/", ".").removesuffix(".lean"))
        return True

    await agent._emit("message", "[PO4] Assembly failed: root still has sorry or errors")
    return False


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
    """Get or create persistent proof_guide for this lemma."""
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
        )
        internal = await ctx.__aenter__()
        setattr(agent, f"{attr}_ctx", ctx)
        setattr(agent, attr, internal)
        state.agent_registry[entry.id] = state.agent_registry.get(entry.id, {})
        state.agent_registry[entry.id]["guide"] = internal.spec.name
    return getattr(agent, attr)


# ─── Initial action for writer ─────────────────────────────────────────────────

def _build_initial_action(entry: LemmaEntry, stub_rel: str, guide_advice: str) -> str:
    """Build the first action message for proof_writer (mirrors v3's pattern)."""
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

def _build_ledger_summary(ledger: LemmaLedger, entry: LemmaEntry) -> str:
    """Build a targeted summary of ledger state for the proof guide.

    Called at prove time. Includes:
    - What's proved (importable)
    - Previous failed attempts on THIS lemma (pruned children = bad decompositions)
    - Cycles detected in this lemma's history
    - What depends on this lemma (motivation)
    """
    proved_count = sum(1 for e in ledger.entries() if e.status == LemmaStatus.PROVED)
    total_count = len(ledger.entries())

    lines = [
        f"You are proving: {entry.name} (depth={entry.depth}, indegree={ledger.indegree(entry.id)})",
        f"DAG progress: {proved_count}/{total_count} proved",
        f"\nTo find proved lemmas you can import, use: ledger_search(query=..., status_filter=['proved'])",
    ]

    # THIS lemma's pruned children = previous decomposition attempts that FAILED
    children = ledger.get_children(entry.id)
    pruned_children = [c for c in children if c.status == LemmaStatus.PRUNED]
    cycle_children = [c for c in children if c.status == LemmaStatus.CYCLE]

    if pruned_children:
        lines.append(f"\nYOUR PREVIOUS FAILED DECOMPOSITIONS ({len(pruned_children)}) — DO NOT repeat:")
        for c in pruned_children:
            lines.append(f"  - {c.name}: {c.pruned_reason}")

    if cycle_children:
        lines.append(f"\nCYCLES DETECTED ({len(cycle_children)}) — these helpers recreated an ancestor:")
        for c in cycle_children:
            ancestor = ledger.get(c.cycle_ancestor_id)
            ancestor_name = ancestor.name if ancestor else "unknown"
            lines.append(f"  - {c.name} ≈ {ancestor_name} — the lemma decomposes recursively to a "
                         f"very similar signature. Possibly INDUCTION will be more helpful here.")

    # Active children still pending
    active_children = [c for c in children if c.status in (LemmaStatus.PENDING, LemmaStatus.PROVING)]
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
