"""Proof Orchestrator v5: Recursive with parallel child POs.

Pipeline:
  SOUNDNESS → SPLIT → ASSESS → (PROVE_DIRECT | DECOMPOSE → SKETCH → CHILD_CEA → REFACTOR → CHILD_POS) → ASSEMBLE → VALIDATE → DONE

Key design:
- ASSESS evaluates the MAIN theorem only (direct or decompose?)
- Parent never proves decomposed lemmas — always spawns child POs
- Child POs are parallel (capped by global proof_writer semaphore)
- Each child is a full PO (self-assesses, may decompose further)
- At max depth, ASSESS forces "direct" (no further decomposition)
- All verification via SwarmLeanTools (deterministic, no agents)
- Agents used ONLY for: proof_writer, decomposer, sketcher, CEA
"""

from __future__ import annotations

import asyncio
import shutil
from dataclasses import dataclass, field
from enum import Enum
from pathlib import Path
from typing import Any, TypeVar

from .po_agents import (
    ProofResult, SketchResult, SoundnessVerdict, ValidationResult, LoopOutcome,
    verified_loop, run_proof_writer, run_cea,
    run_sketcher, run_child_po, swarm_checkpoint,
)
from .po_verify import (
    check_import_dag, verify_file_exists, verify_no_sorry,
    count_sorries, verify_split_complete,
)
from .po_util import (
    rewrite_imports_for_child, write_checkpoint, write_progress,
    setup_child_workspace,
)
from .po_lean import get_lean_tools
from .._helpers import swarm_agent

T = TypeVar("T")

MAX_RETRIES = 3
MAX_RECURSION_DEPTH = 2
MAX_CONCURRENT_WRITERS = 1
DECOMPOSER_MAX_TURNS = 100
WRITER_MAX_TURNS = 50
WRITER_EXTENDED_TURNS = 80

# Global semaphore shared across all PO instances in this process
_writer_semaphore: asyncio.Semaphore | None = None


def _get_writer_semaphore() -> asyncio.Semaphore:
    global _writer_semaphore
    if _writer_semaphore is None:
        _writer_semaphore = asyncio.Semaphore(MAX_CONCURRENT_WRITERS)
    return _writer_semaphore


# ─── Enums ────────────────────────────────────────────────────────────────────

class Stage(str, Enum):
    SOUNDNESS = "soundness"
    SPLIT = "split"
    DECOMPOSE = "decompose"
    PROVE_DIRECT = "prove_direct"
    SKETCH = "sketch"
    CHILD_CEA = "child_cea"
    REFACTOR = "refactor"
    CHILD_POS = "child_pos"
    ASSEMBLE = "assemble"
    VALIDATE = "validate"
    RETRY = "retry"
    DONE = "done"
    FAILED = "failed"


class Trans(str, Enum):
    SOUND = "sound"
    SKIPPED = "skipped"
    UNSOUND = "unsound"
    SPLIT_DONE = "split_done"
    SPLIT_FAILED = "split_failed"
    DIRECT = "direct"
    DECOMPOSED = "decomposed"
    NEEDS_RETRY = "needs_retry"
    PROVED = "proved"
    HAS_CHILDREN = "has_children"
    NO_PROGRESS = "no_progress"
    SKETCH_OK = "sketch_ok"
    SKETCH_FAILED = "sketch_failed"
    ALL_SOUND = "all_sound"
    SOME_UNSOUND = "some_unsound"
    ALL_PROVED = "all_proved"
    CHILD_FAILED = "child_failed"
    ASSEMBLED = "assembled"
    VALID = "valid"
    INVALID = "invalid"
    FAILED = "failed"
    NEW_APPROACH = "new_approach"
    MAX_RETRIES = "max_retries"


TRANSITIONS: dict[tuple[Stage, Trans], Stage] = {
    (Stage.SOUNDNESS, Trans.SOUND):              Stage.SPLIT,
    (Stage.SOUNDNESS, Trans.SKIPPED):            Stage.SPLIT,
    (Stage.SOUNDNESS, Trans.UNSOUND):            Stage.FAILED,

    (Stage.SPLIT, Trans.SPLIT_DONE):             Stage.DECOMPOSE,
    (Stage.SPLIT, Trans.SPLIT_FAILED):           Stage.DECOMPOSE,

    # DECOMPOSE decides: "direct" (skip sketch, go straight to prove) or "decompose" (sketch)
    (Stage.DECOMPOSE, Trans.DIRECT):             Stage.PROVE_DIRECT,
    (Stage.DECOMPOSE, Trans.DECOMPOSED):         Stage.SKETCH,
    (Stage.DECOMPOSE, Trans.NEEDS_RETRY):        Stage.RETRY,

    # PROVE_DIRECT: attempt → extract sorries → child POs if any
    (Stage.PROVE_DIRECT, Trans.PROVED):          Stage.ASSEMBLE,
    (Stage.PROVE_DIRECT, Trans.HAS_CHILDREN):    Stage.CHILD_POS,
    (Stage.PROVE_DIRECT, Trans.NO_PROGRESS):     Stage.RETRY,

    (Stage.SKETCH, Trans.SKETCH_OK):             Stage.CHILD_CEA,
    (Stage.SKETCH, Trans.SKETCH_FAILED):         Stage.RETRY,

    (Stage.CHILD_CEA, Trans.ALL_SOUND):          Stage.REFACTOR,
    (Stage.CHILD_CEA, Trans.SOME_UNSOUND):       Stage.RETRY,

    (Stage.REFACTOR, Trans.HAS_CHILDREN):        Stage.CHILD_POS,
    (Stage.REFACTOR, Trans.ALL_PROVED):          Stage.ASSEMBLE,

    (Stage.CHILD_POS, Trans.ALL_PROVED):         Stage.ASSEMBLE,
    (Stage.CHILD_POS, Trans.CHILD_FAILED):       Stage.RETRY,

    (Stage.ASSEMBLE, Trans.ASSEMBLED):           Stage.VALIDATE,
    (Stage.ASSEMBLE, Trans.FAILED):              Stage.RETRY,

    (Stage.VALIDATE, Trans.VALID):               Stage.DONE,
    (Stage.VALIDATE, Trans.INVALID):             Stage.RETRY,

    (Stage.RETRY, Trans.NEW_APPROACH):           Stage.DECOMPOSE,
    (Stage.RETRY, Trans.MAX_RETRIES):            Stage.FAILED,
}


# ─── State ────────────────────────────────────────────────────────────────────

@dataclass
class SubGoal:
    name: str = ""
    filename: str = ""
    description: str = ""
    depends_on: list[str] = field(default_factory=list)


@dataclass
class DecomposeResult:
    strategy: str = "decompose"
    sub_goals: list[SubGoal] = field(default_factory=list)
    proof_sketch: str = ""
    reasoning: str = ""


@dataclass
class ProverState:
    stage: Stage = Stage.SOUNDNESS
    theorem_file: str = ""
    theorem_name: str = ""
    workspace: str = ""
    skip_soundness: bool = False
    depth: int = 0

    # Files in decomposed/ (populated after DECOMPOSE + REFACTOR)
    decomposed_files: list[str] = field(default_factory=list)
    proved_files: list[str] = field(default_factory=list)

    # Meta
    attempt: int = 0
    parent_agent: str = "TaskManager"
    failure_reason: str = ""
    last_failure_details: str = ""

    # Identity (for recursive checkpoint recovery via swarm checkpoint visibility graph)
    agent_name: str = ""
    internal_agents: dict = field(default_factory=dict)  # e.g. {"decomposer": "po_decomposer_19"}


# ─── Main loop ────────────────────────────────────────────────────────────────

async def run_workflow(agent, inp: Any, result_type: type[T] | None = None):
    from .._types import AgentResult, AgentStatus

    await agent._emit("status_change", "running")

    if isinstance(inp, dict):
        theorem_file = inp.get("theorem_file", "")
        theorem_name = inp.get("theorem_name", "")
        workspace_rel = inp.get("workspace", "")
        skip_soundness = inp.get("skip_soundness", False)
        parent_agent = inp.get("parent_agent", "TaskManager")
        depth = inp.get("depth", 0)
    elif isinstance(inp, str):
        theorem_file, theorem_name, workspace_rel = inp, "", ""
        skip_soundness, parent_agent, depth = False, "TaskManager", 0
    else:
        theorem_file, theorem_name, workspace_rel = str(inp), "", ""
        skip_soundness, parent_agent, depth = False, "TaskManager", 0

    cwd = Path(agent._cwd) if agent._cwd else Path.cwd()

    if not workspace_rel:
        await agent._emit("message", "[PO] ERROR: No workspace provided.")
        return AgentResult(name=agent.spec.name, status=AgentStatus.FAILED,
                           output={"stage": "failed", "error": "no_workspace"})

    workspace_abs = cwd / workspace_rel
    workspace_abs.mkdir(parents=True, exist_ok=True)

    stub_file = workspace_abs / "Stub.lean"
    if not stub_file.exists():
        await agent._emit("message", f"[PO] ERROR: No Stub.lean in {workspace_rel}")
        return AgentResult(name=agent.spec.name, status=AgentStatus.FAILED,
                           output={"stage": "failed", "error": "stub_not_found"})

    originals_dir = workspace_abs / "_originals"
    originals_dir.mkdir(exist_ok=True)
    if not (originals_dir / "Stub.lean").exists():
        shutil.copy2(stub_file, originals_dir / "Stub.lean")

    # Resume from checkpoint or fresh start
    restored = getattr(agent, '_restored_state', None)
    if restored and isinstance(restored, dict):
        state = ProverState(**{k: (Stage(v) if k == "stage" else v)
                               for k, v in restored.items() if k in ProverState.__dataclass_fields__})
        agent._restored_state = None
        await agent._emit("message", f"[PO] RESUMED: stage={state.stage.value}, proved={len(state.proved_files)}")
    else:
        state = ProverState(
            theorem_file=theorem_file, theorem_name=theorem_name,
            workspace=workspace_rel, skip_soundness=skip_soundness,
            parent_agent=parent_agent, depth=depth,
        )

    state.agent_name = agent.spec.name
    agent._workflow_state = state
    await agent._emit("message", f"[PO] Starting: {theorem_name} in {workspace_rel} (depth={depth}, agent={state.agent_name})")

    while not agent.cancellation.is_cancelled:
        if state.stage in (Stage.DONE, Stage.FAILED):
            break
        try:
            transition = await HANDLERS[state.stage](state, agent)
            next_stage = TRANSITIONS.get((state.stage, transition), Stage.RETRY)

            await agent._emit("state_transition", {
                "from": state.stage.value, "transition": transition.value, "to": next_stage.value})
            await agent._emit("message", f"[PO] {state.stage.value} →{transition.value}→ {next_stage.value}")

            state.stage = next_stage
            agent._workflow_state = state
            write_progress(cwd, state)
            write_checkpoint(cwd, state)
        except Exception as e:
            await agent._emit("message", f"[PO] Error in {state.stage.value}: {e}")
            if state.stage == Stage.RETRY:
                # Error in retry handler itself — force fail to prevent infinite loop
                state.stage = Stage.FAILED
                state.failure_reason = f"retry handler crashed: {e}"
            else:
                state.stage = Stage.RETRY
            write_checkpoint(cwd, state)

    await _notify_parent(agent, state,
        f"Proof {'complete' if state.stage == Stage.DONE else 'failed'}: {theorem_file}")
    await _cleanup_internal(agent, "decomposer")

    result = AgentResult(name=agent.spec.name, status=AgentStatus.COMPLETED)
    result.output = {"stage": state.stage.value, "theorem_file": theorem_file,
                     "attempts": state.attempt, "details": state.last_failure_details}
    return result


# ─── Stage handlers ──────────────────────────────────────────────────────────

async def _stage_soundness(state: ProverState, agent) -> Trans:
    if state.skip_soundness:
        return Trans.SKIPPED
    verdict = await run_cea(agent, state.workspace, f"{state.workspace}/Stub.lean", state.theorem_name)
    if verdict and not verdict.sound and verdict.confidence == "high":
        state.failure_reason = "unsound"
        await agent._emit("message", f"[PO] UNSOUND: {verdict.counterexample}")
        return Trans.UNSOUND
    return Trans.SOUND


async def _stage_split(state: ProverState, agent) -> Trans:
    cwd = _resolve(agent)
    if state.depth > 0 and verify_split_complete(cwd, state.workspace):
        return Trans.SPLIT_DONE

    # Use splitter agent in verified loop
    from .po_agents import run_splitter
    outcome = await run_splitter(agent, state.workspace, f"{state.workspace}/Stub.lean")
    if outcome.success:
        return Trans.SPLIT_DONE
    if verify_file_exists(cwd, f"{state.workspace}/Stub/Def.lean"):
        return Trans.SPLIT_DONE
    return Trans.SPLIT_FAILED


async def _stage_prove_direct(state: ProverState, agent) -> Trans:
    """Direct proof attempt → extract sorries as children if any remain.

    Flow:
    1. proof_writer attempts the theorem
    2. If sorry-free → PROVED (go to ASSEMBLE)
    3. If broken (doesn't compile) or bare sorry (no progress) → NO_PROGRESS (go to RETRY)
    4. If has sorries but structural progress → extract each sorry into
       decomposed/lemma_helper_<name>.lean → HAS_CHILDREN (go to CHILD_POS)
    """
    cwd = _resolve(agent)
    stub_rel = f"{state.workspace}/Stub.lean"
    tools = get_lean_tools()

    # Save backup for comparison and revert
    backup = cwd / f"{stub_rel}.bak"
    shutil.copy2(cwd / stub_rel, backup)

    # Also keep Stub.clean.lean for "no progress" detection
    stub_clean = cwd / state.workspace / "Stub.clean.lean"
    if not stub_clean.exists():
        shutil.copy2(cwd / stub_rel, stub_clean)

    sorry_ct = count_sorries(cwd, stub_rel)
    turns = WRITER_EXTENDED_TURNS if sorry_ct <= 2 else WRITER_MAX_TURNS
    rounds = 3 if sorry_ct <= 2 else 2
    action = _build_writer_action(sorry_ct)

    # Acquire global semaphore for proof_writer
    sem = _get_writer_semaphore()
    async with sem:
        await run_proof_writer(
            agent, state.workspace, stub_rel, action,
            max_turns=turns, max_rounds=rounds,
        )

        # After main attempt: check if main theorem body still has sorry.
        # If yes, push proof_writer to factor remaining sorries into named helpers.
        if tools.has_sorry(stub_rel):
            split = tools.split_theorems(stub_rel)
            if not split.error:
                # Find the main theorem (last one, or the one matching theorem_name)
                main_block = split.blocks[-1] if split.blocks else None
                if main_block and main_block.has_sorry:
                    await agent._emit("message",
                        "[PO] Main theorem still has sorry — pushing to factor into helpers")
                    await run_proof_writer(
                        agent, state.workspace, stub_rel,
                        (
                            "CRITICAL: The main theorem's proof body still contains `sorry`. "
                            "You MUST factor each remaining sorry into a named helper theorem:\n"
                            "  theorem helper_<descriptive_name> : <exact_goal_type> := by sorry\n"
                            "Then use `exact helper_<name>` at the sorry position in the main proof.\n"
                            "The main theorem's proof body must have NO sorry — only helper theorems can.\n"
                            "Use lean_goal at each sorry to get the exact type for the helper."
                        ),
                        max_turns=WRITER_MAX_TURNS, max_rounds=2,
                    )

    # ── Check result ──

    # Axiom check
    axiom_check = tools.check_axioms(stub_rel)
    if axiom_check.has_axiom:
        shutil.copy2(backup, cwd / stub_rel)
        backup.unlink(missing_ok=True)
        state.last_failure_details = f"Proof uses axiom: {axiom_check.axiom_names}"
        return Trans.NO_PROGRESS

    # Sorry-free = fully proved
    if not tools.has_sorry(stub_rel):
        backup.unlink(missing_ok=True)
        await agent._emit("message", "[PO] Direct proof succeeded ✅")
        return Trans.PROVED

    # Compilation check
    compile_result = tools.check_compiles(stub_rel)
    if not compile_result.success:
        shutil.copy2(backup, cwd / stub_rel)
        backup.unlink(missing_ok=True)
        await agent._emit("message", "[PO] Proof broke compilation — reverted")
        state.last_failure_details = "Direct attempt broke compilation"
        return Trans.NO_PROGRESS

    # ── Check if file is unchanged (byte-equal = no progress) ──
    stub_clean_path = cwd / state.workspace / "Stub.clean.lean"
    if stub_clean_path.exists():
        if (cwd / stub_rel).read_text().strip() == stub_clean_path.read_text().strip():
            shutil.copy2(backup, cwd / stub_rel)
            backup.unlink(missing_ok=True)
            await agent._emit("message", "[PO] No progress — file unchanged from original")
            state.last_failure_details = "Direct attempt made no changes"
            return Trans.NO_PROGRESS

    # ── Check if main theorem is sorry-free (only helpers have sorry) ──
    split = tools.split_theorems(stub_rel)
    if split.error or not split.blocks:
        backup.unlink(missing_ok=True)
        state.last_failure_details = "Could not parse theorem blocks"
        return Trans.NO_PROGRESS

    main_block = split.blocks[-1]  # main theorem is typically last
    sorry_helpers = [b for b in split.blocks[:-1] if b.has_sorry]

    if main_block.has_sorry:
        # Main theorem still has sorry in its body — proof_writer couldn't factor it out
        backup.unlink(missing_ok=True)
        state.last_failure_details = (
            "Main theorem body still has sorry (not factored into helpers). "
            "Needs decomposition.")
        return Trans.NO_PROGRESS

    if not sorry_helpers:
        # Main theorem proved AND no helpers with sorry — shouldn't reach here
        # (we already checked has_sorry above) but handle gracefully
        backup.unlink(missing_ok=True)
        await agent._emit("message", "[PO] Direct proof succeeded ✅")
        return Trans.PROVED

    # ── Main theorem is sorry-free, helpers have sorry → EXTRACT ──
    await agent._emit("message",
        f"[PO] Main theorem proved! {len(sorry_helpers)} helpers need proving → extracting")

    decomposed_dir = cwd / state.workspace / "decomposed"
    decomposed_dir.mkdir(parents=True, exist_ok=True)

    extract_result = tools.extract_sorry_theorems(stub_rel,
        output_dir=f"{state.workspace}/decomposed")

    if extract_result.created_files:
        state.decomposed_files = extract_result.created_files
        await agent._emit("message",
            f"[PO] Extracted {len(extract_result.created_files)} helpers → spawning child POs")
        backup.unlink(missing_ok=True)
        return Trans.HAS_CHILDREN

    # Extraction failed (compilation issue with extracted files)
    backup.unlink(missing_ok=True)
    state.last_failure_details = f"Extraction failed: {extract_result.error or 'unknown'}"
    return Trans.NO_PROGRESS


async def _stage_decompose(state: ProverState, agent) -> Trans:
    """Decomposer decides: direct attempt or decompose into sub-goals.

    At max recursion depth, forces direct (no further decomposition).
    Otherwise, decomposer agent decides based on theorem complexity.
    """
    cwd = _resolve(agent)
    tools = get_lean_tools()
    stub_rel = f"{state.workspace}/Stub.lean"

    # Already proved? (can happen on resume)
    if not tools.has_sorry(stub_rel):
        return Trans.DIRECT

    # At max depth: always direct (no further decomposition)
    if state.depth >= MAX_RECURSION_DEPTH:
        await agent._emit("message", f"[PO] Max depth ({MAX_RECURSION_DEPTH}) — forcing direct attempt")
        return Trans.DIRECT

    decomposer = await _get_internal(agent, "decomposer")

    msg = (f"Decompose theorem: {state.theorem_name}\nFile: {state.workspace}/Stub.lean\n"
           f"Write each sub-goal using write_decomposed_lemma tool.\n"
           f"RULE: Each file must contain EXACTLY ONE theorem with sorry.\n"
           f"RULE: Must create at least 2 sub-goals (or say strategy='direct' if simple).\n")
    if state.attempt > 0:
        msg += (f"Attempt {state.attempt + 1}/{MAX_RETRIES}. Previous: {state.last_failure_details}\n"
                f"Try a DIFFERENT decomposition strategy.\n")
    msg += f"Read the file, use lean_goal at the sorry, ask SearchAgent about types. Decide strategy.\n"

    output = await _get_decomposition(decomposer, msg, state, agent)
    if output is None:
        state.last_failure_details = "Decomposer produced no output"
        return Trans.NEEDS_RETRY
    if output.strategy == "direct":
        await agent._emit("message", "[PO] Decomposer chose: direct attempt")
        return Trans.DIRECT

    # Collect files from decomposed/ (decomposer wrote them via write_decomposed_lemma)
    decomposed_dir = cwd / state.workspace / "decomposed"
    if not decomposed_dir.exists() or not list(decomposed_dir.glob("*.lean")):
        state.last_failure_details = "No files in decomposed/ after decomposition"
        return Trans.NEEDS_RETRY

    state.decomposed_files = [
        f"{state.workspace}/decomposed/{f.name}"
        for f in decomposed_dir.glob("*.lean")
    ]

    # Must have at least 2 sub-goals (otherwise decomposition is pointless)
    if len(state.decomposed_files) < 2:
        state.last_failure_details = (
            f"Decomposition produced only {len(state.decomposed_files)} sub-goal(s). "
            f"Must produce at least 2. Try splitting into more independent parts.")
        return Trans.NEEDS_RETRY

    # Verify all files with tools (axiom check)
    tools = get_lean_tools()
    for f in state.decomposed_files:
        axiom_check = tools.check_axioms(f)
        if axiom_check.has_axiom:
            state.last_failure_details = f"{Path(f).name} contains axiom: {axiom_check.axiom_names}"
            return Trans.NEEDS_RETRY

    await agent._emit("message", f"[PO] Decomposed into {len(state.decomposed_files)} sub-goals")
    await swarm_checkpoint(agent, f"decomposed:{len(state.decomposed_files)}")
    return Trans.DECOMPOSED


async def _stage_sketch(state: ProverState, agent) -> Trans:
    """Sketch: wire decomposed lemmas together in Stub.lean."""
    cwd = _resolve(agent)
    decomposer = await _get_internal(agent, "decomposer")

    stub_path = cwd / state.workspace / "Stub.lean"
    backup = cwd / state.workspace / "Stub.clean.lean"
    if not backup.exists():
        shutil.copy2(stub_path, backup)

    for attempt in range(3):
        shutil.copy2(backup, stub_path)

        # Get proof sketch from decomposer's last output
        proof_sketch = getattr(decomposer, '_last_sketch', '') or "(combine sub-goals)"

        result = await run_sketcher(
            agent, state.workspace, f"{state.workspace}/Stub.lean",
            state.theorem_name, state.decomposed_files, proof_sketch,
        )

        if result and result.success:
            # Verify with tools
            tools = get_lean_tools()
            bad = tools.check_dag(f"{state.workspace}/Stub.lean",
                                  state.workspace.replace("/", "."))
            if not bad:
                # Check for unused imports: remove each decomposed import one-by-one
                # and see if Stub.lean still compiles. Unused = spurious decomposition.
                unused = await _find_unused_decomposed_imports(
                    cwd, state.workspace, state.decomposed_files, tools)
                if unused:
                    # Report back to decomposer and retry
                    shutil.copy2(backup, stub_path)
                    unused_names = [Path(f).stem for f in unused]
                    await agent._emit("message",
                        f"[PO] Sketch uses only {len(state.decomposed_files) - len(unused)}/{len(state.decomposed_files)} lemmas. "
                        f"Unused: {unused_names}")
                    # Remove unused files and ask decomposer to redo
                    for f in unused:
                        (cwd / f).unlink(missing_ok=True)
                    state.decomposed_files = [f for f in state.decomposed_files if f not in unused]
                    if len(state.decomposed_files) < 2:
                        state.last_failure_details = (
                            f"After removing unused lemmas ({unused_names}), only "
                            f"{len(state.decomposed_files)} remain. Need at least 2.")
                        return Trans.SKETCH_FAILED
                    # Retry sketch with the pruned set
                    continue
                await agent._emit("message", "[PO] Sketch verified ✅ (all lemmas used)")
                return Trans.SKETCH_OK
            shutil.copy2(backup, stub_path)
            await agent._emit("message", f"[PO] Sketch DAG violation: {bad}")
        else:
            shutil.copy2(backup, stub_path)
            reason = result.blocking_reason if result else "no output"
            await agent._emit("message", f"[PO] Sketch failed: {reason}")

        if attempt >= 2:
            break

        # Ask decomposer to revise
        await decomposer.run_ai(
            inp=f"Sketch failed: {reason}. Revise decomposition.",
            result_type=DecomposeResult, max_turns=DECOMPOSER_MAX_TURNS)

    state.last_failure_details = "Sketch could not wire lemmas together"
    return Trans.SKETCH_FAILED


async def _stage_child_cea(state: ProverState, agent) -> Trans:
    """Parallel CEA on all decomposed lemma files."""
    await agent._emit("message", f"[PO] CEA on {len(state.decomposed_files)} lemmas...")

    sem = asyncio.Semaphore(MAX_CONCURRENT_WRITERS)
    unsound = []

    async def _check(f: str):
        async with sem:
            v = await run_cea(agent, state.workspace, f, Path(f).stem)
            if v and not v.sound and v.confidence == "high":
                unsound.append(f)
                await agent._emit("message", f"[PO] CEA: {Path(f).name} UNSOUND")

    await asyncio.gather(*[_check(f) for f in state.decomposed_files])

    if unsound:
        state.last_failure_details = f"CEA rejected: {[Path(f).name for f in unsound]}"
        return Trans.SOME_UNSOUND

    await agent._emit("message", "[PO] All lemmas sound ✅")
    return Trans.ALL_SOUND


async def _stage_refactor(state: ProverState, agent) -> Trans:
    """Enforce one-sorry-per-file. Uses tools, no agents."""
    cwd = _resolve(agent)
    tools = get_lean_tools()

    # Scan decomposed/ and refactor multi-sorry files
    decomposed_dir = cwd / state.workspace / "decomposed"
    if not decomposed_dir.exists():
        return Trans.ALL_PROVED

    sorry_files = []
    for lean_file in decomposed_dir.glob("*.lean"):
        rel = f"{state.workspace}/decomposed/{lean_file.name}"
        if tools.is_proved(rel):
            if rel not in state.proved_files:
                state.proved_files.append(rel)
            continue

        # Check if file has multiple sorry theorems → extract
        split = tools.split_theorems(rel)
        if split.error:
            continue
        sorry_blocks = [b for b in split.blocks if b.has_sorry]

        if len(sorry_blocks) > 1:
            # Refactor: extract each sorry theorem into its own file
            result = tools.extract_sorry_theorems(rel,
                output_dir=f"{state.workspace}/decomposed")
            if result.created_files:
                await agent._emit("message",
                    f"[PO] Refactored {Path(rel).name}: extracted {len(result.created_files)} files")
                sorry_files.extend(result.created_files)
            else:
                sorry_files.append(rel)
        else:
            sorry_files.append(rel)

    # Update decomposed_files list
    state.decomposed_files = [
        f"{state.workspace}/decomposed/{f.name}"
        for f in decomposed_dir.glob("*.lean")
        if f"{state.workspace}/decomposed/{f.name}" not in state.proved_files
    ]

    if not state.decomposed_files:
        return Trans.ALL_PROVED

    await agent._emit("message", f"[PO] Refactor done: {len(state.decomposed_files)} files need proving")
    return Trans.HAS_CHILDREN


async def _stage_child_pos(state: ProverState, agent) -> Trans:
    """Parallel child POs for all sorry files in decomposed/.

    Before spawning, checks each child's po_checkpoint.json:
    - stage=done → already proved, skip
    - stage=other → resume from checkpoint (child will pick up where it left off)
    - no checkpoint → fresh start
    """
    cwd = _resolve(agent)
    remaining = [f for f in state.decomposed_files if f not in state.proved_files]

    if not remaining:
        return Trans.ALL_PROVED

    # Check which children already completed (from prior run/checkpoint)
    import json as _json
    to_spawn = []
    for lemma_file in remaining:
        child_workspace = str(Path(lemma_file).parent / Path(lemma_file).stem)
        child_cp = cwd / child_workspace / "po_checkpoint.json"
        if child_cp.exists():
            try:
                cp_data = _json.loads(child_cp.read_text())
                if cp_data.get("stage") == "done":
                    state.proved_files.append(lemma_file)
                    await agent._emit("message", f"[PO] ✅ {Path(lemma_file).name}: already proved (from checkpoint)")
                    write_checkpoint(cwd, state)
                    continue
            except (ValueError, KeyError):
                pass
        to_spawn.append(lemma_file)

    if not to_spawn:
        return Trans.ALL_PROVED

    await agent._emit("message", f"[PO] Running {len(to_spawn)} child POs (sequential, depth={state.depth + 1})")

    failed = []

    for lemma_file in to_spawn:
        child_workspace = setup_child_workspace(cwd, lemma_file, state.workspace)

        # Check if child has a checkpoint to resume from
        child_cp = cwd / child_workspace / "po_checkpoint.json"
        if child_cp.exists():
            await agent._emit("message", f"[PO] Resuming child: {Path(lemma_file).name}")

        result = await run_child_po(agent, child_workspace, lemma_file, state.depth + 1)

        if result and result.get("stage") == "done":
            state.proved_files.append(lemma_file)
            await agent._emit("message", f"[PO] ✅ Child proved: {Path(lemma_file).name}")
            write_checkpoint(cwd, state)
            await swarm_checkpoint(agent, f"child_proved:{Path(lemma_file).name}")
        else:
            reason = result.get("details", "unknown") if result else "no output"
            failed.append((lemma_file, reason))
            await agent._emit("message", f"[PO] ❌ Child failed: {Path(lemma_file).name}")

    if failed:
        state.last_failure_details = f"{len(failed)} children failed: {[Path(f).name for f, _ in failed[:3]]}"
        return Trans.CHILD_FAILED

    return Trans.ALL_PROVED


async def _stage_assemble(state: ProverState, agent) -> Trans:
    """Merge Def.lean bottom-up and rewrite imports. No file merging/inlining.

    Strategy:
    - Child workspaces stay intact (decomposed/ files keep their own imports)
    - Each child's local Def.lean gets merged INTO the top-level Def.lean
    - All imports of local Def.lean are rewritten to point to top-level Def.lean
    - This is done bottom-up: deepest children first, then their parents
    - Files keep their inter-dependencies (decomposed imports stay valid via Lean module paths)

    After assembly: top-level Stub.lean should compile sorry-free because
    all decomposed lemmas are now proved and their Def.lean contents are
    in the top-level Def.lean.
    """
    cwd = _resolve(agent)
    tools = get_lean_tools()
    top_module = state.workspace.replace("/", ".")
    top_def = cwd / state.workspace / "Stub" / "Def.lean"

    if not top_def.exists():
        state.last_failure_details = "Top-level Stub/Def.lean missing"
        return Trans.FAILED

    # Step 1: Copy each proved child's Stub.lean back to the parent's lemma file.
    # This replaces the sorry version with the proved version.
    for f in state.proved_files:
        lemma_path = Path(f)
        child_workspace = lemma_path.parent / lemma_path.stem
        child_stub = cwd / child_workspace / "Stub.lean"
        if child_stub.exists():
            shutil.copy2(child_stub, cwd / f)
            await agent._emit("message", f"[PO] Assembled: {lemma_path.name} ← child Stub.lean")

    top_def_content = top_def.read_text()

    # Step 2: Merge all child Def.lean into top-level (bottom-up by path depth)
    child_defs = sorted(
        (cwd / state.workspace).rglob("Stub/Def.lean"),
        key=lambda p: len(p.parts),
        reverse=True,  # deepest first
    )

    for child_def in child_defs:
        if child_def == top_def:
            continue
        child_content = child_def.read_text()
        if child_content.strip() == top_def_content.strip():
            continue  # identical — nothing to merge
        # Find new lines not already in top-level
        new_lines = [l for l in child_content.splitlines()
                     if l.strip() and l not in top_def_content and not l.strip().startswith("import ")]
        if new_lines:
            top_def_content = top_def_content.rstrip() + "\n" + "\n".join(new_lines) + "\n"
            top_def.write_text(top_def_content)
            await agent._emit("message",
                f"[PO] Merged {len(new_lines)} lines from {child_def.relative_to(cwd)}")

    # Rewrite all local Def.lean imports to point to top-level
    for lean_file in (cwd / state.workspace).rglob("*.lean"):
        if lean_file.name == "Def.lean":
            continue
        content = lean_file.read_text()
        rewritten = False
        new_lines = []
        for line in content.splitlines():
            stripped = line.strip()
            # Replace any import of a local Stub.Def with the top-level one
            if (stripped.startswith("import ") and
                    "Stub.Def" in stripped and
                    stripped != f"import {top_module}.Stub.Def"):
                new_lines.append(f"import {top_module}.Stub.Def")
                rewritten = True
            else:
                new_lines.append(line)
        if rewritten:
            lean_file.write_text("\n".join(new_lines) + "\n")

    # Verify: Stub.lean compiles sorry-free
    stub_rel = f"{state.workspace}/Stub.lean"
    compile_result = tools.check_compiles(stub_rel)

    if compile_result.success and not compile_result.has_sorry:
        await agent._emit("message", "[PO] Assembly verified ✅")
        return Trans.ASSEMBLED

    if not compile_result.success:
        state.last_failure_details = "Stub.lean doesn't compile after assembly"
    else:
        state.last_failure_details = "Stub.lean still has sorry after assembly"
    return Trans.FAILED


async def _stage_validate(state: ProverState, agent) -> Trans:
    """Final validation: tools check compile/sorry/axiom, then agent checks statement integrity."""
    stub_rel = f"{state.workspace}/Stub.lean"
    original_rel = f"{state.workspace}/_originals/Stub.lean"
    tools = get_lean_tools()

    # Fast deterministic checks first (no agent needed)
    compile_result = tools.check_compiles(stub_rel)
    if not compile_result.success:
        state.last_failure_details = "Validation: doesn't compile"
        return Trans.INVALID

    if tools.has_sorry(stub_rel):
        state.last_failure_details = "Validation: still has sorry"
        return Trans.INVALID

    axiom_check = tools.check_axioms(stub_rel)
    if axiom_check.has_axiom:
        state.last_failure_details = f"Validation: uses axiom ({axiom_check.axiom_names})"
        return Trans.INVALID

    # Statement integrity check via validator agent
    # (compares theorem signature between original and completed file)
    cwd = _resolve(agent)
    if (cwd / original_rel).exists():
        from .po_agents import run_validator
        v = await run_validator(agent, state.workspace, original_rel, stub_rel)
        if v and not v.statements_match:
            state.last_failure_details = "Validation: theorem signature changed"
            return Trans.INVALID

    await agent._emit("message", "[PO] Validation passed ✅")
    return Trans.VALID


async def _stage_retry(state: ProverState, agent) -> Trans:
    state.attempt += 1
    if state.attempt >= MAX_RETRIES:
        return Trans.MAX_RETRIES

    cwd = _resolve(agent)
    decomposed_dir = cwd / state.workspace / "decomposed"
    if decomposed_dir.exists():
        target = cwd / state.workspace / f"decomposed_attempt_{state.attempt}"
        if target.exists():
            shutil.rmtree(target)
        decomposed_dir.rename(target)
    decomposed_dir.mkdir(parents=True, exist_ok=True)

    stub_clean = cwd / state.workspace / "Stub.clean.lean"
    if stub_clean.exists():
        shutil.copy2(stub_clean, cwd / state.workspace / "Stub.lean")

    await _cleanup_internal(agent, "decomposer")

    # Preserve proved files
    preserved = list(state.proved_files)
    state.proved_files = preserved
    state.decomposed_files = []

    await agent._emit("message", f"[PO] Retry {state.attempt}/{MAX_RETRIES}, preserved {len(preserved)} proofs")
    return Trans.NEW_APPROACH


# ─── Handler registry ────────────────────────────────────────────────────────

HANDLERS: dict[Stage, Any] = {
    Stage.SOUNDNESS: _stage_soundness,
    Stage.SPLIT: _stage_split,
    Stage.DECOMPOSE: _stage_decompose,
    Stage.PROVE_DIRECT: _stage_prove_direct,
    Stage.SKETCH: _stage_sketch,
    Stage.CHILD_CEA: _stage_child_cea,
    Stage.REFACTOR: _stage_refactor,
    Stage.CHILD_POS: _stage_child_pos,
    Stage.ASSEMBLE: _stage_assemble,
    Stage.VALIDATE: _stage_validate,
    Stage.RETRY: _stage_retry,
}


# ─── Helpers ─────────────────────────────────────────────────────────────────

async def _find_unused_decomposed_imports(cwd: Path, workspace: str,
                                            decomposed_files: list[str], tools) -> list[str]:
    """After sketch succeeds, check which decomposed imports are actually needed.

    For each decomposed file, temporarily remove its import from Stub.lean and
    re-compile. If it still compiles → that lemma is unused (spurious decomposition).

    Returns list of unused file paths.
    """
    stub_path = cwd / workspace / "Stub.lean"
    original_content = stub_path.read_text()
    stub_rel = f"{workspace}/Stub.lean"
    unused = []

    for f in decomposed_files:
        # Build the import line for this file
        module_path = f.replace("/", ".").removesuffix(".lean")
        import_line = f"import {module_path}"

        # Remove this specific import
        lines = original_content.splitlines()
        filtered = [l for l in lines if l.strip() != import_line]
        if len(filtered) == len(lines):
            continue  # import line not found (shouldn't happen)

        stub_path.write_text("\n".join(filtered) + "\n")

        # Check if it still compiles without this import
        compile_result = tools.check_compiles(stub_rel)
        if compile_result.success:
            unused.append(f)

    # Restore original
    stub_path.write_text(original_content)
    return unused


def _resolve(agent) -> Path:
    return Path(agent._cwd) if agent._cwd else Path.cwd()


def _build_writer_action(sorry_count: int) -> str:
    if sorry_count <= 2:
        return (
            f"File has {sorry_count} sorry(s) — CLOSE to done.\n"
            "Try simple tactics first. Factor hard goals into helpers.\n"
            "Leave stubborn helpers with sorry."
        )
    return (
        "Write a proof. Structural sketch first, fill each sorry.\n"
        "Factor hard sub-goals into helpers. Leave stubborn ones with sorry."
    )


async def _get_decomposition(decomposer, msg, state, agent) -> DecomposeResult | None:
    result = await decomposer.run_ai(inp=msg, result_type=DecomposeResult, max_turns=DECOMPOSER_MAX_TURNS)
    output = result.output

    retries = 0
    while output is None and retries < 3:
        retries += 1
        result = await decomposer.run_ai(
            inp="Produce your StructuredOutput now.", result_type=DecomposeResult, max_turns=DECOMPOSER_MAX_TURNS)
        output = result.output

    # Fallback: check if files were written via the tool
    if output is None:
        cwd = _resolve(agent)
        decomposed_dir = cwd / state.workspace / "decomposed"
        if decomposed_dir.exists():
            files = list(decomposed_dir.glob("*.lean"))
            if files:
                output = DecomposeResult(
                    strategy="decompose",
                    sub_goals=[SubGoal(name=f.stem, filename=f"{state.workspace}/decomposed/{f.name}") for f in files],
                    proof_sketch="(from files)")

    if output:
        # Store sketch for later use by sketcher
        decomposer._last_sketch = output.proof_sketch

    await agent._emit("message",
        f"[PO] Decompose: {output.strategy if output else 'None'}, "
        f"{len(output.sub_goals) if output else 0} sub-goals")
    return output


async def _notify_parent(agent, state, message):
    try:
        await agent.channel_bus.send_to(f"{state.parent_agent}:messages",
                                         sender=agent.spec.name, payload=message)
    except Exception:
        pass


async def _get_internal(agent, which: str):
    """Get or create a persistent internal agent. On resume, reconnects to prior session."""
    attr = f"_po_{which}"
    attr_ctx = f"_po_{which}_ctx"
    if getattr(agent, attr, None) is None:
        state = getattr(agent, '_workflow_state', None)
        workspace = state.workspace if state else None

        # Check if we have a prior session to resume from checkpoint
        resume_session_id = None
        if state and state.internal_agents.get(which):
            prior_name = state.internal_agents[which]
            resume_session_id = _lookup_session_id(agent, prior_name)

        ctx = swarm_agent(f"po_{which}", swarm=agent.swarm, cwd=agent._cwd,
                          workspace=workspace, resume_session_id=resume_session_id)
        internal = await ctx.__aenter__()
        setattr(agent, attr_ctx, ctx)
        setattr(agent, attr, internal)

        # Store the new agent's name for future checkpoints
        if state:
            state.internal_agents[which] = internal.spec.name

    return getattr(agent, attr)


def _lookup_session_id(agent, agent_name: str) -> str | None:
    """Look up a session ID from the swarm checkpoint state.yaml."""
    import json as _json
    from pathlib import Path as _P

    # Try the latest checkpoint
    cp_dir = _P(agent._cwd or ".") / "StrataAgent" / "strataswarm" / "temp" / "checkpoints"
    if not cp_dir.exists():
        return None

    # Find latest checkpoint
    checkpoints = sorted(cp_dir.iterdir(), key=lambda p: p.name, reverse=True)
    if not checkpoints:
        return None

    state_file = checkpoints[0] / "state.yaml"
    if not state_file.exists():
        return None

    try:
        import yaml
        state = yaml.safe_load(state_file.read_text())
        return state.get("sessions", {}).get(agent_name)
    except Exception:
        return None


async def _cleanup_internal(agent, which: str):
    attr = f"_po_{which}"
    attr_ctx = f"_po_{which}_ctx"
    if getattr(agent, attr, None) is not None:
        ctx = getattr(agent, attr_ctx, None)
        if ctx:
            await ctx.__aexit__(None, None, None)
        setattr(agent, attr_ctx, None)
        setattr(agent, attr, None)
