"""Proof Orchestrator v3: Linear pipeline with progress guarantee.

Design:
- Sequential proving (no concurrent session explosion)
- Direct attempt first → refactor remaining → recurse on new lemmas
- Proof writer makes progress (sketch → fill → report)
- All original lemmas must close before recursing
- Recursion only on NEW lemmas from sorry goals
"""

from __future__ import annotations

import asyncio
import shutil
from dataclasses import dataclass, field
from enum import Enum
from pathlib import Path
from typing import Any, TypeVar

from .._helpers import swarm_agent
from .po_verify import (
    check_import_dag, verify_file_exists, verify_no_sorry, verify_has_sorry,
    count_sorries, verify_dag, verify_all_files_dag, is_bare_sorry,
    verify_split_complete,
)

T = TypeVar("T")

MAX_RETRIES = 3
MAX_PARALLEL_DIRECT = 3   # parallel proof_writers for direct attempts
MAX_PARALLEL_VALIDATORS = 5
WRITER_MAX_TURNS = 50
DECOMPOSER_MAX_TURNS = 100


# ─── Enums ────────────────────────────────────────────────────────────────────

class Stage(str, Enum):
    SOUNDNESS = "soundness"
    SPLIT = "split"
    DECOMPOSE = "decompose"
    PROVE_DIRECT = "prove_direct"
    CLOSE_REMAINING = "close_remaining"
    PROVE_RECURSIVE = "prove_recursive"
    VALIDATE = "validate"
    ASSEMBLE = "assemble"
    RETRY = "retry"
    DONE = "done"
    FAILED = "failed"


class Trans(str, Enum):
    SOUND = "sound"
    SKIPPED = "skipped"
    UNSOUND = "unsound"
    SPLIT_DONE = "split_done"
    SPLIT_FAILED = "split_failed"
    DECOMPOSED = "decomposed"
    SIMPLE_ENOUGH = "simple_enough"
    NEEDS_DECOMP = "needs_decomp"
    ALL_PROVED = "all_proved"
    SOME_REMAINING = "some_remaining"
    ALL_CLOSED = "all_closed"
    CANNOT_CLOSE = "cannot_close"
    CHILD_FAILED = "child_failed"
    VALID = "valid"
    INVALID = "invalid"
    ASSEMBLED = "assembled"
    FAILED = "failed"
    NEW_APPROACH = "new_approach"
    MAX_RETRIES = "max_retries"


TRANSITIONS: dict[tuple[Stage, Trans], Stage] = {
    (Stage.SOUNDNESS, Trans.SOUND):         Stage.SPLIT,
    (Stage.SOUNDNESS, Trans.SKIPPED):       Stage.SPLIT,
    (Stage.SOUNDNESS, Trans.UNSOUND):       Stage.FAILED,

    (Stage.SPLIT, Trans.SPLIT_DONE):        Stage.DECOMPOSE,
    (Stage.SPLIT, Trans.SPLIT_FAILED):      Stage.DECOMPOSE,

    (Stage.DECOMPOSE, Trans.DECOMPOSED):    Stage.PROVE_DIRECT,
    (Stage.DECOMPOSE, Trans.SIMPLE_ENOUGH): Stage.PROVE_DIRECT,
    (Stage.DECOMPOSE, Trans.NEEDS_DECOMP):  Stage.RETRY,

    (Stage.PROVE_DIRECT, Trans.ALL_PROVED):     Stage.ASSEMBLE,
    (Stage.PROVE_DIRECT, Trans.SOME_REMAINING): Stage.CLOSE_REMAINING,

    (Stage.CLOSE_REMAINING, Trans.ALL_CLOSED):    Stage.PROVE_RECURSIVE,
    (Stage.CLOSE_REMAINING, Trans.CANNOT_CLOSE):  Stage.RETRY,

    (Stage.PROVE_RECURSIVE, Trans.ALL_PROVED):    Stage.ASSEMBLE,
    (Stage.PROVE_RECURSIVE, Trans.CHILD_FAILED):  Stage.RETRY,

    (Stage.ASSEMBLE, Trans.ASSEMBLED):      Stage.VALIDATE,
    (Stage.ASSEMBLE, Trans.FAILED):         Stage.RETRY,

    (Stage.VALIDATE, Trans.VALID):          Stage.DONE,
    (Stage.VALIDATE, Trans.INVALID):        Stage.RETRY,

    (Stage.RETRY, Trans.NEW_APPROACH):      Stage.DECOMPOSE,
    (Stage.RETRY, Trans.MAX_RETRIES):       Stage.FAILED,
}


# ─── Structured output types ─────────────────────────────────────────────────

@dataclass
class Axiom:
    name: str = ""
    filename: str = ""
    description: str = ""
    depends_on: list[str] = field(default_factory=list)


@dataclass
class DecomposeResult:
    strategy: str = "decompose"
    axioms: list[Axiom] = field(default_factory=list)
    proof_sketch: str = ""
    reasoning: str = ""


@dataclass
class ProofResult:
    success: bool = False
    has_sorry: bool = True
    blocking_reason: str = ""


@dataclass
class SketchResult:
    success: bool = False
    blocking_reason: str = ""


@dataclass
class SorryGoal:
    file: str = ""
    line: int = 0
    goal: str = ""


@dataclass
class RefactorFindResult:
    sorries: list[SorryGoal] = field(default_factory=list)
    cannot_refactor: bool = False


@dataclass
class AxiomProposal:
    name: str = ""
    formalization: str = ""


@dataclass
class EditResult:
    success: bool = False
    error: str = ""


@dataclass
class ValidationResult:
    compiles: bool = False
    has_sorry: bool = True
    statements_match: bool = False


@dataclass
class VerifyResult:
    compiles: bool = False
    has_sorry: bool = True


@dataclass
class SoundnessVerdict:
    sound: bool = False
    confidence: str = "medium"
    counterexample: str | None = None
    reasoning: str | None = None


# ─── State ────────────────────────────────────────────────────────────────────

@dataclass
class ProverState:
    stage: Stage = Stage.SOUNDNESS
    theorem_file: str = ""
    theorem_name: str = ""
    workspace: str = ""
    skip_soundness: bool = False

    # Lemma tracking
    all_lemmas: list[str] = field(default_factory=list)      # original decomposed lemmas
    proved_lemmas: list[str] = field(default_factory=list)   # fully proved (no sorry)
    closed_lemmas: list[str] = field(default_factory=list)   # closed by new theorems
    new_lemmas: list[str] = field(default_factory=list)      # from close_remaining (to prove recursively)

    # Meta
    attempt: int = 0
    parent_agent: str = "TaskManager"
    failure_reason: str = ""
    last_failure_details: str = ""


# ─── Main loop ────────────────────────────────────────────────────────────────

async def run_workflow(agent, inp: Any, result_type: type[T] | None = None):
    from .._types import AgentResult, AgentStatus

    await agent._emit("status_change", "running")

    # Parse input
    if isinstance(inp, dict):
        theorem_file = inp.get("theorem_file", "")
        theorem_name = inp.get("theorem_name", "")
        workspace_rel = inp.get("workspace", "")
        skip_soundness = inp.get("skip_soundness", False)
        parent_agent = inp.get("parent_agent", "TaskManager")
    elif isinstance(inp, str):
        theorem_file = inp
        theorem_name = ""
        workspace_rel = ""
        skip_soundness = False
        parent_agent = "TaskManager"
    else:
        theorem_file = str(inp)
        theorem_name = ""
        workspace_rel = ""
        skip_soundness = False
        parent_agent = "TaskManager"

    cwd = Path(agent._cwd) if agent._cwd else Path.cwd()

    if not workspace_rel:
        await agent._emit("message", "[PO] ERROR: No workspace provided.")
        result = AgentResult(name=agent.spec.name, status=AgentStatus.FAILED)
        result.output = {"stage": "failed", "error": "no_workspace"}
        return result

    workspace_abs = cwd / workspace_rel
    workspace_abs.mkdir(parents=True, exist_ok=True)

    # Stub.lean must exist
    stub_file = workspace_abs / "Stub.lean"
    if not stub_file.exists():
        await agent._emit("message", f"[PO] ERROR: No Stub.lean in {workspace_rel}")
        await _notify_parent(agent, ProverState(parent_agent=parent_agent),
                             f"Failed: Stub.lean not found in {workspace_rel}")
        result = AgentResult(name=agent.spec.name, status=AgentStatus.FAILED)
        result.output = {"stage": "failed", "error": "stub_not_found"}
        return result

    # Save original
    originals_dir = workspace_abs / "_originals"
    originals_dir.mkdir(exist_ok=True)
    if not (originals_dir / "Stub.lean").exists():
        shutil.copy2(stub_file, originals_dir / "Stub.lean")

    state = ProverState(
        stage=Stage.SOUNDNESS,
        theorem_file=theorem_file,
        theorem_name=theorem_name,
        workspace=workspace_rel,
        skip_soundness=skip_soundness,
        parent_agent=parent_agent,
    )
    agent._workflow_state = state

    await agent._emit("message", f"[PO] Starting: {theorem_name} in {workspace_rel}")

    while not agent.cancellation.is_cancelled:
        if state.stage in (Stage.DONE, Stage.FAILED):
            break

        try:
            handler = HANDLERS[state.stage]
            transition = await handler(state, agent)

            next_stage = TRANSITIONS.get((state.stage, transition))
            if next_stage is None:
                await agent._emit("message", f"[PO] Bad transition: ({state.stage.value}, {transition.value})")
                next_stage = Stage.RETRY

            await agent._emit("state_transition", {
                "from": state.stage.value, "transition": transition.value, "to": next_stage.value,
            })
            await agent._emit("message",
                f"[PO] {state.stage.value} →{transition.value}→ {next_stage.value}")

            state.stage = next_stage
            agent._workflow_state = state
            _write_progress(_resolve(agent), state)

        except Exception as e:
            await agent._emit("message", f"[PO] Error in {state.stage.value}: {e}")
            state.stage = Stage.RETRY
            agent._workflow_state = state

    # Notify parent
    status_msg = f"Proof {'complete' if state.stage == Stage.DONE else 'failed'}: {theorem_file}"
    await _notify_parent(agent, state, status_msg)

    # Cleanup
    await _cleanup_internal(agent, "decomposer")

    result = AgentResult(name=agent.spec.name, status=AgentStatus.COMPLETED)
    result.output = {
        "stage": state.stage.value,
        "theorem_file": theorem_file,
        "attempts": state.attempt,
        "failure_reason": state.failure_reason,
        "details": state.last_failure_details,
    }
    return result


# ─── Stage: soundness ─────────────────────────────────────────────────────────

async def _stage_soundness(state: ProverState, agent) -> Trans:
    if state.skip_soundness:
        await agent._emit("message", "[PO] Soundness skipped.")
        return Trans.SKIPPED

    await agent._emit("message", "[PO] Running CEA soundness check...")
    verdict = await _run_cea(agent, state.workspace, f"{state.workspace}/Stub.lean", state.theorem_name)

    if verdict and not verdict.sound:
        state.failure_reason = "unsound"
        await agent._emit("message", f"[PO] UNSOUND: {verdict.counterexample}")
        await _notify_parent(agent, state, f"UNSOUND: {verdict.counterexample}")
        return Trans.UNSOUND

    await agent._emit("message", f"[PO] Sound ({verdict.confidence if verdict else '?'}).")
    return Trans.SOUND


# ─── Stage: split ─────────────────────────────────────────────────────────────

async def _stage_split(state: ProverState, agent) -> Trans:
    await agent._emit("message", "[PO] Splitting defs from theorems...")

    @dataclass
    class _SplitResult:
        success: bool = False
        error: str = ""

    async with swarm_agent("po_splitter", swarm=agent.swarm, cwd=agent._cwd, workspace=state.workspace) as splitter:
        result = await splitter.run(
            inp={
                "file": f"{state.workspace}/Stub.lean",
                "workspace": state.workspace,
                "action": "Split into Stub/Def.lean (definitions) and Stub.lean (theorem only, imports defs)",
            },
            result_type=_SplitResult,
        )

    # Verify split programmatically
    cwd = _resolve(agent)
    if verify_split_complete(cwd, state.workspace):
        await agent._emit("message", "[PO] Split verified: Stub/Def.lean exists + Stub.lean imports it ✅")
        return Trans.SPLIT_DONE

    # Partial success: Def.lean exists but import might be missing
    if verify_file_exists(cwd, f"{state.workspace}/Stub/Def.lean"):
        await agent._emit("message", "[PO] Split: Def.lean exists (import may be incomplete) — proceeding")
        return Trans.SPLIT_DONE

    await agent._emit("message", f"[PO] Split failed — proceeding anyway.")
    return Trans.SPLIT_FAILED


# ─── Stage: decompose (includes sketch check loop) ───────────────────────────

async def _stage_decompose(state: ProverState, agent) -> Trans:
    """Decompose + verify sketch. Loops if sketch fails (up to 3 revisions)."""
    decomposer = await _get_internal(agent, "decomposer")

    decomposed_path = f"{state.workspace}/decomposed"
    msg = f"Decompose theorem: {state.theorem_name}\nFile: {state.workspace}/Stub.lean\n"
    msg += f"Write lemma files to: {decomposed_path}/lemma_<n>_<name>.lean\n"
    if state.attempt > 0:
        msg += f"Attempt {state.attempt + 1}/{MAX_RETRIES}. Previous approach failed.\n"
        if state.last_failure_details:
            msg += f"Details: {state.last_failure_details}\n"
        msg += f"The decomposed/ directory has been CLEARED. Write completely NEW files there.\n"
        msg += f"Do NOT reference old filenames — they no longer exist.\n"
    msg += f"Read the file, use lean_goal at the sorry, and decide strategy.\n"
    msg += f"IMPORTANT: Files MUST go to {decomposed_path}/ — NOT any other decomposed/ folder."

    # Get decomposition
    decompose_output = await _get_decomposition(decomposer, msg, state, agent)
    if decompose_output is None:
        if state.attempt > 0:
            # Retry with no decomposition = decomposer is dead → fail
            state.last_failure_details = "Decomposer produced no output on retry"
            return Trans.NEEDS_DECOMP
        return Trans.SIMPLE_ENOUGH

    if decompose_output.strategy == "direct":
        await agent._emit("message", f"[PO] Strategy: direct. Sketch: {decompose_output.proof_sketch[:150]}")
        return Trans.SIMPLE_ENOUGH

    # Collect lemma files from decomposed/
    cwd = _resolve(agent)
    originals_dir = cwd / state.workspace / "_originals"
    originals_dir.mkdir(exist_ok=True)
    state.all_lemmas = []

    for axiom in (decompose_output.axioms or []):
        src = cwd / axiom.filename
        if src.exists():
            # Verify the file has no DAG violations
            bad = check_import_dag(src, state.workspace)
            if bad:
                await agent._emit("message", f"[PO] Warning: {axiom.filename} has bad imports {bad} — skipping")
                continue
            state.all_lemmas.append(axiom.filename)
            shutil.copy2(src, originals_dir / Path(axiom.filename).name)
        else:
            await agent._emit("message", f"[PO] Warning: {axiom.filename} not found")

    if not state.all_lemmas:
        return Trans.SIMPLE_ENOUGH

    # Deduplicate
    state.all_lemmas = list(dict.fromkeys(state.all_lemmas))
    await agent._emit("message", f"[PO] Decomposed: {len(state.all_lemmas)} lemmas")

    # Sketch check: can Stub.lean be proved using these lemmas?
    cwd = _resolve(agent)
    sketch_ok = await _verify_sketch(state, agent, decomposer, decompose_output)
    if sketch_ok:
        return Trans.DECOMPOSED

    # All sketch attempts failed
    state.all_lemmas = []
    state.last_failure_details = "Sketch proof couldn't use the decomposed lemmas"
    return Trans.NEEDS_DECOMP


# ─── Stage: prove_direct (parallel, bounded proof_writers) ────────────────────

async def _stage_prove_direct(state: ProverState, agent) -> Trans:
    """Proof_writer attempts each lemma. Parallel but bounded. Partial success OK."""
    to_prove = list(dict.fromkeys(state.all_lemmas)) if state.all_lemmas else [f"{state.workspace}/Stub.lean"]
    await agent._emit("message", f"[PO] Direct proving {len(to_prove)} lemmas...")

    # Topological sort by dependencies (if available)
    # For now: just prove in order (decomposer gives dependency-ordered list)

    semaphore = asyncio.Semaphore(MAX_PARALLEL_DIRECT)
    proved = []
    has_sorry = []

    cwd = _resolve(agent)
    originals_dir = cwd / state.workspace / "_originals"

    async def _attempt_one(lemma_file: str):
        async with semaphore:
            # Backup before proof_writer touches it
            backup = cwd / f"{lemma_file}.bak"
            shutil.copy2(cwd / lemma_file, backup)

            result = await _run_proof_writer(agent, state.workspace, lemma_file, state.theorem_name)

            # DAG check: no imports from parent/sibling
            bad_imports = check_import_dag(cwd / lemma_file, state.workspace)
            if bad_imports:
                await agent._emit("message", f"[PO] ⚠️ {Path(lemma_file).name}: bad imports {bad_imports} — reverting")
                shutil.copy2(backup, cwd / lemma_file)
                has_sorry.append(lemma_file)
            else:
                # Programmatic check: does file actually contain "sorry"?
                file_content = (cwd / lemma_file).read_text()
                file_has_sorry = "sorry" in file_content

                if not file_has_sorry:
                    # Fully proved regardless of what proof_writer reported
                    proved.append(lemma_file)
                    await agent._emit("message", f"[PO] ✅ Proved: {Path(lemma_file).name}")
                else:
                    # Verify the file still compiles (only sorry warnings, no errors)
                    v = await _run_compilation_check(agent, state.workspace, lemma_file)
                    if v and not v.compiles:
                        await agent._emit("message", f"[PO] ⚠️ {Path(lemma_file).name}: broken after proof attempt — reverting")
                        shutil.copy2(backup, cwd / lemma_file)
                        has_sorry.append(lemma_file)
                    else:
                        has_sorry.append(lemma_file)
                        await agent._emit("message", f"[PO] ⏳ Sorry remaining: {Path(lemma_file).name}")

            backup.unlink(missing_ok=True)

    await asyncio.gather(*[_attempt_one(f) for f in to_prove])

    state.proved_lemmas = proved
    await agent._emit("message", f"[PO] Direct: {len(proved)}/{len(to_prove)} proved")

    if len(proved) == len(to_prove):
        return Trans.ALL_PROVED
    return Trans.SOME_REMAINING


# ─── Stage: close_remaining (categorize by sorry count) ──────────────────────

MAX_CLOSABLE_SORRIES = 2  # Files with ≤ this many sorries get close_remaining treatment


async def _stage_close_remaining(state: ProverState, agent) -> Trans:
    """Categorize remaining files by sorry count:
    - ≤ MAX_CLOSABLE_SORRIES: try to close with new theorems (must succeed or decomp is bad)
    - > MAX_CLOSABLE_SORRIES: send directly to prove_recursive (need deeper decomposition)
    """
    remaining = [f for f in state.all_lemmas if f not in state.proved_lemmas]
    if not remaining:
        return Trans.ALL_CLOSED

    await agent._emit("message", f"[PO] Categorizing {len(remaining)} remaining lemmas...")
    cwd = _resolve(agent)
    originals_dir = cwd / state.workspace / "_originals"

    # Categorize by sorry count and whether proof_writer made structural progress
    closable = []    # ≤ MAX_CLOSABLE_SORRIES + structural progress → try to close
    recursive = []   # > MAX_CLOSABLE_SORRIES or no progress → go straight to recursive

    for lemma_file in remaining:
        # Quick programmatic check: does the file actually contain "sorry"?
        if verify_no_sorry(cwd, lemma_file):
            state.proved_lemmas.append(lemma_file)
            await agent._emit("message", f"[PO] ✅ {Path(lemma_file).name} has no sorry — already proved!")
            continue

        # Check if bare sorry (no structural progress made)
        if is_bare_sorry(cwd, lemma_file):
            recursive.append(lemma_file)
            await agent._emit("message", f"[PO] {Path(lemma_file).name}: bare sorry (no progress) → needs recursive")
            continue

        sorry_count = count_sorries(cwd, lemma_file)

        if sorry_count <= MAX_CLOSABLE_SORRIES:
            closable.append(lemma_file)
            await agent._emit("message", f"[PO] {Path(lemma_file).name}: {sorry_count} sorries → will try to close")
        else:
            recursive.append(lemma_file)
            await agent._emit("message", f"[PO] {Path(lemma_file).name}: {sorry_count} sorries → needs recursive")

    # Files with > MAX_CLOSABLE_SORRIES go directly to new_lemmas for recursive proving
    state.new_lemmas.extend(recursive)

    # Try to close files with ≤ MAX_CLOSABLE_SORRIES
    for lemma_file in closable:
        await agent._emit("message", f"[PO] Closing: {Path(lemma_file).name}")

        # Find sorry goals (need agent for lean_hover_info)
        find_result = await _find_sorries(agent, state.workspace, lemma_file)
        if not find_result or not find_result.sorries:
            await agent._emit("message", f"[PO] ⚠️ Can't find sorry goals in {Path(lemma_file).name} — sending to recursive")
            state.new_lemmas.append(lemma_file)
            continue

        await agent._emit("message", f"[PO] Found {len(find_result.sorries)} sorry goals in {Path(lemma_file).name}")

        # Propose theorems for all sorries (fresh stateless agent)
        new_theorems = await _propose_theorems_for_goals(agent, state.workspace, find_result.sorries)

        if len(new_theorems) != len(find_result.sorries):
            await agent._emit("message",
                f"[PO] ❌ Can't propose theorems for {Path(lemma_file).name} — decomposition is bad")
            state.last_failure_details = (
                f"Cannot axiomatize sorries in {Path(lemma_file).name} "
                f"(only {len(new_theorems)}/{len(find_result.sorries)} proposed)")
            return Trans.CANNOT_CLOSE

        # Write new theorem files (prefix "helper_" to distinguish from decomposed lemmas)
        parent_stem = Path(lemma_file).stem
        new_files = []
        for i, (_, prop) in enumerate(new_theorems):
            path = _create_lemma_file(cwd, state.workspace, f"helper_{parent_stem}", len(state.new_lemmas) + i, prop.name, prop.formalization)
            new_files.append(path)
            shutil.copy2(cwd / path, originals_dir / Path(path).name)

        # Try to close: replace sorries with simple tactics
        backup = cwd / state.workspace / f"{Path(lemma_file).stem}.backup.lean"
        shutil.copy2(cwd / lemma_file, backup)

        closed = await _try_close_file(agent, state.workspace, lemma_file, new_theorems, new_files)

        if not closed:
            shutil.copy2(backup, cwd / lemma_file)
            backup.unlink(missing_ok=True)
            for f in new_files:
                (cwd / f).unlink(missing_ok=True)
            state.last_failure_details = f"Theorems don't close sorries in {Path(lemma_file).name} — decomposition is bad"
            return Trans.CANNOT_CLOSE

        # DAG check on the closed file
        bad = check_import_dag(cwd / lemma_file, state.workspace)
        if bad:
            shutil.copy2(backup, cwd / lemma_file)
            backup.unlink(missing_ok=True)
            for f in new_files:
                (cwd / f).unlink(missing_ok=True)
            state.last_failure_details = f"Closed file {Path(lemma_file).name} has bad imports: {bad}"
            return Trans.CANNOT_CLOSE

        backup.unlink(missing_ok=True)
        state.closed_lemmas.append(lemma_file)
        state.new_lemmas.extend(new_files)
        await agent._emit("message", f"[PO] ✅ Closed: {Path(lemma_file).name} (+{len(new_files)} new)")

    # Verify all closed files compile cleanly (no errors, sorry only in new lemma files)
    await agent._emit("message", "[PO] Verifying all closed files compile...")
    for lemma_file in state.closed_lemmas:
        v = await _run_compilation_check(agent, state.workspace, lemma_file)
        if v and not v.compiles:
            state.last_failure_details = f"Closed file {Path(lemma_file).name} doesn't compile after closure"
            await agent._emit("message", f"[PO] ❌ {Path(lemma_file).name} broken after closure — decomposition invalid")
            return Trans.CANNOT_CLOSE

    # Also verify Stub.lean still compiles (imports might have been affected)
    stub_rel = f"{state.workspace}/Stub.lean"
    v = await _run_compilation_check(agent, state.workspace, stub_rel)
    if v and not v.compiles:
        state.last_failure_details = "Stub.lean doesn't compile after closing lemmas"
        await agent._emit("message", "[PO] ❌ Stub.lean broken after closure — decomposition invalid")
        return Trans.CANNOT_CLOSE

    total_recursive = len(state.new_lemmas)
    await agent._emit("message",
        f"[PO] Close phase done. {len(state.closed_lemmas)} closed, {total_recursive} lemmas for recursive proving. All compile ✅")
    return Trans.ALL_CLOSED


# ─── Stage: prove_recursive (sequential child POs) ───────────────────────────

async def _stage_prove_recursive(state: ProverState, agent) -> Trans:
    """Sequential child PO for each new lemma. One at a time."""
    if not state.new_lemmas:
        return Trans.ALL_PROVED

    await agent._emit("message", f"[PO] Recursive proving {len(state.new_lemmas)} new lemmas (sequential)...")
    cwd = _resolve(agent)

    for lemma_file in state.new_lemmas:
        lemma_path = Path(lemma_file)
        child_workspace = f"{lemma_path.parent}/{lemma_path.stem}"
        (cwd / child_workspace).mkdir(parents=True, exist_ok=True)
        shutil.copy2(cwd / lemma_file, cwd / child_workspace / "Stub.lean")

        await agent._emit("message", f"[PO] Recursive: {lemma_path.name}...")

        result = await _run_child_po(agent, child_workspace, lemma_file)

        if result and result.get("stage") == "done":
            state.proved_lemmas.append(lemma_file)
            await agent._emit("message", f"[PO] ✅ Child proved: {lemma_path.name}")
        else:
            reason = result.get("details", "unknown") if result else "no output"
            state.last_failure_details = f"Child PO failed on {lemma_path.name}: {reason}"
            await agent._emit("message", f"[PO] ❌ Child failed: {lemma_path.name}")
            return Trans.CHILD_FAILED

    return Trans.ALL_PROVED


# ─── Stage: validate ──────────────────────────────────────────────────────────

async def _stage_validate(state: ProverState, agent) -> Trans:
    """Deep validation on all proved/closed files."""
    all_files = state.proved_lemmas + state.closed_lemmas
    if not all_files:
        # Direct attempt on Stub.lean — validate that
        all_files = [f"{state.workspace}/Stub.lean"]

    await agent._emit("message", f"[PO] Validating {len(all_files)} files...")
    cwd = _resolve(agent)
    originals_dir = cwd / state.workspace / "_originals"

    semaphore = asyncio.Semaphore(MAX_PARALLEL_VALIDATORS)
    issues = []

    async def _validate_one(f: str):
        original = originals_dir / Path(f).name
        if not original.exists():
            issues.append(f"No original for {Path(f).name}")
            return
        original_rel = f"{state.workspace}/_originals/{Path(f).name}"
        async with semaphore:
            v = await _run_validator(agent, state.workspace, original_rel, f)
            if v:
                if not v.compiles: issues.append(f"{Path(f).name}: doesn't compile")
                if v.has_sorry: issues.append(f"{Path(f).name}: has sorry")
                if not v.statements_match: issues.append(f"{Path(f).name}: statements changed")

    await asyncio.gather(*[_validate_one(f) for f in all_files])

    if not issues:
        await agent._emit("message", "[PO] Validation passed.")
        return Trans.VALID

    await agent._emit("message", f"[PO] Validation failed: {issues}")
    state.last_failure_details = f"Validation: {issues}"
    return Trans.INVALID


# ─── Stage: assemble ──────────────────────────────────────────────────────────

async def _stage_assemble(state: ProverState, agent) -> Trans:
    """Copy child proofs back, verify final Stub.lean."""
    cwd = _resolve(agent)
    await agent._emit("message", "[PO] Assembling...")

    # Copy child Stub.lean → parent lemma file (for recursively proved lemmas)
    for lemma_file in state.new_lemmas:
        if lemma_file in state.proved_lemmas:
            lemma_path = Path(lemma_file)
            child_stub = cwd / lemma_path.parent / lemma_path.stem / "Stub.lean"
            if child_stub.exists():
                shutil.copy2(child_stub, cwd / lemma_file)
                # DAG check on assembled file
                bad = check_import_dag(cwd / lemma_file, state.workspace)
                if bad:
                    await agent._emit("message", f"[PO] ⚠️ Assembled {lemma_path.name} has bad imports: {bad}")
                    state.last_failure_details = f"Assembly DAG violation in {lemma_path.name}: {bad}"
                    return Trans.FAILED

    # DAG check on all lemma files in workspace
    for f in state.all_lemmas + state.new_lemmas:
        file_path = cwd / f
        if file_path.exists():
            bad = check_import_dag(file_path, state.workspace)
            if bad:
                await agent._emit("message", f"[PO] ⚠️ {Path(f).name} has bad imports: {bad}")
                state.last_failure_details = f"DAG violation in {Path(f).name}: {bad}"
                return Trans.FAILED

    # Final verify: Stub.lean should compile with everything in place
    stub_rel = f"{state.workspace}/Stub.lean"
    original_rel = f"{state.workspace}/_originals/Stub.lean"

    if not (cwd / stub_rel).exists():
        return Trans.FAILED

    v = await _run_validator(agent, state.workspace, original_rel, stub_rel)
    if v and v.compiles and not v.has_sorry:
        await agent._emit("message", "[PO] Assembly verified — proof complete!")
        return Trans.ASSEMBLED

    issues = []
    if v:
        if not v.compiles: issues.append("doesn't compile")
        if v.has_sorry: issues.append("has sorry")
    await agent._emit("message", f"[PO] Assembly failed: {issues}")
    state.last_failure_details = f"Assembly: {issues}"
    return Trans.FAILED


# ─── Stage: retry ─────────────────────────────────────────────────────────────

async def _stage_retry(state: ProverState, agent) -> Trans:
    state.attempt += 1
    await agent._emit("message", f"[PO] Attempt {state.attempt}/{MAX_RETRIES}")

    if state.attempt >= MAX_RETRIES:
        return Trans.MAX_RETRIES

    # Clean up previous attempt's files
    cwd = _resolve(agent)
    decomposed_dir = cwd / state.workspace / "decomposed"
    if decomposed_dir.exists():
        # Move old decomposition for reference (decomposer session remembers it anyway)
        old_dir = cwd / state.workspace / f"decomposed_attempt_{state.attempt}"
        decomposed_dir.rename(old_dir)
        decomposed_dir.mkdir()

    # Remove lemma files at workspace root (from close_remaining)
    for f in state.new_lemmas:
        (cwd / f).unlink(missing_ok=True)

    # Restore Stub.lean from clean backup
    stub_clean = cwd / state.workspace / "Stub.clean.lean"
    stub_path = cwd / state.workspace / "Stub.lean"
    if stub_clean.exists():
        shutil.copy2(stub_clean, stub_path)

    # Kill the old decomposer (context too bloated) — fresh one will be created on next decompose
    await _cleanup_internal(agent, "decomposer")

    # Reset lemma state (keep last_failure_details for decomposer context)
    state.all_lemmas = []
    state.proved_lemmas = []
    state.closed_lemmas = []
    state.new_lemmas = []
    return Trans.NEW_APPROACH


# ─── Handler registry ─────────────────────────────────────────────────────────

HANDLERS: dict[Stage, Any] = {
    Stage.SOUNDNESS: _stage_soundness,
    Stage.SPLIT: _stage_split,
    Stage.DECOMPOSE: _stage_decompose,
    Stage.PROVE_DIRECT: _stage_prove_direct,
    Stage.CLOSE_REMAINING: _stage_close_remaining,
    Stage.PROVE_RECURSIVE: _stage_prove_recursive,
    Stage.VALIDATE: _stage_validate,
    Stage.ASSEMBLE: _stage_assemble,
    Stage.RETRY: _stage_retry,
}


# ─── Reusable helpers ─────────────────────────────────────────────────────────

def _resolve(agent) -> Path:
    return Path(agent._cwd) if agent._cwd else Path.cwd()


async def _run_proof_writer(agent, workspace: str, file: str, theorem: str) -> ProofResult | None:
    """Spawn a bounded proof_writer, return result."""
    async with swarm_agent("proof_writer", swarm=agent.swarm, cwd=agent._cwd, workspace=workspace) as writer:
        result = await writer.run(
            inp={
                "file": file,
                "theorem": theorem,
                "action": (
                    "Start with a proof SKETCH (structure + sorry at each case). "
                    "Then systematically fill each sorry with real tactics. "
                    "If a sorry resists after a fair attempt, leave it — it's a precise sub-goal."
                ),
            },
            result_type=ProofResult,
        )
    return result.output


async def _run_cea(agent, workspace: str, file: str, theorem: str) -> SoundnessVerdict | None:
    """Spawn CEA, return verdict."""
    async with swarm_agent("counter_example", swarm=agent.swarm, cwd=agent._cwd, workspace=workspace) as cea:
        result = await cea.run(
            inp={"file": file, "theorem": theorem, "action": f"Check soundness of: {theorem}"},
            result_type=SoundnessVerdict,
        )
    return result.output


async def _run_compilation_check(agent, workspace: str, file: str) -> VerifyResult | None:
    """Lightweight check: does the file compile? Does it have sorry?
    Uses deep_proof_validator with same file as both stub and complete (just for compilation check)."""
    async with swarm_agent("deep_proof_validator", swarm=agent.swarm, cwd=agent._cwd, workspace=workspace,
                            stateless=True) as v:
        result = await v.run(
            inp={
                "stub_file": file,
                "complete_file": file,
                "action": "ONLY check if this file compiles (ignore sorry warnings). Report compiles=true if no errors, has_sorry=true if sorry found.",
            },
            result_type=VerifyResult,
        )
    return result.output


async def _run_validator(agent, workspace: str, stub_file: str, complete_file: str) -> ValidationResult | None:
    """Spawn deep_proof_validator, return result."""
    async with swarm_agent("deep_proof_validator", swarm=agent.swarm, cwd=agent._cwd, workspace=workspace) as v:
        result = await v.run(
            inp={"stub_file": stub_file, "complete_file": complete_file},
            result_type=ValidationResult,
        )
    return result.output


async def _run_child_po(agent, child_workspace: str, lemma_file: str) -> dict | None:
    """Spawn a child PO sequentially, return its output dict.
    CEA is skipped — parent already validated soundness of decomposed lemmas."""
    async with swarm_agent("prover", swarm=agent.swarm, cwd=agent._cwd, workspace=child_workspace) as child:
        result = await child.run(
            inp={
                "theorem_file": lemma_file,
                "theorem_name": Path(lemma_file).stem,
                "workspace": child_workspace,
                "skip_soundness": True,  # parent already ran CEA on these
                "parent_agent": agent.spec.name,
            },
            result_type=None,
        )
    return result.output if result else None


async def _find_sorries(agent, workspace: str, file: str) -> RefactorFindResult | None:
    """Spawn refactoring_agent to find sorry goals."""
    async with swarm_agent("refactoring_agent", swarm=agent.swarm, cwd=agent._cwd, workspace=workspace) as refactorer:
        result = await refactorer.run(
            inp={
                "files": [file],
                "workspace": workspace,
                "action": "Use lean_hover_info at each sorry to get the exact goal. Return ALL sorries.",
            },
            result_type=RefactorFindResult,
        )
    return result.output


@dataclass
class BatchProposalResult:
    proposals: list[AxiomProposal] = field(default_factory=list)
    all_valid: bool = False


async def _propose_theorems_for_goals(agent, workspace: str, sorries: list[SorryGoal]) -> list[tuple[SorryGoal, AxiomProposal]]:
    """Fresh stateless call to propose theorems for ALL sorries in a file at once.
    Does NOT use the decomposer session — avoids contaminating the decomposition."""
    goals_desc = "\n".join(
        f"- Sorry #{i} at {s.file} line {s.line}:\n  Goal: {s.goal}"
        for i, s in enumerate(sorries)
    )

    async with swarm_agent("po_decomposer", swarm=agent.swarm, cwd=agent._cwd, workspace=workspace,
                            stateless=True) as proposer:
        result = await proposer.run(
            inp=(
                f"Propose compilable theorems for ALL of the following sorry goals.\n\n"
                f"{goals_desc}\n\n"
                f"RULES:\n"
                f"- Use `theorem` keyword (NOT lemma/axiom)\n"
                f"- Each theorem type must EXACTLY match its corresponding goal\n"
                f"- Include necessary imports in each formalization\n"
                f"- Verify ALL compile with lean_run_code\n"
                f"- Do NOT restructure the original proof — just formalize each goal as a standalone theorem\n"
                f"- Return one proposal per sorry in the same order\n"
                f"- Write all theorem files to decomposed/ directory"
            ),
            result_type=BatchProposalResult,
        )

    if not result.output or not result.output.proposals:
        return []

    # Match proposals back to sorries (in order)
    pairs = []
    for i, sorry in enumerate(sorries):
        if i < len(result.output.proposals):
            prop = result.output.proposals[i]
            if prop.formalization:
                pairs.append((sorry, prop))
    return pairs


async def _try_close_file(agent, workspace: str, file: str, theorems: list, new_files: list) -> bool:
    """Refactoring agent replaces sorries with simple tactics using proposed theorems."""
    axiom_info = "\n".join(
        f"- Sorry at line {s.line}, goal: {s.goal}\n  Theorem: {a.name} (file: {new_files[i]})"
        for i, (s, a) in enumerate(theorems)
    )

    async with swarm_agent("refactoring_agent", swarm=agent.swarm, cwd=agent._cwd, workspace=workspace) as refactorer:
        result = await refactorer.run(
            inp={
                "file": file,
                "action": (
                    f"Lemma files have been created. Now:\n"
                    f"1. Read the file\n"
                    f"2. Add imports for the lemma files\n"
                    f"3. Replace EACH sorry with: `first | exact <thm> | rw [<thm>] | simp [<thm>] | apply <thm>`\n"
                    f"4. Write the entire file in one shot\n"
                    f"5. Run lean_verify — must compile with NO sorry\n\n"
                    f"Do NOT write complex proofs. Only `first | ...` combinator.\n\n"
                    f"Theorems:\n{axiom_info}"
                ),
            },
            result_type=EditResult,
        )
    return result.output.success if result.output else False


async def _get_decomposition(decomposer, msg: str, state: ProverState, agent) -> DecomposeResult | None:
    """Get decomposition from decomposer with nudge retries."""
    result = await decomposer.run_ai(inp=msg, result_type=DecomposeResult, max_turns=DECOMPOSER_MAX_TURNS)
    output = result.output

    # Nudge if no output
    retries = 0
    while output is None and retries < 3:
        retries += 1
        await agent._emit("message", f"[PO] Decomposer didn't return output — nudging ({retries}/3)")
        result = await decomposer.run_ai(
            inp="Produce your StructuredOutput now with the decomposition result.",
            result_type=DecomposeResult,
            max_turns=DECOMPOSER_MAX_TURNS,
        )
        output = result.output

    # Fallback: check decomposed/ directory
    if output is None:
        cwd = _resolve(agent)
        decomposed_dir = cwd / state.workspace / "decomposed"
        if decomposed_dir.exists():
            files = list(decomposed_dir.glob("*.lean"))
            if files:
                await agent._emit("message", f"[PO] Using {len(files)} files from decomposed/")
                output = DecomposeResult(
                    strategy="decompose",
                    axioms=[Axiom(name=f.stem, filename=f"{state.workspace}/decomposed/{f.name}") for f in files],
                    proof_sketch="(decomposer didn't return sketch)",
                )

    await agent._emit("message",
        f"[PO] Decompose: strategy={output.strategy if output else 'None'}, "
        f"lemmas={len(output.axioms) if output else 0}")
    return output


async def _verify_sketch(state: ProverState, agent, decomposer, decompose_output: DecomposeResult) -> bool:
    """Loop: try sketch, if fails ask decomposer to revise. Returns True if sketch works.
    Keeps a persistent backup of the post-split Stub.lean — restored before each attempt."""
    cwd = _resolve(agent)
    max_attempts = 3

    # Save the post-split Stub.lean as a persistent backup (kept until proof is done)
    stub_path = cwd / state.workspace / "Stub.lean"
    backup = cwd / state.workspace / "Stub.clean.lean"
    if not backup.exists():
        shutil.copy2(stub_path, backup)

    for attempt in range(max_attempts):
        await agent._emit("message", f"[PO] Sketch check ({attempt + 1}/{max_attempts})...")

        # Always restore from the clean post-split version
        shutil.copy2(backup, stub_path)

        async with swarm_agent("po_sketcher", swarm=agent.swarm, cwd=agent._cwd, workspace=state.workspace) as writer:
            sketch_run = await writer.run(
                inp={
                    "file": f"{state.workspace}/Stub.lean",
                    "theorem": state.theorem_name,
                    "action": (
                        f"SKETCH STITCHING TASK (not a full proof — just wire lemmas together).\n\n"
                        f"Lemma files in decomposed/ contain theorems with `sorry`. "
                        f"Treat them as AXIOMS — their proofs will come later. "
                        f"Your job: import them and use their theorem statements to prove Stub.lean.\n\n"
                        f"The sorry in the lemma files is EXPECTED. Lean compiles fine with sorry. "
                        f"You should be able to `exact <lemma_name>` or `apply <lemma_name>` etc. "
                        f"The fact that lemmas have sorry does NOT prevent you from using them.\n\n"
                        f"IMPORT PATHS (use ONLY these — do NOT import from any parent directory):\n"
                        f"{chr(10).join('import ' + Path(f).with_suffix('').as_posix().replace('/', '.') for f in state.all_lemmas)}\n\n"
                        f"Proof sketch: {decompose_output.proof_sketch}\n\n"
                        f"STEPS:\n"
                        f"1. Add the import lines above to Stub.lean\n"
                        f"2. Use the imported theorems to fill the proof body of the main theorem\n"
                        f"3. Run lean_verify — it should compile (sorry warnings from lemmas are OK)\n"
                        f"4. success=true if Stub.lean compiles with NO sorry in the main theorem itself\n"
                        f"5. success=false if the lemma types don't match the goal — explain WHY in blocking_reason\n\n"
                        f"Do NOT import from any other path. ONLY use the imports listed above."
                    ),
                },
                result_type=SketchResult,
            )
        sketch_result = sketch_run.output

        if sketch_result and sketch_result.success:
            # DAG check: no imports from parent/sibling Sandbox paths
            bad_imports = check_import_dag(stub_path, state.workspace)
            if bad_imports:
                await agent._emit("message", f"[PO] Sketch has bad imports (DAG violation): {bad_imports}")
                shutil.copy2(backup, stub_path)
                reason = f"DAG violation: imports {bad_imports} from outside workspace"
                await agent._emit("message", f"[PO] Sketch failed: {reason}")
                if attempt >= max_attempts - 1:
                    break
                continue
            await agent._emit("message", "[PO] Sketch verified ✅")
            return True

        # Revert (backup stays — will be restored on next attempt)
        shutil.copy2(backup, stub_path)

        reason = (sketch_result.blocking_reason if sketch_result and sketch_result.blocking_reason
                  else sketch_run.raw_result[:200] if sketch_run.raw_result else "no output from proof_writer")
        await agent._emit("message", f"[PO] Sketch failed: {reason}")

        if attempt >= max_attempts - 1:
            break

        # Ask decomposer to revise
        result = await decomposer.run_ai(
            inp=f"Sketch proof failed: {reason}\nRevise your decomposition — write new files to decomposed/.",
            result_type=DecomposeResult,
            max_turns=DECOMPOSER_MAX_TURNS,
        )
        if result.output and result.output.axioms:
            # Reload lemma files
            state.all_lemmas = []
            originals_dir = cwd / state.workspace / "_originals"
            for axiom in result.output.axioms:
                src = cwd / axiom.filename
                if src.exists():
                    state.all_lemmas.append(axiom.filename)
                    shutil.copy2(src, originals_dir / Path(axiom.filename).name)
            decompose_output = result.output

    return False




# ─── File creation ────────────────────────────────────────────────────────────

def _create_lemma_file(cwd: Path, workspace_rel: str, prefix: str, index: int, name: str, content: str) -> str:
    """Create a lemma file and save original. Returns relative path."""
    workspace_abs = cwd / workspace_rel
    originals_dir = workspace_abs / "_originals"
    originals_dir.mkdir(exist_ok=True)

    safe_name = name.replace(" ", "_").replace("/", "_")[:40] or f"{prefix}_{index}"
    filename = f"{prefix}_{index}_{safe_name}.lean"
    filepath = workspace_abs / filename

    if not content:
        content = f"-- {name}\nsorry\n"
    filepath.write_text(content)

    shutil.copy2(filepath, originals_dir / filename)
    return f"{workspace_rel}/{filename}"


def _write_progress(cwd: Path, state: ProverState):
    """Write progress.md for monitoring."""
    workspace_abs = cwd / state.workspace
    workspace_abs.mkdir(parents=True, exist_ok=True)
    progress = workspace_abs / "progress.md"

    total = len(state.all_lemmas)
    proved = len(state.proved_lemmas)
    closed = len(state.closed_lemmas)
    new = len(state.new_lemmas)

    content = (
        f"# Proof Progress\n\n"
        f"- **Stage**: {state.stage.value}\n"
        f"- **Theorem**: {state.theorem_name}\n"
        f"- **Attempt**: {state.attempt + 1}/{MAX_RETRIES}\n"
        f"- **Proved**: {proved}/{total}\n"
        f"- **Closed**: {closed}/{total}\n"
        f"- **New lemmas**: {new}\n"
        f"- **Failure**: {state.failure_reason or 'none'}\n"
        f"- **Details**: {state.last_failure_details or 'none'}\n\n"
        f"## Lemmas\n"
    )
    for f in state.all_lemmas:
        if f in state.proved_lemmas:
            content += f"- ✅ `{Path(f).name}`\n"
        elif f in state.closed_lemmas:
            content += f"- 🔗 `{Path(f).name}` (closed, deps need proving)\n"
        else:
            content += f"- ❌ `{Path(f).name}`\n"
    if state.new_lemmas:
        content += f"\n## New (from close_remaining)\n"
        for f in state.new_lemmas:
            status = "✅" if f in state.proved_lemmas else "❌"
            content += f"- {status} `{Path(f).name}`\n"

    progress.write_text(content)


async def _notify_parent(agent, state: ProverState, message: str):
    try:
        await agent.channel_bus.send_to(
            f"{state.parent_agent}:messages",
            sender=agent.spec.name,
            payload=message,
        )
    except Exception:
        pass
    await agent._emit("message", f"[PO → {state.parent_agent}]: {message}")


async def _get_internal(agent, which: str):
    """Get or create a persistent internal agent scoped to workspace."""
    attr = f"_po_{which}"
    attr_ctx = f"_po_{which}_ctx"

    if getattr(agent, attr, None) is None:
        workspace = None
        if hasattr(agent, '_workflow_state') and agent._workflow_state:
            workspace = agent._workflow_state.workspace
        ctx = swarm_agent(f"po_{which}", swarm=agent.swarm, cwd=agent._cwd, workspace=workspace)
        internal = await ctx.__aenter__()
        setattr(agent, attr_ctx, ctx)
        setattr(agent, attr, internal)

    return getattr(agent, attr)


async def _cleanup_internal(agent, which: str):
    attr = f"_po_{which}"
    attr_ctx = f"_po_{which}_ctx"
    if getattr(agent, attr, None) is not None:
        ctx = getattr(agent, attr_ctx, None)
        if ctx:
            await ctx.__aexit__(None, None, None)
        setattr(agent, attr_ctx, None)
        setattr(agent, attr, None)
