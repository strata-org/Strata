"""Proof Orchestrator v4: Worklist-based pipeline (state machine).

Pipeline:
  SOUNDNESS → SPLIT → DECOMPOSE → [ANALYZE → PROVE_DIRECT → REFACTOR]* → PROVE_RECURSIVE → ASSEMBLE → VALIDATE → DONE

This file is the STATE MACHINE only — thin orchestration layer.
Logic lives in:
  - po_agents.py    → Agent spawning + verified_run pattern
  - po_analysis.py  → Difficulty assessment + refactoring
  - po_verify.py    → Programmatic checks
  - po_util.py      → File ops, checkpointing, import rewriting
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
    verified_loop, run_proof_writer, run_cea, run_validator, run_splitter,
    run_sketcher, run_child_po, swarm_checkpoint,
)
from .po_analysis import (
    DifficultyAssessment, analyze_files, refactor_multi_theorem_files,
)
from .po_verify import (
    check_import_dag, verify_file_exists, verify_no_sorry,
    count_sorries, is_bare_sorry, verify_split_complete,
)
from .po_util import (
    rewrite_imports_for_child, write_checkpoint, write_progress,
    setup_child_workspace,
)
from .._helpers import swarm_agent

T = TypeVar("T")

MAX_RETRIES = 3
MAX_RECURSION_DEPTH = 2
MAX_PARALLEL_DIRECT = 3
MAX_DRAIN_ROUNDS = 5
DECOMPOSER_MAX_TURNS = 100
WRITER_MAX_TURNS = 50
WRITER_EXTENDED_TURNS = 80


# ─── Enums ────────────────────────────────────────────────────────────────────

class Stage(str, Enum):
    SOUNDNESS = "soundness"
    SPLIT = "split"
    DECOMPOSE = "decompose"
    ANALYZE = "analyze"
    PROVE_DIRECT = "prove_direct"
    REFACTOR = "refactor"
    PROVE_RECURSIVE = "prove_recursive"
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
    DECOMPOSED = "decomposed"
    SIMPLE_ENOUGH = "simple_enough"
    NEEDS_DECOMP = "needs_decomp"
    HAS_DIRECT = "has_direct"
    ALL_RECURSIVE = "all_recursive"
    ALL_PROVED = "all_proved"
    SOME_REMAINING = "some_remaining"
    NEW_WORK = "new_work"
    STABLE = "stable"
    CHILD_FAILED = "child_failed"
    ASSEMBLED = "assembled"
    VALID = "valid"
    INVALID = "invalid"
    FAILED = "failed"
    NEW_APPROACH = "new_approach"
    MAX_RETRIES = "max_retries"


TRANSITIONS: dict[tuple[Stage, Trans], Stage] = {
    (Stage.SOUNDNESS, Trans.SOUND):         Stage.SPLIT,
    (Stage.SOUNDNESS, Trans.SKIPPED):       Stage.SPLIT,
    (Stage.SOUNDNESS, Trans.UNSOUND):       Stage.FAILED,

    (Stage.SPLIT, Trans.SPLIT_DONE):        Stage.DECOMPOSE,
    (Stage.SPLIT, Trans.SPLIT_FAILED):      Stage.DECOMPOSE,

    (Stage.DECOMPOSE, Trans.DECOMPOSED):    Stage.ANALYZE,
    (Stage.DECOMPOSE, Trans.SIMPLE_ENOUGH): Stage.ANALYZE,
    (Stage.DECOMPOSE, Trans.NEEDS_DECOMP):  Stage.RETRY,

    (Stage.ANALYZE, Trans.HAS_DIRECT):      Stage.PROVE_DIRECT,
    (Stage.ANALYZE, Trans.ALL_RECURSIVE):   Stage.PROVE_RECURSIVE,
    (Stage.ANALYZE, Trans.ALL_PROVED):      Stage.ASSEMBLE,

    (Stage.PROVE_DIRECT, Trans.ALL_PROVED):     Stage.ASSEMBLE,
    (Stage.PROVE_DIRECT, Trans.SOME_REMAINING): Stage.REFACTOR,

    (Stage.REFACTOR, Trans.NEW_WORK):       Stage.ANALYZE,
    (Stage.REFACTOR, Trans.STABLE):         Stage.PROVE_RECURSIVE,
    (Stage.REFACTOR, Trans.ALL_PROVED):     Stage.ASSEMBLE,

    (Stage.PROVE_RECURSIVE, Trans.ALL_PROVED):    Stage.ASSEMBLE,
    (Stage.PROVE_RECURSIVE, Trans.CHILD_FAILED):  Stage.RETRY,

    (Stage.ASSEMBLE, Trans.ASSEMBLED):      Stage.VALIDATE,
    (Stage.ASSEMBLE, Trans.FAILED):         Stage.RETRY,

    (Stage.VALIDATE, Trans.VALID):          Stage.DONE,
    (Stage.VALIDATE, Trans.INVALID):        Stage.RETRY,

    (Stage.RETRY, Trans.NEW_APPROACH):      Stage.DECOMPOSE,
    (Stage.RETRY, Trans.MAX_RETRIES):       Stage.FAILED,
}


# ─── State ────────────────────────────────────────────────────────────────────

@dataclass
class ProverState:
    stage: Stage = Stage.SOUNDNESS
    theorem_file: str = ""
    theorem_name: str = ""
    workspace: str = ""
    skip_soundness: bool = False
    depth: int = 0

    proved_files: list[str] = field(default_factory=list)
    direct_files: list[str] = field(default_factory=list)
    recursive_files: list[str] = field(default_factory=list)

    drain_round: int = 0
    attempt: int = 0
    parent_agent: str = "TaskManager"
    failure_reason: str = ""
    last_failure_details: str = ""


# ─── Decompose helper types ──────────────────────────────────────────────────

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

    # Resume or fresh start
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

    agent._workflow_state = state
    await agent._emit("message", f"[PO] Starting: {theorem_name} in {workspace_rel} (depth={depth})")

    # Main state machine loop
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

    outcome = await run_splitter(agent, state.workspace, f"{state.workspace}/Stub.lean")

    if outcome.success:
        return Trans.SPLIT_DONE
    if verify_file_exists(cwd, f"{state.workspace}/Stub/Def.lean"):
        return Trans.SPLIT_DONE
    return Trans.SPLIT_FAILED


async def _stage_decompose(state: ProverState, agent) -> Trans:
    decomposer = await _get_internal(agent, "decomposer")
    cwd = _resolve(agent)

    msg = (f"Decompose theorem: {state.theorem_name}\nFile: {state.workspace}/Stub.lean\n"
           f"Write lemma files to: {state.workspace}/decomposed/lemma_<n>_<name>.lean\n"
           f"RULE: Each file must contain EXACTLY ONE theorem with sorry.\n")
    if state.attempt > 0:
        msg += (f"Attempt {state.attempt + 1}/{MAX_RETRIES}. Previous failed: {state.last_failure_details}\n"
                f"decomposed/ is CLEARED. Write completely NEW files.\n")
    msg += f"Read the file, use lean_goal at the sorry, decide strategy.\n"

    output = await _get_decomposition(decomposer, msg, state, agent)
    if output is None:
        return Trans.NEEDS_DECOMP if state.attempt > 0 else Trans.SIMPLE_ENOUGH
    if output.strategy == "direct":
        return Trans.SIMPLE_ENOUGH

    # Collect lemma files
    all_lemmas = []
    originals_dir = cwd / state.workspace / "_originals"
    originals_dir.mkdir(exist_ok=True)
    for goal in (output.sub_goals or []):
        src = cwd / goal.filename
        if src.exists() and not check_import_dag(src, state.workspace):
            all_lemmas.append(goal.filename)
            shutil.copy2(src, originals_dir / Path(goal.filename).name)

    if not all_lemmas:
        return Trans.SIMPLE_ENOUGH

    all_lemmas = list(dict.fromkeys(all_lemmas))
    await agent._emit("message", f"[PO] Decomposed: {len(all_lemmas)} lemmas")

    # Parallel CEA
    unsound = await _parallel_cea(all_lemmas, state, agent)
    all_lemmas = [f for f in all_lemmas if f not in unsound]
    if not all_lemmas:
        state.last_failure_details = "All lemmas rejected by CEA"
        return Trans.NEEDS_DECOMP

    # Sketch verification loop
    sketch_ok = await _verify_sketch(all_lemmas, state, agent, decomposer, output)
    if sketch_ok:
        await swarm_checkpoint(agent, f"decomposed:{len(all_lemmas)}_lemmas")
        return Trans.DECOMPOSED

    state.last_failure_details = "Sketch couldn't use decomposed lemmas"
    return Trans.NEEDS_DECOMP


async def _stage_analyze(state: ProverState, agent) -> Trans:
    cwd = _resolve(agent)
    decomposed_dir = cwd / state.workspace / "decomposed"

    # Gather unproved files
    all_files = ([f"{state.workspace}/decomposed/{f.name}" for f in decomposed_dir.glob("*.lean")]
                 if decomposed_dir.exists() else [])

    # If no decomposed files, check Stub.lean directly
    if not all_files:
        stub = f"{state.workspace}/Stub.lean"
        all_files = [stub] if not verify_no_sorry(cwd, stub) else []

    unproved = [f for f in all_files if f not in state.proved_files and not verify_no_sorry(cwd, f)]

    # Mark newly proved
    for f in all_files:
        if f not in state.proved_files and verify_no_sorry(cwd, f):
            state.proved_files.append(f)

    if not unproved:
        return Trans.ALL_PROVED

    if state.drain_round >= MAX_DRAIN_ROUNDS:
        state.recursive_files = unproved
        state.direct_files = []
        return Trans.ALL_RECURSIVE

    await agent._emit("message", f"[PO] Analyzing {len(unproved)} files (round {state.drain_round + 1})...")
    assessments = analyze_files(unproved, cwd)

    state.direct_files = [a.file for a in assessments if a.difficulty == "direct"]
    state.recursive_files = [a.file for a in assessments if a.difficulty == "recursive"]
    for a in assessments:
        if a.difficulty == "proved" and a.file not in state.proved_files:
            state.proved_files.append(a.file)

    await agent._emit("message",
        f"[PO] Analysis: {len(state.direct_files)} direct, {len(state.recursive_files)} recursive")

    if state.direct_files:
        return Trans.HAS_DIRECT
    if state.recursive_files:
        return Trans.ALL_RECURSIVE
    return Trans.ALL_PROVED


async def _stage_prove_direct(state: ProverState, agent) -> Trans:
    to_prove = list(state.direct_files)
    if not to_prove:
        return Trans.ALL_PROVED

    await agent._emit("message", f"[PO] Direct proving {len(to_prove)} files...")
    semaphore = asyncio.Semaphore(MAX_PARALLEL_DIRECT)
    cwd = _resolve(agent)
    newly_proved = []

    async def _attempt(f: str):
        async with semaphore:
            backup = cwd / f"{f}.bak"
            shutil.copy2(cwd / f, backup)

            sorry_ct = count_sorries(cwd, f)
            turns = WRITER_EXTENDED_TURNS if sorry_ct <= 2 else WRITER_MAX_TURNS
            rounds = 3 if sorry_ct <= 2 else 2
            action = _build_writer_action(sorry_ct)

            # Run proof_writer with in-context verification loop
            # Agent stays alive across rounds — sees its own errors and fixes them
            outcome = await run_proof_writer(
                agent, state.workspace, f, action,
                max_turns=turns, max_rounds=rounds,
            )

            # Final safety: DAG violations → revert
            bad = check_import_dag(cwd / f, state.workspace)
            if bad:
                await agent._emit("message", f"[PO] ⚠️ {Path(f).name}: DAG violation — reverting")
                shutil.copy2(backup, cwd / f)
            elif outcome.success:
                newly_proved.append(f)
                await agent._emit("message", f"[PO] ✅ Proved: {Path(f).name}")
            else:
                await agent._emit("message",
                    f"[PO] ⏳ {Path(f).name}: {count_sorries(cwd, f)} sorries after {outcome.attempts} rounds")

            backup.unlink(missing_ok=True)

    await asyncio.gather(*[_attempt(f) for f in to_prove])

    state.proved_files.extend(newly_proved)
    state.direct_files = [f for f in state.direct_files if f not in newly_proved]

    if newly_proved:
        write_checkpoint(cwd, state)
        await swarm_checkpoint(agent, f"prove_direct:{len(newly_proved)}_proved")

    # Check if everything in decomposed/ is done
    decomposed_dir = cwd / state.workspace / "decomposed"
    if decomposed_dir.exists():
        all_done = all(verify_no_sorry(cwd, f"{state.workspace}/decomposed/{f.name}")
                       for f in decomposed_dir.glob("*.lean"))
        if all_done:
            return Trans.ALL_PROVED

    return Trans.SOME_REMAINING


async def _stage_refactor(state: ProverState, agent) -> Trans:
    cwd = _resolve(agent)
    decomposed_dir = cwd / state.workspace / "decomposed"
    if not decomposed_dir.exists():
        return Trans.STABLE

    state.drain_round += 1
    new_files = refactor_multi_theorem_files(decomposed_dir, state.workspace, state.proved_files)

    if new_files:
        await agent._emit("message", f"[PO] Refactored: {len(new_files)} new files")
        return Trans.NEW_WORK

    # Check if all done after refactoring
    all_done = all(
        verify_no_sorry(cwd, f"{state.workspace}/decomposed/{f.name}")
        for f in decomposed_dir.glob("*.lean")
    )
    if all_done:
        return Trans.ALL_PROVED

    return Trans.STABLE


async def _stage_prove_recursive(state: ProverState, agent) -> Trans:
    remaining = [f for f in state.recursive_files if f not in state.proved_files]
    if not remaining:
        return Trans.ALL_PROVED

    if state.depth >= MAX_RECURSION_DEPTH:
        state.last_failure_details = f"Depth limit: {len(remaining)} files need deeper decomposition"
        return Trans.CHILD_FAILED

    cwd = _resolve(agent)
    await agent._emit("message", f"[PO] Recursive: {len(remaining)} files (depth={state.depth + 1})")

    for lemma_file in remaining:
        if is_bare_sorry(cwd, lemma_file):
            continue

        child_workspace = setup_child_workspace(cwd, lemma_file, state.workspace)
        await agent._emit("message", f"[PO] Child PO: {Path(lemma_file).name}")

        result = await run_child_po(agent, child_workspace, lemma_file, state.depth + 1)

        if result and result.get("stage") == "done":
            state.proved_files.append(lemma_file)
            write_checkpoint(cwd, state)
            await swarm_checkpoint(agent, f"child_proved:{Path(lemma_file).name}")
            await agent._emit("message", f"[PO] ✅ Child proved: {Path(lemma_file).name}")
        else:
            reason = result.get("details", "unknown") if result else "no output"
            state.last_failure_details = f"Child failed: {Path(lemma_file).name}: {reason}"
            return Trans.CHILD_FAILED

    return Trans.ALL_PROVED


async def _stage_assemble(state: ProverState, agent) -> Trans:
    cwd = _resolve(agent)

    # Copy child results back
    for f in state.proved_files:
        child_stub = cwd / Path(f).parent / Path(f).stem / "Stub.lean"
        if child_stub.exists():
            shutil.copy2(child_stub, cwd / f)
            if check_import_dag(cwd / f, state.workspace):
                state.last_failure_details = f"Assembly DAG violation: {Path(f).name}"
                return Trans.FAILED

    # Validate Stub.lean
    stub_rel = f"{state.workspace}/Stub.lean"
    original_rel = f"{state.workspace}/_originals/Stub.lean"
    v = await run_validator(agent, state.workspace, original_rel, stub_rel)
    if v and v.compiles and not v.has_sorry:
        await agent._emit("message", "[PO] Assembly verified ✅")
        return Trans.ASSEMBLED

    state.last_failure_details = f"Assembly: {'no compile' if v and not v.compiles else 'has sorry'}"
    return Trans.FAILED


async def _stage_validate(state: ProverState, agent) -> Trans:
    stub_rel = f"{state.workspace}/Stub.lean"
    original_rel = f"{state.workspace}/_originals/Stub.lean"
    v = await run_validator(agent, state.workspace, original_rel, stub_rel)
    if v and v.compiles and not v.has_sorry and v.statements_match:
        return Trans.VALID
    state.last_failure_details = f"Validation failed"
    return Trans.INVALID


async def _stage_retry(state: ProverState, agent) -> Trans:
    state.attempt += 1
    if state.attempt >= MAX_RETRIES:
        return Trans.MAX_RETRIES

    cwd = _resolve(agent)
    decomposed_dir = cwd / state.workspace / "decomposed"
    if decomposed_dir.exists():
        decomposed_dir.rename(cwd / state.workspace / f"decomposed_attempt_{state.attempt}")
        decomposed_dir.mkdir()

    stub_clean = cwd / state.workspace / "Stub.clean.lean"
    if stub_clean.exists():
        shutil.copy2(stub_clean, cwd / state.workspace / "Stub.lean")

    await _cleanup_internal(agent, "decomposer")

    preserved = list(state.proved_files)
    state.proved_files = preserved
    state.direct_files = []
    state.recursive_files = []
    state.drain_round = 0

    await agent._emit("message", f"[PO] Retry {state.attempt}/{MAX_RETRIES}, preserved {len(preserved)} proofs")
    return Trans.NEW_APPROACH


HANDLERS: dict[Stage, Any] = {
    Stage.SOUNDNESS: _stage_soundness,
    Stage.SPLIT: _stage_split,
    Stage.DECOMPOSE: _stage_decompose,
    Stage.ANALYZE: _stage_analyze,
    Stage.PROVE_DIRECT: _stage_prove_direct,
    Stage.REFACTOR: _stage_refactor,
    Stage.PROVE_RECURSIVE: _stage_prove_recursive,
    Stage.ASSEMBLE: _stage_assemble,
    Stage.VALIDATE: _stage_validate,
    Stage.RETRY: _stage_retry,
}


# ─── Private helpers (thin) ──────────────────────────────────────────────────

def _resolve(agent) -> Path:
    return Path(agent._cwd) if agent._cwd else Path.cwd()


def _build_writer_action(sorry_count: int) -> str:
    if sorry_count <= 2:
        return (
            f"File has {sorry_count} sorry(s) — CLOSE to done.\n"
            "Try simple tactics first. If stuck, factor into helper theorems in same file.\n"
            "Leave stubborn helpers with sorry — they'll be extracted later."
        )
    return (
        "Write a proof. Start with structural sketch, fill each sorry.\n"
        "For hard sub-goals: factor into helper theorems in same file.\n"
        "Leave stubborn helpers with sorry — they'll be extracted later."
    )


async def _parallel_cea(lemma_files: list[str], state: ProverState, agent) -> list[str]:
    unsound = []
    semaphore = asyncio.Semaphore(MAX_PARALLEL_DIRECT)

    async def _check(f: str):
        async with semaphore:
            v = await run_cea(agent, state.workspace, f, Path(f).stem)
            if v and not v.sound and v.confidence == "high":
                unsound.append(f)
                await agent._emit("message", f"[PO] CEA: {Path(f).name} UNSOUND")

    await asyncio.gather(*[_check(f) for f in lemma_files])
    return unsound


async def _verify_sketch(all_lemmas: list[str], state: ProverState, agent, decomposer, output) -> bool:
    cwd = _resolve(agent)
    stub_path = cwd / state.workspace / "Stub.lean"
    backup = cwd / state.workspace / "Stub.clean.lean"
    if not backup.exists():
        shutil.copy2(stub_path, backup)

    for attempt in range(3):
        shutil.copy2(backup, stub_path)
        result = await run_sketcher(agent, state.workspace, f"{state.workspace}/Stub.lean",
                                    state.theorem_name, all_lemmas, output.proof_sketch)

        if result and result.success:
            if not check_import_dag(stub_path, state.workspace):
                return True
            shutil.copy2(backup, stub_path)
        else:
            shutil.copy2(backup, stub_path)

        if attempt >= 2:
            break

        # Ask decomposer to revise
        rev = await decomposer.run_ai(
            inp=f"Sketch failed: {result.blocking_reason if result else 'no output'}. Revise.",
            result_type=DecomposeResult, max_turns=DECOMPOSER_MAX_TURNS)
        if rev.output and rev.output.sub_goals:
            all_lemmas.clear()
            for goal in rev.output.sub_goals:
                if (cwd / goal.filename).exists():
                    all_lemmas.append(goal.filename)
            output = rev.output

    return False


async def _get_decomposition(decomposer, msg, state, agent) -> DecomposeResult | None:
    result = await decomposer.run_ai(inp=msg, result_type=DecomposeResult, max_turns=DECOMPOSER_MAX_TURNS)
    output = result.output

    retries = 0
    while output is None and retries < 3:
        retries += 1
        result = await decomposer.run_ai(
            inp="Produce your StructuredOutput now.", result_type=DecomposeResult, max_turns=DECOMPOSER_MAX_TURNS)
        output = result.output

    if output is None:
        cwd = _resolve(agent)
        decomposed_dir = cwd / state.workspace / "decomposed"
        if decomposed_dir.exists():
            files = list(decomposed_dir.glob("*.lean"))
            if files:
                output = DecomposeResult(
                    strategy="decompose",
                    sub_goals=[SubGoal(name=f.stem, filename=f"{state.workspace}/decomposed/{f.name}") for f in files],
                    proof_sketch="(from directory)")

    await agent._emit("message",
        f"[PO] Decompose: {output.strategy if output else 'None'}, {len(output.sub_goals) if output else 0} lemmas")
    return output


async def _notify_parent(agent, state, message):
    try:
        await agent.channel_bus.send_to(f"{state.parent_agent}:messages",
                                         sender=agent.spec.name, payload=message)
    except Exception:
        pass


async def _get_internal(agent, which: str):
    attr = f"_po_{which}"
    attr_ctx = f"_po_{which}_ctx"
    if getattr(agent, attr, None) is None:
        workspace = getattr(agent, '_workflow_state', None)
        workspace = workspace.workspace if workspace else None
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
