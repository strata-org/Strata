"""Proof Orchestrator v2: Router pattern with internal agents.

Same architecture as TaskManager:
- Orchestrator's own session is the router brain (persistent, no tools)
- Internal agents (decomposer, assembler) do the work
- Spawned agents (proof_writer, refactoring_agent, CEA) are stateless and scoped
- State machine handles mechanics
"""

from __future__ import annotations

import asyncio
import shutil
import time
from dataclasses import dataclass, field, asdict
from enum import Enum
from pathlib import Path
from typing import Any, TypeVar

from .._helpers import swarm_agent

T = TypeVar("T")

MAX_RETRIES = 3
MAX_PARALLEL_WRITERS = 3
MAX_PARALLEL_VALIDATORS = 5
WRITER_MAX_TURNS = 50
DECOMPOSER_MAX_TURNS = 25


# ─── Enums ────────────────────────────────────────────────────────────────────

class ProverStage(str, Enum):
    DECOMPOSE = "decompose"
    DIRECT_ATTEMPT = "direct_attempt"
    PROVE_LEMMAS = "prove_lemmas"
    REFACTOR = "refactor"
    VALIDATE = "validate"
    ASSEMBLE = "assemble"
    RETRY = "retry"
    DONE = "done"
    FAILED = "failed"


class ProverTransition(str, Enum):
    DECOMPOSED = "decomposed"
    SIMPLE_ENOUGH = "simple_enough"
    PROOF_FOUND = "proof_found"
    NEEDS_DECOMP = "needs_decomp"
    ALL_PROVED = "all_proved"
    HAS_SORRY = "has_sorry"
    STUCK = "stuck"
    NEW_AXIOMS = "new_axioms"
    CANNOT_REFACTOR = "cannot_refactor"
    VALID = "valid"
    INVALID = "invalid"
    ASSEMBLED = "assembled"
    NEW_APPROACH = "new_approach"
    MAX_RETRIES = "max_retries"
    FAILED = "failed"


# ─── Transitions ──────────────────────────────────────────────────────────────

TRANSITIONS: dict[tuple[ProverStage, ProverTransition], ProverStage] = {
    (ProverStage.DECOMPOSE, ProverTransition.DECOMPOSED):   ProverStage.PROVE_LEMMAS,
    (ProverStage.DECOMPOSE, ProverTransition.SIMPLE_ENOUGH): ProverStage.DIRECT_ATTEMPT,

    (ProverStage.DIRECT_ATTEMPT, ProverTransition.PROOF_FOUND): ProverStage.VALIDATE,
    (ProverStage.DIRECT_ATTEMPT, ProverTransition.NEEDS_DECOMP): ProverStage.DECOMPOSE,
    (ProverStage.DIRECT_ATTEMPT, ProverTransition.FAILED):  ProverStage.RETRY,

    (ProverStage.PROVE_LEMMAS, ProverTransition.ALL_PROVED): ProverStage.VALIDATE,
    (ProverStage.PROVE_LEMMAS, ProverTransition.HAS_SORRY): ProverStage.REFACTOR,
    (ProverStage.PROVE_LEMMAS, ProverTransition.STUCK):     ProverStage.RETRY,

    (ProverStage.REFACTOR, ProverTransition.NEW_AXIOMS):    ProverStage.PROVE_LEMMAS,
    (ProverStage.REFACTOR, ProverTransition.CANNOT_REFACTOR): ProverStage.RETRY,

    (ProverStage.VALIDATE, ProverTransition.VALID):         ProverStage.ASSEMBLE,
    (ProverStage.VALIDATE, ProverTransition.INVALID):       ProverStage.REFACTOR,
    (ProverStage.VALIDATE, ProverTransition.STUCK):         ProverStage.RETRY,

    (ProverStage.ASSEMBLE, ProverTransition.ASSEMBLED):     ProverStage.DONE,
    (ProverStage.ASSEMBLE, ProverTransition.FAILED):        ProverStage.RETRY,

    (ProverStage.RETRY, ProverTransition.NEW_APPROACH):     ProverStage.DECOMPOSE,
    (ProverStage.RETRY, ProverTransition.MAX_RETRIES):      ProverStage.FAILED,
}


# ─── State ────────────────────────────────────────────────────────────────────

@dataclass
class ProverState:
    stage: ProverStage = ProverStage.DECOMPOSE
    theorem_file: str = ""
    theorem_name: str = ""
    workspace: str = ""
    axiom_files: list[str] = field(default_factory=list)
    proved_files: list[str] = field(default_factory=list)
    attempt: int = 0
    parent_agent: str = "TaskManager"



# ─── Main loop ────────────────────────────────────────────────────────────────

async def run_workflow(agent, inp: Any, result_type: type[T] | None = None):
    from .._types import AgentResult, AgentStatus

    await agent._emit("status_change", "running")

    # Parse input
    if isinstance(inp, dict):
        theorem_file = inp.get("theorem_file", "")
        theorem_name = inp.get("theorem_name", "")
        workspace_rel = inp.get("workspace", "")
        parent_agent = inp.get("parent_agent", "TaskManager")
    elif isinstance(inp, str):
        theorem_file = inp
        theorem_name = ""
        workspace_rel = ""
        parent_agent = "TaskManager"
    else:
        theorem_file = str(inp)
        theorem_name = ""
        workspace_rel = ""
        parent_agent = "TaskManager"

    cwd = Path(agent._cwd) if agent._cwd else Path.cwd()

    if not workspace_rel:
        await agent._emit("message", "[Prover] ERROR: No workspace provided by parent.")
        from .._types import AgentResult, AgentStatus as _AS
        result = AgentResult(name=agent.spec.name, status=_AS.FAILED)
        result.output = {"stage": "failed", "error": "no_workspace"}
        return result

    # All paths stored RELATIVE to cwd — tool scoping needs relative paths
    workspace_abs = cwd / workspace_rel
    workspace_abs.mkdir(parents=True, exist_ok=True)

    # Stub.lean MUST exist — placed by TM (top-level) or parent orchestrator (recursive)
    stub_file = workspace_abs / "Stub.lean"
    if not stub_file.exists():
        from .._types import AgentResult, AgentStatus as _AS
        await agent._emit("message", f"[Prover] ERROR: No Stub.lean found in {workspace_rel}. Cannot proceed.")
        await _notify_parent(agent, ProverState(parent_agent=parent_agent),
                             f"Failed: Stub.lean not found in workspace {workspace_rel}")
        result = AgentResult(name=agent.spec.name, status=_AS.FAILED)
        result.output = {"stage": "failed", "error": "stub_not_found"}
        return result

    # Keep original copy for self-validation
    originals_dir = workspace_abs / "_originals"
    originals_dir.mkdir(exist_ok=True)
    own_original = originals_dir / "Stub.lean"
    if not own_original.exists():
        shutil.copy2(stub_file, own_original)

    state = ProverState(
        stage=ProverStage.DECOMPOSE,
        theorem_file=theorem_file,
        theorem_name=theorem_name,
        workspace=workspace_rel,  # always relative to cwd
        parent_agent=parent_agent,
    )
    agent._workflow_state = state

    await agent._emit("message", f"[Prover] Starting: {theorem_name} in {theorem_file}")
    await agent._emit("message", f"[Prover] Workspace: {workspace_rel}")

    while not agent.cancellation.is_cancelled:
        if state.stage in (ProverStage.DONE, ProverStage.FAILED):
            break

        try:
            handler = STAGE_HANDLERS.get(state.stage)
            if not handler:
                break

            transition = await handler(state, agent)

            next_stage = TRANSITIONS.get((state.stage, transition))
            if next_stage is None:
                await agent._emit("message", f"[Prover] Bad transition: ({state.stage.value}, {transition.value})")
                next_stage = ProverStage.RETRY

            await agent._emit("state_transition", {
                "from": state.stage.value, "transition": transition.value, "to": next_stage.value,
            })
            await agent._emit("message",
                f"[Prover] {state.stage.value} → {transition.value} → {next_stage.value}")

            state.stage = next_stage
            agent._workflow_state = state

        except Exception as e:
            await agent._emit("message", f"[Prover] Error in {state.stage.value}: {e}")
            state.stage = ProverStage.RETRY
            agent._workflow_state = state

    # Notify parent
    status_msg = f"Proof {'complete' if state.stage == ProverStage.DONE else 'failed'}: {theorem_file}"
    await _notify_parent(agent, state, status_msg)

    # Cleanup internal agents
    await _cleanup_internal(agent, "decomposer")

    result = AgentResult(name=agent.spec.name, status=AgentStatus.COMPLETED)
    result.output = {"stage": state.stage.value, "theorem_file": theorem_file, "attempts": state.attempt}
    return result


# ─── Stage handlers ───────────────────────────────────────────────────────────

async def _stage_decompose(state: ProverState, agent) -> ProverTransition:
    """Decomposer agent analyzes theorem and proposes strategy.
    Returns structured axioms — module creates files deterministically."""
    decomposer = await _get_internal(agent, "decomposer")

    msg = f"Decompose theorem: {state.theorem_name}\nFile: {state.workspace}/Stub.lean\n"
    if state.attempt > 0:
        msg += f"Attempt {state.attempt + 1}/{MAX_RETRIES}. Previous decomposition didn't work — try a different approach.\n"
    msg += "Read the file, use lean_hover_info on the sorry, and decide strategy. Use lean_run_code to verify your formalizations compile."

    await agent.channel_bus.send_to(
        f"{decomposer.spec.name}:messages",
        sender="system",
        payload=msg,
    )

    @dataclass
    class _Axiom:
        name: str = ""
        description: str = ""
        formalization: str = ""  # full Lean code (imports + theorem statement with sorry)
        depends_on: list[str] = field(default_factory=list)

    @dataclass
    class _DecomposeResult:
        strategy: str = "decompose"  # "direct" or "decompose"
        axioms: list[_Axiom] = field(default_factory=list)
        proof_sketch: str = ""  # how axioms combine to prove the main theorem
        reasoning: str = ""

    result = await decomposer.run_ai(inp=None, result_type=_DecomposeResult, max_turns=DECOMPOSER_MAX_TURNS)
    decompose_output : _DecomposeResult | None = result.output

    if decompose_output:
        if decompose_output.strategy == "direct":
            await agent._emit("message", f"[Prover] Strategy: direct attempt. Sketch: {decompose_output.proof_sketch}")
            return ProverTransition.SIMPLE_ENOUGH

        # Create axiom files deterministically from structured output
        cwd = _resolve(agent, "")
        state.axiom_files = []

        for i, axiom in enumerate(decompose_output.axioms or []):
            content = axiom.formalization
            if not content:
                desc_lines = "\n".join(f"-- {line}" for line in (axiom.description or "TODO").splitlines())
                content = f"{desc_lines}\nsorry\n"
            rel_path = _create_axiom_file(cwd, state.workspace, "axiom", i, axiom.name, content)
            state.axiom_files.append(rel_path)

        await agent._emit("message",
            f"[Prover] Decomposed: {len(state.axiom_files)} axioms. Sketch: {decompose_output.proof_sketch[:200]}")

        if state.axiom_files:
            return ProverTransition.DECOMPOSED

    return ProverTransition.SIMPLE_ENOUGH


async def _stage_direct_attempt(state: ProverState, agent) -> ProverTransition:
    """Single proof_writer on the stub file."""
    target = f"{state.workspace}/Stub.lean"

    @dataclass
    class _ProofResult:
        success: bool
        needs_decomposition: bool = False
        blocking_reason: str = ""

    async with swarm_agent("proof_writer", swarm=agent.swarm, cwd=agent._cwd, workspace=state.workspace) as writer:
        result = await writer.run(
            inp={"file": target, "theorem": state.theorem_name, "action": "Prove the sorry"},
            result_type=_ProofResult,
        )

    if result.output:
        if result.output.success:
            state.proved_files = [target]
            return ProverTransition.PROOF_FOUND
        if result.output.needs_decomposition:
            return ProverTransition.NEEDS_DECOMP

    return ProverTransition.FAILED


async def _stage_prove_lemmas(state: ProverState, agent) -> ProverTransition:
    """Spawn a child prover_orchestrator for each UNPROVED axiom (parallel, capped).
    Accumulates into proved_files — doesn't re-prove already proved ones."""

    # Only attempt unproved axioms
    to_prove = [f for f in state.axiom_files if f not in state.proved_files]
    if not to_prove:
        return ProverTransition.ALL_PROVED

    await agent._emit("message", f"[Prover] Proving {len(to_prove)} axioms ({len(state.proved_files)} already proved)...")

    semaphore = asyncio.Semaphore(MAX_PARALLEL_WRITERS)
    newly_proved = []
    failed = []

    cwd = _resolve(agent, "")

    async def _prove_one(axiom_file: str):
        async with semaphore:
            axiom_path = Path(axiom_file)
            child_workspace = f"{axiom_path.parent}/{axiom_path.stem}"
            (cwd / child_workspace).mkdir(parents=True, exist_ok=True)

            # Copy axiom file as the child's Stub.lean
            child_stub = cwd / child_workspace / "Stub.lean"
            shutil.copy2(cwd / axiom_file, child_stub)

            # Spawn child orchestrator scoped to its subdirectory
            async with swarm_agent("prover", swarm=agent.swarm, cwd=agent._cwd, workspace=child_workspace) as child:
                result = await child.run(
                    inp={
                        "theorem_file": axiom_file,
                        "theorem_name": axiom_path.stem,
                        "workspace": child_workspace,
                        "parent_agent": agent.spec.name,
                    },
                    result_type=None,
                )

            if result.output and result.output.get("stage") == "done":
                newly_proved.append(axiom_file)
                await agent._emit("message", f"[Prover] Child proved: {axiom_path.name}")
            else:
                failed.append(axiom_file)
                await agent._emit("message", f"[Prover] Child failed: {axiom_path.name}")

    await asyncio.gather(*[_prove_one(f) for f in to_prove])

    # Accumulate — don't replace
    state.proved_files.extend(newly_proved)
    total = len(state.axiom_files)
    await agent._emit("message", f"[Prover] Proved {len(state.proved_files)}/{total}")

    if len(state.proved_files) == total:
        return ProverTransition.ALL_PROVED
    if failed:
        return ProverTransition.HAS_SORRY
    return ProverTransition.STUCK


async def _stage_refactor(state: ProverState, agent) -> ProverTransition:
    """All-or-nothing refactoring: for each unproved file, axiomatize ALL its sorries
    or reject entirely and retry with a different approach.

    Flow per unproved file:
    1. Refactoring agent finds all sorries + goals in the file
    2. For each sorry: decomposer proposes axiom, we test it closes the sorry
    3. If ALL sorries have working axioms: edit file, verify, accept
    4. If ANY sorry can't be axiomatized: reject this file → retry
    """

    unproved = [f for f in state.axiom_files if f not in state.proved_files]
    await agent._emit("message", f"[Prover] Refactoring {len(unproved)} unproved files...")

    decomposer = await _get_internal(agent, "decomposer")
    cwd = _resolve(agent, "")

    @dataclass
    class _SorryGoal:
        file: str
        line: int
        goal: str

    @dataclass
    class _RefactorFindResult:
        sorries: list[_SorryGoal] = field(default_factory=list)
        cannot_refactor: bool = False

    @dataclass
    class _AxiomProposal:
        name: str = ""
        formalization: str = ""  # compilable axiom declaration only

    all_new_axioms = []
    any_success = False

    for unproved_file in unproved:
        await agent._emit("message", f"[Prover] Refactoring: {Path(unproved_file).name}")

        # Phase 1: Find all sorries in this file
        async with swarm_agent("refactoring_agent", swarm=agent.swarm, cwd=agent._cwd, workspace=state.workspace) as refactorer:
            find_result = await refactorer.run(
                inp={
                    "files": [unproved_file],
                    "workspace": state.workspace,
                    "action": (
                        "Use lean_hover_info at each sorry position to get the exact goal. "
                        "Return ALL sorries with file, line, and goal type."
                    ),
                },
                result_type=_RefactorFindResult,
            )

        if not find_result.output or find_result.output.cannot_refactor:
            await agent._emit("message", f"[Prover] Cannot refactor {Path(unproved_file).name}")
            return ProverTransition.CANNOT_REFACTOR

        sorries = find_result.output.sorries or []
        if not sorries:
            return ProverTransition.CANNOT_REFACTOR

        await agent._emit("message", f"[Prover] {Path(unproved_file).name}: {len(sorries)} sorries")

        # Phase 2: Decomposer proposes compilable axiom for each sorry
        axioms_for_file = []
        all_have_axioms = True

        for sorry in sorries:
            proposal = await decomposer.run_ai(
                inp=(
                    f"Propose a compilable axiom for this goal (from {sorry.file} line {sorry.line}):\n"
                    f"Goal: {sorry.goal}\n\n"
                    f"Just the axiom declaration (name + type). Verify it compiles with lean_run_code."
                ),
                result_type=_AxiomProposal,
                max_turns=DECOMPOSER_MAX_TURNS,
            )

            if proposal.output and proposal.output.formalization:
                axioms_for_file.append((sorry, proposal.output))
            else:
                await agent._emit("message",
                    f"[Prover] Cannot axiomatize sorry at {sorry.file}:{sorry.line} — rejecting file")
                all_have_axioms = False
                break

        if not all_have_axioms:
            return ProverTransition.CANNOT_REFACTOR

        # Phase 3: Write axiom files first (so they're importable)
        file_new_axioms = []
        for i, (_, axiom) in enumerate(axioms_for_file):
            global_idx = len(all_new_axioms) + i
            rel_path = _create_axiom_file(cwd, state.workspace, "refactor", global_idx, axiom.name, axiom.formalization)
            file_new_axioms.append(rel_path)

        # Phase 4: Refactoring agent imports axioms and tests closures (all-or-nothing)
        axiom_info = "\n".join(
            f"- Sorry at line {s.line}, goal: {s.goal}\n  Axiom: {a.name} (file: {file_new_axioms[i]})"
            for i, (s, a) in enumerate(axioms_for_file)
        )

        # Save a backup before refactoring agent touches the file
        backup_path = cwd / state.workspace / f"{Path(unproved_file).stem}.backup.lean"
        shutil.copy2(cwd / unproved_file, backup_path)

        @dataclass
        class _EditResult:
            success: bool
            error: str = ""

        async with swarm_agent("refactoring_agent", swarm=agent.swarm, cwd=agent._cwd, workspace=state.workspace) as refactorer:
            edit_result = await refactorer.run(
                inp={
                    "file": unproved_file,
                    "action": (
                        f"The axiom files have been created. Now:\n\n"
                        f"1. Read the file\n"
                        f"2. Add axiom imports at the top\n"
                        f"3. Replace EACH sorry with:\n"
                        f"   `first | exact <axiom> | rw [<axiom>] | simp [<axiom>] | apply <axiom>`\n"
                        f"   This lets Lean try each simple tactic and use whichever works.\n"
                        f"4. Write the entire file in one shot\n"
                        f"5. Run lean_verify once\n"
                        f"   - If it compiles with no sorry → success=true\n"
                        f"   - If it fails → the axioms don't fit → success=false\n\n"
                        f"Do NOT write complex proofs. Only the `first | ... ` combinator above.\n\n"
                        f"Axioms:\n{axiom_info}"
                    ),
                },
                result_type=_EditResult,
            )

        if not edit_result.output or not edit_result.output.success:
            await agent._emit("message", f"[Prover] Cannot close sorries in {Path(unproved_file).name} — reverting")
            # Revert file and clean up axiom files
            shutil.copy2(backup_path, cwd / unproved_file)
            backup_path.unlink(missing_ok=True)
            for f in file_new_axioms:
                (cwd / f).unlink(missing_ok=True)
            return ProverTransition.CANNOT_REFACTOR

        # Success — delete backup
        backup_path.unlink(missing_ok=True)

        state.proved_files.append(unproved_file)
        all_new_axioms.extend(file_new_axioms)
        any_success = True
        await agent._emit("message",
            f"[Prover] {Path(unproved_file).name} closed with {len(file_new_axioms)} new axioms to prove")

    if all_new_axioms:
        state.axiom_files.extend(all_new_axioms)
        await agent._emit("message", f"[Prover] Total new axioms to prove: {len(all_new_axioms)}")
        return ProverTransition.NEW_AXIOMS

    if any_success:
        return ProverTransition.NEW_AXIOMS

    return ProverTransition.CANNOT_REFACTOR


async def _stage_validate(state: ProverState, agent) -> ProverTransition:
    """Deep validation: compare each proved file against its original (stub).
    Checks: compiles, no sorry, theorem statements unchanged."""

    cwd = _resolve(agent, "")
    originals_dir = cwd / state.workspace / "_originals"

    @dataclass
    class _Validation:
        compiles: bool
        has_sorry: bool
        statements_match: bool

    issues = []
    semaphore = asyncio.Semaphore(MAX_PARALLEL_VALIDATORS)

    async def _validate_one(proved_file: str):
        proved_path = Path(proved_file)
        original_path = originals_dir / proved_path.name

        if not original_path.exists():
            issues.append(f"No original found for {proved_path.name} — cannot validate")
            return

        async with semaphore, swarm_agent("deep_proof_validator", swarm=agent.swarm, cwd=agent._cwd, workspace=state.workspace) as validator:
            result = await validator.run(
                inp={
                    "stub_file": f"{state.workspace}/_originals/{proved_path.name}",
                    "complete_file": proved_file,
                },
                result_type=_Validation,
            )

        if result.output:
            v = result.output
            if not v.compiles:
                issues.append(f"{proved_path.name}: doesn't compile")
            if v.has_sorry:
                issues.append(f"{proved_path.name}: still has sorry")
            if not v.statements_match:
                issues.append(f"{proved_path.name}: theorem statements changed")

    await asyncio.gather(*[_validate_one(f) for f in state.proved_files])

    if not issues:
        await agent._emit("message", f"[Prover] Validation passed: {len(state.proved_files)} files clean")
        return ProverTransition.VALID

    await agent._emit("message", f"[Prover] Validation failed: {issues}")
    return ProverTransition.INVALID


async def _stage_assemble(state: ProverState, agent) -> ProverTransition:
    """Mechanical assembly: copy each child's Stub.lean back into the parent axiom file.
    Then lean_verify the parent Stub.lean to confirm everything links up.
    No LLM needed — purely deterministic file operations."""

    cwd = _resolve(agent, "")
    await agent._emit("message", f"[Prover] Assembling {len(state.axiom_files)} axioms...")

    # For each axiom file, find the child workspace and copy its Stub.lean back
    for axiom_file in state.axiom_files:
        axiom_path = Path(axiom_file)
        child_workspace = axiom_path.parent / axiom_path.stem
        child_stub = cwd / child_workspace / "Stub.lean"

        if child_stub.exists():
            shutil.copy2(child_stub, cwd / axiom_file)
            await agent._emit("message", f"[Prover] Assembled: {axiom_path.name}")
        elif axiom_file in state.proved_files:
            # Proved in-place (by refactor stage) — already contains proof
            pass
        else:
            await agent._emit("message", f"[Prover] Assembly error: no proof found for {axiom_path.name}")
            return ProverTransition.FAILED

    # Final verification: parent Stub.lean should compile with all axioms now proved
    stub_rel = f"{state.workspace}/Stub.lean"
    original_rel = f"{state.workspace}/_originals/Stub.lean"

    if not (cwd / stub_rel).exists():
        await agent._emit("message", "[Prover] Assembly error: Stub.lean missing")
        return ProverTransition.FAILED

    @dataclass
    class _VerifyResult:
        compiles: bool
        has_sorry: bool

    async with swarm_agent("deep_proof_validator", swarm=agent.swarm, cwd=agent._cwd, workspace=state.workspace) as validator:
        result = await validator.run(
            inp={
                "stub_file": original_rel,
                "complete_file": stub_rel,
            },
            result_type=_VerifyResult,
        )

    if result.output and result.output.compiles and not result.output.has_sorry:
        await agent._emit("message", "[Prover] Assembly verified — proof complete!")
        return ProverTransition.ASSEMBLED

    issues = []
    if result.output:
        if not result.output.compiles:
            issues.append("doesn't compile")
        if result.output.has_sorry:
            issues.append("still has sorry")
    await agent._emit("message", f"[Prover] Assembly verification failed: {issues}")
    return ProverTransition.FAILED


async def _stage_retry(state: ProverState, agent) -> ProverTransition:
    """Increment attempt, reset, or give up."""
    state.attempt += 1
    await agent._emit("message", f"[Prover] Attempt {state.attempt}/{MAX_RETRIES}")

    if state.attempt >= MAX_RETRIES:
        return ProverTransition.MAX_RETRIES

    state.axiom_files = []
    state.proved_files = []
    return ProverTransition.NEW_APPROACH


# ─── Stage handler registry ──────────────────────────────────────────────────

STAGE_HANDLERS: dict[ProverStage, Any] = {
    ProverStage.DECOMPOSE: _stage_decompose,
    ProverStage.DIRECT_ATTEMPT: _stage_direct_attempt,
    ProverStage.PROVE_LEMMAS: _stage_prove_lemmas,
    ProverStage.REFACTOR: _stage_refactor,
    ProverStage.VALIDATE: _stage_validate,
    ProverStage.ASSEMBLE: _stage_assemble,
    ProverStage.RETRY: _stage_retry,
}


# ─── Internal agent management ───────────────────────────────────────────────

async def _get_internal(agent, which: str):
    """Get or create an internal agent (decomposer, assembler). Session persists."""

    attr = f"_po_{which}"
    attr_ctx = f"_po_{which}_ctx"

    if getattr(agent, attr, None) is None:
        ctx = swarm_agent(f"po_{which}", swarm=agent.swarm, cwd=agent._cwd)
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


# ─── Helpers ──────────────────────────────────────────────────────────────────

def _resolve(agent, rel_path: str) -> Path:
    """Resolve a relative workspace path to absolute using agent's cwd."""
    cwd = Path(agent._cwd) if agent._cwd else Path.cwd()
    return cwd / rel_path


def _create_axiom_file(cwd: Path, workspace_rel: str, prefix: str, index: int, name: str, content: str) -> str:
    """Create an axiom file in workspace and save a copy in _originals.
    Returns RELATIVE path (to cwd) for use in state and tool scoping."""
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


async def _notify_parent(agent, state: ProverState, message: str):
    try:
        await agent.channel_bus.send_to(
            f"{state.parent_agent}:messages",
            sender=agent.spec.name,
            payload=message,
        )
    except Exception:
        pass
    await agent._emit("message", f"[Prover → {state.parent_agent}]: {message}")
