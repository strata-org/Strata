"""Proof Orchestrator v3: Write-first, extract-later.

Pipeline:
  CEA → SPLIT → PROVE → EXTRACT → CHILD_POS → ASSEMBLE → VALIDATE → DONE

No pre-planned decomposition. The proof_writer writes as far as it can,
leaving sorries where stuck. The lemma_extractor then mechanically factors
those sorries into standalone helpers. Recurse on each helper.

Key agents (all internal to the PO, spawned dynamically):
- proof_writer_v2: persistent, writes proofs, receives guidance
- proof_guide: persistent, tracks strategy, advises on approach
- goal_analyzer: stateless, diagnoses stuck goals
- lemma_extractor: stateless, replaces sorries with helper refs
"""

from __future__ import annotations

import asyncio
import shutil
from dataclasses import dataclass, field
from enum import Enum
from pathlib import Path
from typing import Any, TypeVar

from .po_agents import (
    LoopOutcome, verified_loop, run_cea, swarm_checkpoint,
)
from .po_verify import verify_file_exists, verify_no_sorry, verify_split_complete
from .po_lean import get_lean_tools
from .po_util import write_checkpoint, write_progress, setup_child_workspace
from .verifiers.proof_writer_verifier import make_proof_writer_verifier
from .verifiers.lemma_extractor_verifier import make_extractor_verifier
from .verifiers.goal_analyzer_verifier import GoalAssessment
from .._helpers import swarm_agent

T = TypeVar("T")

MAX_RETRIES = 3
MAX_RECURSION_DEPTH = 3
WRITER_TURNS_PER_ATTEMPT = [50, 20, 10]  # decreasing budget per attempt
WRITER_CLEANUP_TURNS = 10
EXTRACTOR_MAX_TURNS = 50
MAX_PROOF_ATTEMPTS = 3


# ─── Enums ────────────────────────────────────────────────────────────────────

class Stage(str, Enum):
    SOUNDNESS = "soundness"
    SPLIT = "split"
    PROVE = "prove"
    EXTRACT = "extract"
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
    PROVED = "proved"
    HAS_SORRY = "has_sorry"
    NO_PROGRESS = "no_progress"
    EXTRACTED = "extracted"
    EXTRACT_FAILED = "extract_failed"
    ALL_PROVED = "all_proved"
    CHILD_FAILED = "child_failed"
    ASSEMBLED = "assembled"
    VALID = "valid"
    INVALID = "invalid"
    FAILED = "failed"
    NEW_APPROACH = "new_approach"
    MAX_RETRIES = "max_retries"


TRANSITIONS: dict[tuple[Stage, Trans], Stage] = {
    (Stage.SOUNDNESS, Trans.SOUND):        Stage.SPLIT,
    (Stage.SOUNDNESS, Trans.SKIPPED):      Stage.SPLIT,
    (Stage.SOUNDNESS, Trans.UNSOUND):      Stage.FAILED,

    (Stage.SPLIT, Trans.SPLIT_DONE):       Stage.PROVE,
    (Stage.SPLIT, Trans.SPLIT_FAILED):     Stage.PROVE,

    (Stage.PROVE, Trans.PROVED):           Stage.ASSEMBLE,
    (Stage.PROVE, Trans.HAS_SORRY):        Stage.EXTRACT,
    (Stage.PROVE, Trans.NO_PROGRESS):      Stage.RETRY,

    (Stage.EXTRACT, Trans.EXTRACTED):      Stage.CHILD_POS,
    (Stage.EXTRACT, Trans.EXTRACT_FAILED): Stage.RETRY,

    (Stage.CHILD_POS, Trans.ALL_PROVED):   Stage.ASSEMBLE,
    (Stage.CHILD_POS, Trans.CHILD_FAILED): Stage.RETRY,

    (Stage.ASSEMBLE, Trans.ASSEMBLED):     Stage.VALIDATE,
    (Stage.ASSEMBLE, Trans.FAILED):        Stage.RETRY,

    (Stage.VALIDATE, Trans.VALID):         Stage.DONE,
    (Stage.VALIDATE, Trans.INVALID):       Stage.RETRY,

    (Stage.RETRY, Trans.NEW_APPROACH):     Stage.PROVE,
    (Stage.RETRY, Trans.MAX_RETRIES):      Stage.FAILED,
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

    decomposed_files: list[str] = field(default_factory=list)
    proved_files: list[str] = field(default_factory=list)

    attempt: int = 0
    parent_agent: str = "TaskManager"
    failure_reason: str = ""
    last_failure_details: str = ""
    agent_name: str = ""
    internal_agents: dict = field(default_factory=dict)


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

    state.agent_name = agent.spec.name
    agent._workflow_state = state
    await agent._emit("message", f"[PO] Starting: {theorem_name} in {workspace_rel} (depth={depth})")

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
                state.stage = Stage.FAILED
            else:
                state.stage = Stage.RETRY
            write_checkpoint(cwd, state)

    await _notify_parent(agent, state,
        f"Proof {'complete' if state.stage == Stage.DONE else 'failed'}: {theorem_file}")
    await _cleanup_all(agent)

    result = AgentResult(name=agent.spec.name, status=AgentStatus.COMPLETED)
    result.output = {"stage": state.stage.value, "theorem_file": theorem_file,
                     "attempts": state.attempt, "details": state.last_failure_details}
    return result


# ─── Stage: soundness ─────────────────────────────────────────────────────────

async def _stage_soundness(state: ProverState, agent) -> Trans:
    if state.skip_soundness:
        return Trans.SKIPPED
    verdict = await run_cea(agent, state.workspace, f"{state.workspace}/Stub.lean", state.theorem_name)
    if verdict and not verdict.sound and verdict.confidence == "high":
        state.failure_reason = "unsound"
        await agent._emit("message", f"[PO] UNSOUND: {verdict.counterexample}")
        return Trans.UNSOUND
    return Trans.SOUND


# ─── Stage: split ────────────────────────────────────────────────────────────

async def _stage_split(state: ProverState, agent) -> Trans:
    cwd = _resolve(agent)
    if state.depth > 0 and verify_split_complete(cwd, state.workspace):
        return Trans.SPLIT_DONE

    from .po_agents import run_splitter
    outcome = await run_splitter(agent, state.workspace, f"{state.workspace}/Stub.lean")
    if outcome.success:
        return Trans.SPLIT_DONE
    if verify_file_exists(cwd, f"{state.workspace}/Stub/Def.lean"):
        return Trans.SPLIT_DONE
    return Trans.SPLIT_FAILED


# ─── Stage: prove ────────────────────────────────────────────────────────────

async def _stage_prove(state: ProverState, agent) -> Trans:
    """proof_writer attempts the theorem. PO orchestrates guidance between rounds."""
    cwd = _resolve(agent)
    stub_rel = f"{state.workspace}/Stub.lean"
    tools = get_lean_tools()

    # Save original for progress detection
    original_content = (cwd / stub_rel).read_text()

    # Ensure internal agents exist
    writer = await _get_writer(agent, state)
    guide = await _get_guide(agent, state)

    # Build verifier (pure deterministic checks)
    verify_fn = make_proof_writer_verifier(stub_rel, original_content, state.workspace, state.theorem_name)

    action = _build_initial_action(state)

    for attempt in range(MAX_PROOF_ATTEMPTS):
        turns = WRITER_TURNS_PER_ATTEMPT[min(attempt, len(WRITER_TURNS_PER_ATTEMPT) - 1)]
        await agent._emit("message", f"[PO] Prove attempt {attempt + 1}/{MAX_PROOF_ATTEMPTS} ({turns} turns)")

        # Inject turn budget into the action message
        if attempt == 0:
            action_with_budget = f"{action}\n\nYou have {turns} turns for this attempt. Be efficient."
        else:
            action_with_budget = f"{action}\n\nYou have {turns} turns remaining. Focus on the most impactful changes."

        # Run writer with verified_loop
        outcome = await verified_loop(
            agent_ctx=writer,
            initial_input=action_with_budget,
            verify=verify_fn,
            max_rounds=2,
            max_turns=turns,
            use_run_ai=True,
        )

        # Check: sorry-free?
        if not tools.has_sorry(stub_rel):
            await agent._emit("message", "[PO] Proof complete ✅")
            return Trans.PROVED

        # Check: file unchanged? (no progress at all)
        current_content = (cwd / stub_rel).read_text()
        if current_content.strip() == original_content.strip():
            await agent._emit("message", "[PO] No progress — file unchanged")
            state.last_failure_details = "Writer made no changes"
            return Trans.NO_PROGRESS

        # Check: compiles?
        cr = tools.check_compiles(stub_rel)
        if not cr.success:
            # Try cleanup round
            await agent._emit("message", "[PO] File doesn't compile — cleanup round")
            await writer.run_ai(
                inp="Your file does not compile. Fix compilation errors ONLY. Do not add new proof content. Just make it compile (sorry is fine).",
                max_turns=WRITER_CLEANUP_TURNS,
            )
            cr = tools.check_compiles(stub_rel)
            if not cr.success:
                # Revert to original
                (cwd / stub_rel).write_text(original_content)
                state.last_failure_details = "Writer broke compilation, could not fix"
                return Trans.NO_PROGRESS

        # Has sorry but made progress — last attempt? Then go to EXTRACT
        if attempt >= MAX_PROOF_ATTEMPTS - 1:
            break

        # Not the last attempt — consult guide + analyzer for next round
        sorry_info = tools.get_sorries_by_theorem(stub_rel)
        await agent._emit("message", f"[PO] Still has sorry: {sorry_info}. Consulting guide...")

        # Ask goal_analyzer (stateless) about stuck goals
        diagnosis = await _run_goal_analyzer(agent, state, stub_rel, sorry_info)

        if diagnosis and diagnosis.assessment == "contradictory":
            await agent._emit("message", f"[PO] Goal diagnosed as contradictory: {diagnosis.reasoning}")
            state.last_failure_details = f"Contradictory goal: {diagnosis.reasoning}"
            return Trans.NO_PROGRESS

        # Ask proof_guide for strategy
        diagnosis_text = f"Assessment: {diagnosis.assessment}. {diagnosis.reasoning}" if diagnosis else "No diagnosis available."
        advice_result = await guide.run_ai(
            inp=f"Writer is stuck after attempt {attempt + 1}.\nGoals with sorry: {sorry_info}\nDiagnosis: {diagnosis_text}\nWhat should it try next?",
        )
        advice = advice_result.raw_result or "Try a different approach."

        # Build next round's action with guidance
        action = f"STRATEGY ADVICE from your proof guide:\n{advice}\n\nApply this advice and continue the proof."
        await agent._emit("message", f"[PO] Feeding guidance to writer...")

    # Writer made progress but has sorry remaining → go to EXTRACT
    await agent._emit("message", "[PO] Proof has sorry remaining → extracting helpers")
    return Trans.HAS_SORRY


# ─── Stage: extract ──────────────────────────────────────────────────────────

async def _stage_extract(state: ProverState, agent) -> Trans:
    """lemma_extractor replaces sorries in main theorem with helper lemma refs."""
    cwd = _resolve(agent)
    stub_rel = f"{state.workspace}/Stub.lean"
    tools = get_lean_tools()

    # Check: does the main theorem already have no sorry? (writer may have finished)
    split = tools.split_theorems(stub_rel)
    if not split.error and split.blocks:
        main_block = split.blocks[-1]
        if not main_block.has_sorry:
            # Main theorem is sorry-free, but helpers above it may have sorry
            # That's fine — go to CHILD_POS to prove them
            state.decomposed_files = _collect_decomposed(cwd, state.workspace)
            if state.decomposed_files:
                return Trans.EXTRACTED
            return Trans.EXTRACTED  # no decomposed but main is clean → assembly

    # Run lemma_extractor with verifier
    verify_fn = make_extractor_verifier(stub_rel, state.theorem_name, state.workspace)

    async with swarm_agent("lemma_extractor", swarm=agent.swarm, cwd=agent._cwd,
                           workspace=state.workspace,
                           can_see=["SearchAgent"]) as extractor:
        outcome = await verified_loop(
            agent_ctx=extractor,
            initial_input={
                "file": stub_rel,
                "main_theorem": state.theorem_name,
                "target_folder": f"{state.workspace}/decomposed",
                "action": (
                    f"Extract all sorries from the main theorem '{state.theorem_name}' into helper lemma files. "
                    f"Use get_sorries_by_theorem to find them, lean_goal to see each goal, "
                    f"and write_helper_lemma to create each helper and wire it in."
                ),
            },
            verify=verify_fn,
            max_rounds=3,
            max_turns=EXTRACTOR_MAX_TURNS,
            use_run_ai=False,
        )

    if outcome.success:
        state.decomposed_files = _collect_decomposed(cwd, state.workspace)
        await agent._emit("message", f"[PO] Extracted {len(state.decomposed_files)} helpers")
        return Trans.EXTRACTED

    state.last_failure_details = f"Extraction failed: {outcome.last_error}"
    return Trans.EXTRACT_FAILED


# ─── Stage: child_pos ────────────────────────────────────────────────────────

async def _stage_child_pos(state: ProverState, agent) -> Trans:
    """Sequential child POs for each helper in decomposed/."""
    cwd = _resolve(agent)
    import json as _json

    remaining = [f for f in state.decomposed_files if f not in state.proved_files]
    if not remaining:
        return Trans.ALL_PROVED

    await agent._emit("message", f"[PO] Running {len(remaining)} child POs (sequential, depth={state.depth + 1})")

    failed = []
    for lemma_file in remaining:
        # Check if already done from prior run
        child_workspace_rel = str(Path(lemma_file).parent / Path(lemma_file).stem)
        child_cp = cwd / child_workspace_rel / "po_checkpoint.json"
        if child_cp.exists():
            try:
                cp_data = _json.loads(child_cp.read_text())
                if cp_data.get("stage") == "done":
                    state.proved_files.append(lemma_file)
                    await agent._emit("message", f"[PO] ✅ {Path(lemma_file).name}: already proved (checkpoint)")
                    write_checkpoint(cwd, state)
                    continue
            except (ValueError, KeyError):
                pass

        child_workspace = setup_child_workspace(cwd, lemma_file, state.workspace)

        # Run child PO
        from .po_agents import run_child_po
        result = await run_child_po(agent, child_workspace, lemma_file, state.depth + 1)

        if result and result.get("stage") == "done":
            state.proved_files.append(lemma_file)
            await agent._emit("message", f"[PO] ✅ Child proved: {Path(lemma_file).name}")
            write_checkpoint(cwd, state)
            await swarm_checkpoint(agent, f"child_proved:{Path(lemma_file).name}")
        else:
            reason = result.get("details", "unknown") if result else "no output"
            failed.append((lemma_file, reason))
            await agent._emit("message", f"[PO] ❌ Child failed: {Path(lemma_file).name}: {reason}")

    if failed:
        state.last_failure_details = f"{len(failed)} children failed: {[Path(f).name for f, _ in failed[:3]]}"
        return Trans.CHILD_FAILED

    return Trans.ALL_PROVED


# ─── Stage: assemble ─────────────────────────────────────────────────────────

async def _stage_assemble(state: ProverState, agent) -> Trans:
    """Bottom-up assembly: merge Def.lean, copy proofs back, rewrite imports, verify.

    Strategy (bottom-up by path depth):
    1. For each proved child: copy its Stub.lean back to parent's lemma file
    2. Merge all child Def.lean into the top-level Def.lean
    3. Rewrite all local Stub.Def imports to point to top-level Def.lean
    4. Build all decomposed files (produce .olean)
    5. Verify Stub.lean compiles sorry-free
    """
    import subprocess
    cwd = _resolve(agent)
    tools = get_lean_tools()
    stub_rel = f"{state.workspace}/Stub.lean"
    top_module = state.workspace.replace("/", ".")
    top_def = cwd / state.workspace / "Stub" / "Def.lean"

    # ── Step 1: Copy child Stub.lean → parent's lemma file (bottom-up) ──
    for f in sorted(state.proved_files, key=lambda p: len(Path(p).parts), reverse=True):
        lemma_path = Path(f)
        child_workspace = lemma_path.parent / lemma_path.stem
        child_stub = cwd / child_workspace / "Stub.lean"
        if child_stub.exists():
            shutil.copy2(child_stub, cwd / f)
            await agent._emit("message", f"[PO] Assembled: {lemma_path.name} ← child Stub.lean")

    # ── Step 2: Merge all child Def.lean into top-level (bottom-up by depth) ──
    if top_def.exists():
        top_def_content = top_def.read_text()
        child_defs = sorted(
            (cwd / state.workspace).rglob("Stub/Def.lean"),
            key=lambda p: len(p.parts),
            reverse=True,
        )
        for child_def in child_defs:
            if child_def == top_def:
                continue
            child_content = child_def.read_text()
            if child_content.strip() == top_def_content.strip():
                continue
            new_lines = [l for l in child_content.splitlines()
                         if l.strip() and l not in top_def_content and not l.strip().startswith("import ")]
            if new_lines:
                top_def_content = top_def_content.rstrip() + "\n" + "\n".join(new_lines) + "\n"
                top_def.write_text(top_def_content)
                await agent._emit("message", f"[PO] Merged Def.lean from {child_def.relative_to(cwd)}")

    # ── Step 3: Rewrite all Stub.Def imports to top-level ──
    for lean_file in (cwd / state.workspace).rglob("*.lean"):
        if lean_file.name == "Def.lean":
            continue
        content = lean_file.read_text()
        rewritten = False
        new_lines = []
        for line in content.splitlines():
            stripped = line.strip()
            if (stripped.startswith("import ") and
                    "Stub.Def" in stripped and
                    stripped != f"import {top_module}.Stub.Def"):
                new_lines.append(f"import {top_module}.Stub.Def")
                rewritten = True
            else:
                new_lines.append(line)
        if rewritten:
            lean_file.write_text("\n".join(new_lines) + "\n")

    # ── Step 4: Build all decomposed files ──
    decomposed_dir = cwd / state.workspace / "decomposed"
    if decomposed_dir.exists():
        for helper in decomposed_dir.glob("lemma_helper_*.lean"):
            helper_module = str(helper.relative_to(cwd)).replace("/", ".").removesuffix(".lean")
            subprocess.run(["lake", "build", helper_module],
                          cwd=str(cwd), capture_output=True, timeout=120)

    # ── Step 5: Verify Stub.lean ──
    cr = tools.check_compiles(stub_rel)
    if cr.success and not tools.has_sorry(stub_rel):
        await agent._emit("message", "[PO] Assembly verified ✅")
        return Trans.ASSEMBLED

    if not cr.success:
        state.last_failure_details = "Stub.lean doesn't compile after assembly"
    else:
        state.last_failure_details = "Stub.lean still has sorry after assembly"
    return Trans.FAILED


# ─── Stage: validate ─────────────────────────────────────────────────────────

async def _stage_validate(state: ProverState, agent) -> Trans:
    """Final check: compiles, no sorry, no axiom."""
    stub_rel = f"{state.workspace}/Stub.lean"
    tools = get_lean_tools()

    cr = tools.check_compiles(stub_rel)
    if not cr.success:
        state.last_failure_details = "Validation: doesn't compile"
        return Trans.INVALID

    if tools.has_sorry(stub_rel):
        state.last_failure_details = "Validation: still has sorry"
        return Trans.INVALID

    ax = tools.check_axioms(stub_rel)
    if ax.has_axiom:
        state.last_failure_details = f"Validation: uses axiom ({ax.axiom_names})"
        return Trans.INVALID

    await agent._emit("message", "[PO] Validation passed ✅")
    return Trans.VALID


# ─── Stage: retry ────────────────────────────────────────────────────────────

async def _stage_retry(state: ProverState, agent) -> Trans:
    state.attempt += 1
    if state.attempt >= MAX_RETRIES:
        return Trans.MAX_RETRIES

    cwd = _resolve(agent)
    await agent._emit("message", f"[PO] Retry {state.attempt}/{MAX_RETRIES}")

    # Archive old decomposed/
    decomposed_dir = cwd / state.workspace / "decomposed"
    if decomposed_dir.exists():
        target = cwd / state.workspace / f"decomposed_attempt_{state.attempt}"
        if target.exists():
            shutil.rmtree(target)
        decomposed_dir.rename(target)
    decomposed_dir.mkdir(parents=True, exist_ok=True)

    # Restore Stub.lean from clean backup
    stub_clean = cwd / state.workspace / "Stub.clean.lean"
    stub_path = cwd / state.workspace / "Stub.lean"
    if stub_clean.exists():
        shutil.copy2(stub_clean, stub_path)

    # Notify guide about the failure (it accumulates context)
    guide = await _get_guide(agent, state)
    await guide.run_ai(
        inp=f"RETRY #{state.attempt}: Previous approach failed. Details: {state.last_failure_details}. "
            f"Remember this — don't suggest the same approach again.",
    )

    # Keep proved files from prior attempts
    state.decomposed_files = []

    return Trans.NEW_APPROACH


# ─── Handler registry ────────────────────────────────────────────────────────

HANDLERS: dict[Stage, Any] = {
    Stage.SOUNDNESS: _stage_soundness,
    Stage.SPLIT: _stage_split,
    Stage.PROVE: _stage_prove,
    Stage.EXTRACT: _stage_extract,
    Stage.CHILD_POS: _stage_child_pos,
    Stage.ASSEMBLE: _stage_assemble,
    Stage.VALIDATE: _stage_validate,
    Stage.RETRY: _stage_retry,
}


# ─── Internal agent management ───────────────────────────────────────────────

async def _get_writer(agent, state: ProverState):
    """Get or create the persistent proof_writer_v2."""
    attr = "_po_writer"
    if getattr(agent, attr, None) is None:
        # Need guide's name for template
        guide = await _get_guide(agent, state)
        ctx = swarm_agent(
            "proof_writer_v2", swarm=agent.swarm, cwd=agent._cwd,
            workspace=state.workspace,
            template_vars={
                "proof_guide": guide.spec.name,
                "goal_analyzer": "goal_analyzer",
            },
            can_see=["SearchAgent", guide.spec.name],
        )
        internal = await ctx.__aenter__()
        setattr(agent, f"{attr}_ctx", ctx)
        setattr(agent, attr, internal)
        state.internal_agents["writer"] = internal.spec.name
    return getattr(agent, attr)


async def _get_guide(agent, state: ProverState):
    """Get or create the persistent proof_guide."""
    attr = "_po_guide"
    if getattr(agent, attr, None) is None:
        ctx = swarm_agent(
            "proof_guide", swarm=agent.swarm, cwd=agent._cwd,
            workspace=state.workspace,
            can_see=["SearchAgent"],
        )
        internal = await ctx.__aenter__()
        setattr(agent, f"{attr}_ctx", ctx)
        setattr(agent, attr, internal)
        state.internal_agents["guide"] = internal.spec.name
    return getattr(agent, attr)


async def _run_goal_analyzer(agent, state: ProverState, stub_rel: str, sorry_info: dict) -> GoalAssessment | None:
    """Run goal_analyzer (stateless) on stuck goals."""
    # Pick the first stuck goal for analysis
    first_thm = next(iter(sorry_info), None)
    if not first_thm:
        return None
    first_sorry = sorry_info[first_thm][0] if sorry_info[first_thm] else None
    if not first_sorry:
        return None

    async with swarm_agent("goal_analyzer", swarm=agent.swarm, cwd=agent._cwd,
                           workspace=state.workspace,
                           can_see=["SearchAgent"]) as analyzer:
        result = await analyzer.run(
            inp={
                "file_path": stub_rel,
                "theorem_name": first_thm,
                "sorry_line": first_sorry["line"],
                "sorry_col": first_sorry["col"],
                "action": (
                    f"Analyze the sorry goal in theorem '{first_thm}' at line {first_sorry['line']}. "
                    f"Use lean_goal to see the exact goal type and context. "
                    f"Determine: is it provable, needs strengthening, contradictory, or a bad goal?"
                ),
            },
            result_type=GoalAssessment,
        )
    return result.output


async def _cleanup_all(agent):
    """Cleanup all internal agents."""
    for attr in ("_po_writer", "_po_guide"):
        ctx_attr = f"{attr}_ctx"
        if getattr(agent, attr, None) is not None:
            ctx = getattr(agent, ctx_attr, None)
            if ctx:
                await ctx.__aexit__(None, None, None)
            setattr(agent, ctx_attr, None)
            setattr(agent, attr, None)


# ─── Helpers ─────────────────────────────────────────────────────────────────

def _resolve(agent) -> Path:
    return Path(agent._cwd) if agent._cwd else Path.cwd()


def _build_initial_action(state: ProverState) -> str:
    """Build the first action message for proof_writer."""
    stub_rel = f"{state.workspace}/Stub.lean"
    msg = (
        f"Prove the theorem in {stub_rel}.\n"
        f"Theorem name: {state.theorem_name}\n\n"
        f"APPROACH:\n"
        f"1. Read the file and understand the theorem\n"
        f"2. Use lean_goal at the sorry to see what needs proving\n"
        f"3. Ask SearchAgent about the types and available lemmas\n"
        f"4. Write the proof — factor hard sub-goals into helper theorems with sorry\n"
        f"5. The main theorem's proof body must be sorry-free (helpers can have sorry)\n"
    )
    if state.attempt > 0:
        msg += (
            f"\nThis is attempt {state.attempt + 1}. Previous attempt failed:\n"
            f"{state.last_failure_details}\n"
            f"Try a DIFFERENT approach.\n"
        )
    return msg


def _collect_decomposed(cwd: Path, workspace: str) -> list[str]:
    """Collect helper files from decomposed/ that have sorry."""
    tools = get_lean_tools()
    decomposed_dir = cwd / workspace / "decomposed"
    if not decomposed_dir.exists():
        return []
    files = []
    for f in decomposed_dir.glob("lemma_helper_*.lean"):
        rel = f"{workspace}/decomposed/{f.name}"
        if tools.has_sorry(rel):
            files.append(rel)
    return files


async def _notify_parent(agent, state, message):
    try:
        await agent.channel_bus.send_to(f"{state.parent_agent}:messages",
                                         sender=agent.spec.name, payload=message)
    except Exception:
        pass
