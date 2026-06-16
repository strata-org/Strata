"""Proof Orchestrator v3: Write-first, extract-later.

Pipeline:
  CEA → SPLIT → PROVE → EXTRACT → CHILD_POS → ASSEMBLE → VALIDATE → DONE

No pre-planned decomposition. The proof_writer writes as far as it can,
leaving sorries where stuck. The lemma_extractor then mechanically factors
those sorries into standalone helpers. Recurse on each helper.

Key agents (all internal to the PO, spawned dynamically):
- proof_writer_v2: persistent, writes proofs, receives guidance
- proof_guide: persistent, tracks strategy, advises on approach
- proof_guide: persistent, diagnoses stuck goals + provides strategy
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
from .._helpers import swarm_agent

T = TypeVar("T")

MAX_RETRIES = 3
MAX_RECURSION_DEPTH = 3
WRITER_TURNS_PER_ATTEMPT = [75, 30, 15]  # decreasing budget per attempt
GRACE_TURNS_PER_ATTEMPT = 20  # turns per grace attempt (sorry wrap-up phase)
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

    # Copy cheat sheet into workspace so all agents (guide, writer) can read it
    cheat_src = cwd / "StrataAgent" / "strataswarm" / "agent_specs" / "StrataProofCheatSheet.md"
    cheat_dst = workspace_abs / "StrataProofCheatSheet.md"
    if cheat_src.exists() and not cheat_dst.exists():
        shutil.copy2(cheat_src, cheat_dst)

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

    # Clean up theorem_name (TM sometimes passes "Theorems: ['name']" format)
    if state.theorem_name and "'" in state.theorem_name:
        import re
        match = re.search(r"'([^']+)'", state.theorem_name)
        if match:
            state.theorem_name = match.group(1)

    state.agent_name = agent.spec.name
    agent._workflow_state = state
    await agent._emit("message", f"[PO] Starting: {state.theorem_name} in {workspace_rel} (depth={depth})")

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

    # Get initial strategy from guide BEFORE first attempt
    await agent._emit("message", "[PO] Consulting proof guide for initial strategy...")
    initial_advice = await guide.run_ai(
        inp=(
            f"A proof_writer is about to prove theorem '{state.theorem_name}' in {stub_rel}.\n"
            f"Read the cheat sheet and then advise on the best approach.\n"
            f"Consider: what proof technique fits this theorem's structure? "
            f"What common pitfalls should the writer avoid?"
        ),
    )
    guide_preamble = initial_advice.raw_result or ""

    action = _build_initial_action(state)
    if guide_preamble:
        action = f"STRATEGY ADVICE from your proof guide:\n{guide_preamble}\n\n{action}"

    # ── Phase 1: Initial attempts (prove directly) ──
    for attempt in range(MAX_PROOF_ATTEMPTS):
        turns = WRITER_TURNS_PER_ATTEMPT[min(attempt, len(WRITER_TURNS_PER_ATTEMPT) - 1)]
        await agent._emit("message", f"[PO] Prove attempt {attempt + 1}/{MAX_PROOF_ATTEMPTS} ({turns} turns)")

        action_with_budget = f"{action}\n\nYou have {turns} turns."

        outcome = await verified_loop(
            agent_ctx=writer,
            initial_input=action_with_budget,
            verify=verify_fn,
            max_rounds=2,
            max_turns=turns,
            use_run_ai=True,
        )

        # Check results and update progress
        result = _check_attempt_result(tools, stub_rel, cwd, original_content)
        write_progress(cwd, state)

        if result["sorry_free"]:
            await agent._emit("message", "[PO] Proof complete ✅")
            return Trans.PROVED
        if result["unchanged"]:
            await agent._emit("message", "[PO] No progress — file unchanged")
            state.last_failure_details = "Writer made no changes"
            return Trans.NO_PROGRESS
        if result["broken"]:
            await agent._emit("message", "[PO] File doesn't compile — cleanup round")
            await writer.run_ai(
                inp="Your file does not compile. Fix compilation errors ONLY. Do not add new proof content. Just make it compile (sorry is fine).",
                max_turns=WRITER_CLEANUP_TURNS,
            )
            if not tools.check_compiles(stub_rel).success:
                (cwd / stub_rel).write_text(original_content)
                state.last_failure_details = "Writer broke compilation, could not fix"
                return Trans.NO_PROGRESS

        # Last initial attempt → move to grace phase
        if attempt >= MAX_PROOF_ATTEMPTS - 1:
            break

        # Consult guide (which now also diagnoses goals) for next round
        sorry_info = tools.get_sorries_by_theorem(stub_rel)
        await agent._emit("message", f"[PO] Still has {result['sorry_count']} sorry. Consulting guide...")

        # Build sorry position details for guide
        first_thm = next(iter(sorry_info), None)
        sorry_detail = ""
        if first_thm and sorry_info[first_thm]:
            pos = sorry_info[first_thm][0]
            sorry_detail = f"\nUse lean_goal at {stub_rel} line {pos['line']} col {pos['col']} to see the stuck goal."

        advice_result = await guide.run_ai(
            inp=(
                f"Writer is stuck after attempt {attempt + 1}.\n"
                f"File: {stub_rel}\n"
                f"Goals with sorry: {sorry_info}\n"
                f"{sorry_detail}\n"
                f"Diagnose the stuck goals (use lean_goal) and advise what to try next.\n"
                f"If a goal looks contradictory or needs strengthening, say so clearly."
            ),
        )
        advice = advice_result.raw_result or "Try a different approach."

        if "contradictory" in advice.lower() and "not provable" in advice.lower():
            await agent._emit("message", f"[PO] Guide says goal is contradictory")
            state.last_failure_details = f"Guide diagnosed contradictory goal"
            return Trans.NO_PROGRESS

        action = f"STRATEGY ADVICE from your proof guide:\n{advice}\n\nApply this advice and continue the proof."
        await agent._emit("message", f"[PO] Feeding guidance to writer...")

    # ── Phase 2: Grace attempts (wrap up — reduce sorry in main theorem) ──
    # Track sorry in the MAIN theorem — factoring into helpers reduces this count
    sorry_info = tools.get_sorries_by_theorem(stub_rel)
    main_sorry_count = len(sorry_info.get(state.theorem_name, []))
    max_grace = main_sorry_count  # at most one grace attempt per sorry in main

    if main_sorry_count == 0:
        # Main theorem already sorry-free (helpers have sorry) → go to extract
        await agent._emit("message", "[PO] Main theorem sorry-free → extracting helpers")
        return Trans.HAS_SORRY

    await agent._emit("message", f"[PO] Phase 2: wrap-up ({main_sorry_count} sorry in main theorem, up to {max_grace} grace attempts)")
    prev_main_sorry = main_sorry_count

    for grace in range(max_grace):
        grace_turns = GRACE_TURNS_PER_ATTEMPT
        await agent._emit("message", f"[PO] Grace attempt {grace + 1}/{max_grace} ({grace_turns} turns)")

        sorry_info = tools.get_sorries_by_theorem(stub_rel)
        action_with_budget = (
            f"WRAP UP — grace attempt {grace + 1}. You have {grace_turns} turns.\n\n"
            f"Remaining sorry in main theorem '{state.theorem_name}': {sorry_info.get(state.theorem_name, [])}\n\n"
            f"For each sorry you cannot close directly, factor it into a helper theorem:\n"
            f"  theorem helper_<name> (<params>) : <goal_type> := by sorry\n"
            f"Then use `exact helper_<name> ...` in the main proof.\n\n"
            f"The MAIN theorem '{state.theorem_name}' must be sorry-free when you're done.\n"
            f"Helpers CAN have sorry. Keep everything in one file. Make it compile."
        )

        outcome = await verified_loop(
            agent_ctx=writer,
            initial_input=action_with_budget,
            verify=verify_fn,
            max_rounds=2,
            max_turns=grace_turns,
            use_run_ai=True,
        )

        if not tools.has_sorry(stub_rel):
            await agent._emit("message", "[PO] Proof complete ✅")
            return Trans.PROVED

        cr = tools.check_compiles(stub_rel)
        if not cr.success:
            await writer.run_ai(
                inp="Your file does not compile. Fix compilation errors ONLY. Just make it compile (sorry is fine).",
                max_turns=WRITER_CLEANUP_TURNS,
            )
            if not tools.check_compiles(stub_rel).success:
                (cwd / stub_rel).write_text(original_content)
                state.last_failure_details = "Writer broke compilation during wrap-up"
                return Trans.NO_PROGRESS

        # Did we reduce sorry in the MAIN theorem?
        sorry_info = tools.get_sorries_by_theorem(stub_rel)
        current_main_sorry = len(sorry_info.get(state.theorem_name, []))
        write_progress(cwd, state)

        if current_main_sorry >= prev_main_sorry:
            await agent._emit("message", f"[PO] No reduction in main theorem sorry ({current_main_sorry} remaining) — stopping")
            break

        await agent._emit("message", f"[PO] Main theorem sorry: {prev_main_sorry} → {current_main_sorry}")
        prev_main_sorry = current_main_sorry

        if current_main_sorry == 0:
            await agent._emit("message", "[PO] Main theorem sorry-free → extracting helpers")
            return Trans.HAS_SORRY

    # Ensure file compiles before going to extract
    cr = tools.check_compiles(stub_rel)
    if not cr.success:
        await agent._emit("message", "[PO] File doesn't compile — final cleanup")
        await writer.run_ai(
            inp="Your file does not compile. Fix ALL compilation errors. Do not add new proof content. Replace any references to undefined lemmas with sorry. The file MUST compile.",
            max_turns=WRITER_CLEANUP_TURNS,
        )
        if not tools.check_compiles(stub_rel).success:
            (cwd / stub_rel).write_text(original_content)
            state.last_failure_details = "File doesn't compile after all attempts"
            return Trans.NO_PROGRESS

    sorry_info = tools.get_sorries_by_theorem(stub_rel)
    main_sorries = len(sorry_info.get(state.theorem_name, []))
    if main_sorries == 0:
        await agent._emit("message", "[PO] Main theorem sorry-free → extracting helpers")
    else:
        await agent._emit("message", f"[PO] Main theorem still has {main_sorries} sorry → will extract what we can")
    return Trans.HAS_SORRY


# ─── Stage: extract ──────────────────────────────────────────────────────────

async def _stage_extract(state: ProverState, agent) -> Trans:
    """Mechanical extraction: split sorry theorems into decomposed/ files."""
    cwd = _resolve(agent)
    stub_rel = f"{state.workspace}/Stub.lean"
    tools = get_lean_tools()

    # Precondition: file must compile
    if not tools.check_compiles(stub_rel).success:
        state.last_failure_details = "File doesn't compile — cannot extract"
        return Trans.EXTRACT_FAILED

    # Nothing to extract? (only main theorem remains, no helpers)
    split = tools.split_theorems(stub_rel)
    helper_blocks = [b for b in split.blocks if b.name != state.theorem_name]
    if not helper_blocks:
        state.decomposed_files = []
        return Trans.EXTRACTED

    # Mechanical extraction — one file per theorem (sorry or not)
    decomposed_dir = cwd / state.workspace / "decomposed"
    decomposed_dir.mkdir(parents=True, exist_ok=True)

    extract_result = tools.extract_sorry_theorems(stub_rel,
        output_dir=f"{state.workspace}/decomposed",
        exclude={state.theorem_name},
        extract_all=True)

    if not extract_result.created_files:
        state.last_failure_details = extract_result.error or "No sorry theorems to extract"
        return Trans.EXTRACT_FAILED

    # Check all extracted files compile
    failed_dir = cwd / state.workspace / "decomposed" / "extraction_failed"
    if failed_dir.exists() and list(failed_dir.glob("*.lean")):
        # Some failed — this means mechanical extraction has issues
        # Clean up and retry the whole prove stage
        state.last_failure_details = f"Extraction produced non-compilable files"
        shutil.rmtree(decomposed_dir)
        decomposed_dir.mkdir(parents=True, exist_ok=True)
        return Trans.EXTRACT_FAILED

    # Rewrite Stub.lean: remove extracted helpers, add imports
    _rewrite_stub_after_extraction(cwd, stub_rel, extract_result, tools, state)

    # Verify Stub.lean still compiles after rewrite
    if not tools.check_compiles(stub_rel).success:
        # Rewrite broke it — revert and fail
        (cwd / stub_rel).write_text((cwd / state.workspace / "_originals" / "Stub.lean").read_text())
        shutil.rmtree(decomposed_dir)
        decomposed_dir.mkdir(parents=True, exist_ok=True)
        state.last_failure_details = "Stub.lean doesn't compile after extraction rewrite"
        return Trans.EXTRACT_FAILED

    state.decomposed_files = extract_result.created_files
    await agent._emit("message", f"[PO] Extracted {len(state.decomposed_files)} theorems to decomposed/")
    return Trans.EXTRACTED


# ─── Stage: child_pos ────────────────────────────────────────────────────────

async def _stage_child_pos(state: ProverState, agent) -> Trans:
    """Sequential child POs for decomposed files that have sorry."""
    cwd = _resolve(agent)
    import json as _json
    tools = get_lean_tools()

    # Only attempt child POs for files that actually have sorry
    remaining = [f for f in state.decomposed_files
                 if f not in state.proved_files and tools.has_sorry(f)]
    # Mark sorry-free files as already proved
    for f in state.decomposed_files:
        if f not in state.proved_files and not tools.has_sorry(f):
            state.proved_files.append(f)

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

    # ── Step 1: Rewrite parent Stub.lean imports to point to child's Stub ──
    # Change: import ...decomposed.lemma_helper_foo
    # To:     import ...decomposed.lemma_helper_foo.Stub
    # This way parent imports the child's PROVED Stub.lean directly (no copy needed)
    stub_path = cwd / stub_rel
    stub_content = stub_path.read_text()
    decomposed_module_prefix = f"{top_module}.decomposed."
    new_stub_lines = []
    for line in stub_content.splitlines():
        stripped = line.strip()
        if (stripped.startswith("import ") and
                decomposed_module_prefix in stripped and
                not stripped.endswith(".Stub")):
            # Append .Stub to import the child's proved file
            new_stub_lines.append(f"{stripped}.Stub")
        else:
            new_stub_lines.append(line)
    stub_path.write_text("\n".join(new_stub_lines) + "\n")

    # ── Step 2: Rewrite each child's Stub.Def import to point to parent's Def ──
    # Child imported its own copy: import ...decomposed.lemma_helper_foo.Stub.Def
    # Change to: import <parent>.Stub.Def
    decomposed_dir_path = cwd / state.workspace / "decomposed"
    if decomposed_dir_path.exists():
        for child_dir in decomposed_dir_path.iterdir():
            if not child_dir.is_dir():
                continue
            child_stub = child_dir / "Stub.lean"
            if not child_stub.exists():
                continue
            content = child_stub.read_text()
            rewritten = False
            new_lines = []
            for line in content.splitlines():
                stripped = line.strip()
                if stripped.startswith("import ") and "Stub.Def" in stripped and stripped != f"import {top_module}.Stub.Def":
                    new_lines.append(f"import {top_module}.Stub.Def")
                    rewritten = True
                else:
                    new_lines.append(line)
            if rewritten:
                child_stub.write_text("\n".join(new_lines) + "\n")
                await agent._emit("message", f"[PO] Rewrote Def import in {child_dir.name}/Stub.lean")

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
        ctx = swarm_agent(
            "proof_writer_v2", swarm=agent.swarm, cwd=agent._cwd,
            workspace=state.workspace,
            can_see=["SearchAgent"],
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
        cheat_rel = f"{state.workspace}/StrataProofCheatSheet.md"
        ctx = swarm_agent(
            "proof_guide", swarm=agent.swarm, cwd=agent._cwd,
            workspace=state.workspace,
            template_vars={"cheat_sheet_path": cheat_rel},
            can_see=["SearchAgent"],
        )
        internal = await ctx.__aenter__()
        setattr(agent, f"{attr}_ctx", ctx)
        setattr(agent, attr, internal)
        state.internal_agents["guide"] = internal.spec.name
    return getattr(agent, attr)



async def _repair_failed_extractions(agent, state, failed_dir: Path, tools) -> list[str]:
    """Try to fix extracted files that failed to compile using a stateless fixer agent."""
    cwd = _resolve(agent)
    repaired = []

    failed_files = list(failed_dir.glob("*.lean"))
    if not failed_files:
        return repaired

    await agent._emit("message", f"[PO] Attempting to repair {len(failed_files)} failed extractions...")

    for failed_file in failed_files:
        rel_path = str(failed_file.relative_to(cwd))
        content = failed_file.read_text()

        # Get the compile error
        cr = tools.check_compiles(rel_path)
        if cr.success:
            # Already compiles (maybe fixed by header changes) — move back
            dest = failed_dir.parent / failed_file.name
            shutil.move(str(failed_file), str(dest))
            repaired.append(str(dest.relative_to(cwd)))
            continue

        # Run a stateless fixer agent
        async with swarm_agent("proof_writer_v2", swarm=agent.swarm, cwd=agent._cwd,
                               workspace=state.workspace,
                               can_see=["SearchAgent"]) as fixer:
            fix_result = await fixer.run_ai(
                inp=(
                    f"This file has compilation errors. Fix them so it compiles (sorry is OK).\n"
                    f"File: {rel_path}\n"
                    f"The file should contain exactly ONE theorem with `sorry`.\n"
                    f"Do NOT change the theorem signature — only fix compilation errors "
                    f"(missing imports, wrong syntax, etc). Make it compile."
                ),
                max_turns=10,
            )

        # Check if it compiles now
        if tools.check_compiles(rel_path).success:
            dest = failed_dir.parent / failed_file.name
            shutil.move(str(failed_file), str(dest))
            repaired.append(str(dest.relative_to(cwd)))
            await agent._emit("message", f"[PO] Repaired: {failed_file.name}")
        else:
            await agent._emit("message", f"[PO] Could not repair: {failed_file.name}")

    return repaired


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


def _check_attempt_result(tools, stub_rel: str, cwd: Path, original_content: str) -> dict:
    """Check the state after a writer attempt. Returns a summary dict."""
    sorry_free = not tools.has_sorry(stub_rel)
    current_content = (cwd / stub_rel).read_text()
    unchanged = current_content.strip() == original_content.strip()
    cr = tools.check_compiles(stub_rel)
    sorry_count = tools.count_sorries(stub_rel).total if not sorry_free else 0
    return {
        "sorry_free": sorry_free,
        "unchanged": unchanged,
        "broken": not cr.success,
        "sorry_count": sorry_count,
    }


def _rewrite_stub_after_extraction(cwd: Path, stub_rel: str, extract_result, tools, state):
    """After extracting sorry helpers to decomposed/, rewrite Stub.lean:
    - Remove inline sorry theorem definitions (they now live in decomposed/)
    - Add imports to the decomposed files
    - The main theorem uses the helpers via imports instead of inline defs
    """
    stub_path = cwd / stub_rel
    content = stub_path.read_text()
    lines = content.splitlines()

    # Get block boundaries for the extracted theorems
    split = tools.split_theorems(stub_rel)
    if split.error:
        return

    extracted_set = set(extract_result.extracted_names)
    # Also remove unreachable dead helpers (sorry theorems not used by main theorem)
    reachable = tools.get_reachable_theorems(stub_rel, state.theorem_name)
    dead_helpers = set()
    for block in split.blocks:
        if block.has_sorry and block.name not in extracted_set and block.name != state.theorem_name:
            if block.name not in reachable:
                dead_helpers.add(block.name)

    # Find line ranges to remove (extracted + dead helper blocks)
    remove_set_names = extracted_set | dead_helpers
    remove_ranges = []
    for block in split.blocks:
        if block.name in remove_set_names:
            # Expand upward to include the preceding doc-comment for THIS theorem
            actual_start = block.start
            while actual_start > 0:
                prev = lines[actual_start - 1].strip()
                if prev == "" or prev.startswith("/--") or prev.startswith("--"):
                    actual_start -= 1
                else:
                    break
            # Trim end: don't include trailing doc-comments/section-markers (belong to next block)
            actual_end = block.end
            while actual_end >= actual_start:
                line = lines[actual_end].strip()
                if line == "" or line.startswith("/-") or line.startswith("--"):
                    actual_end -= 1
                else:
                    break
            remove_ranges.append((actual_start, actual_end))

    # Build import lines for decomposed files
    top_module = state.workspace.replace("/", ".")
    import_lines = []
    for f in extract_result.created_files:
        module = f.replace("/", ".").removesuffix(".lean")
        import_lines.append(f"import {module}")

    # Mark lines for removal (use a set to handle overlaps)
    remove_set = set()
    for start, end in remove_ranges:
        for i in range(start, end + 1):
            remove_set.add(i)

    # Build new content: keep non-removed lines
    new_lines = [line for i, line in enumerate(lines) if i not in remove_set]

    # Add imports after the existing import block
    insert_pos = 0
    for i, line in enumerate(new_lines):
        if line.strip().startswith("import "):
            insert_pos = i + 1
    for i, imp in enumerate(import_lines):
        new_lines.insert(insert_pos + i, imp)

    stub_path.write_text("\n".join(new_lines) + "\n")


def _build_initial_action(state: ProverState) -> str:
    """Build the first action message for proof_writer."""
    stub_rel = f"{state.workspace}/Stub.lean"
    msg = (
        f"Prove the theorem in {stub_rel}.\n"
        f"Theorem name: {state.theorem_name}\n\n"
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
