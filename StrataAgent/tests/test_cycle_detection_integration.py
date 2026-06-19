"""Integration test for cycle detection — spawns a real proof_writer agent.

Tests that verify_ancestor_match correctly:
1. Creates a temp file with ancestor (sorry) + variant statement
2. Spawns proof_writer_v2 with 5 turns to prove variant from ancestor
3. Checks if Lean accepts the proof

Run with: .venv/bin/python tests/test_cycle_detection_integration.py

Requires: Claude API credentials, Lean toolchain, itp_interface
"""

import asyncio
import os
import shutil
import sys
from pathlib import Path

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

from strataswarm import (
    AgentEvent, AgentSpec, AgentStatus,
    CancellationToken, ChannelBus, ClaudeBackend,
    PauseToken, Swarm, SwarmAgent, ToolSet,
)
from strataswarm._helpers import swarm_agent
from strataswarm.modules.lemma_ledger import LemmaLedger, LemmaStatus
from strataswarm.modules.cycle_detection import verify_ancestor_match, _run_short_writer
from strataswarm.modules.po_lean import get_lean_tools, SwarmLeanTools


PROJECT_ROOT = Path(__file__).resolve().parent.parent.parent  # Strata/
WORK_DIR = PROJECT_ROOT / "StrataAgent" / "tests" / "Lean" / "cycle_integration_test"
LOG_DIR = PROJECT_ROOT / "StrataAgent" / "tests" / "Lean"

log_lines = []
def log(msg):
    print(msg)
    log_lines.append(msg)


async def test_verify_ancestor_match_with_writer():
    """Full integration: spawn proof_writer to prove variant from ancestor."""

    log("=" * 70)
    log("INTEGRATION TEST: verify_ancestor_match with real proof_writer")
    log("=" * 70)
    log("")

    # Setup workspace
    if WORK_DIR.exists():
        shutil.rmtree(WORK_DIR)
    WORK_DIR.mkdir(parents=True, exist_ok=True)

    tools = get_lean_tools()

    # The ancestor statement (with sorry — acts as given)
    ancestor_statement = """\
theorem sim_terminal_stmt
    (extendEval : ExtendEval P)
    (s : Stmt P (Cmd P)) (s' : KleeneStmt P (Cmd P))
    (hT : StmtToKleeneStmt s = some s')
    (ρ₀ ρ₁ : Env P)
    (hWF : WellFormedSemanticEvalBool ρ₀.eval ∧
           WellFormedSemanticEvalVal ρ₀.eval ∧
           WellFormedSemanticEvalVar ρ₀.eval)
    (hNotFail : ρ₀.hasFailure = false)
    (hStar : StepStmtStar P (EvalCmd P) extendEval (.stmt s ρ₀) (.terminal ρ₁))
    (hNotFail₁ : ρ₁.hasFailure = false) :
    StepKleeneStar P (EvalCmd P) (.stmt s' ρ₀) (.terminal ρ₁) := by
  sorry"""

    # The variant (same semantics, different variable names)
    variant_statement = """\
theorem helper_sim_terminal_stmt_renamed
    (extendEval : ExtendEval P)
    (stmt : Stmt P (Cmd P)) (kstmt : KleeneStmt P (Cmd P))
    (hConvert : StmtToKleeneStmt stmt = some kstmt)
    (env_init env_final : Env P)
    (hWF : WellFormedSemanticEvalBool env_init.eval ∧
           WellFormedSemanticEvalVal env_init.eval ∧
           WellFormedSemanticEvalVar env_init.eval)
    (hNotFail : env_init.hasFailure = false)
    (hStar : StepStmtStar P (EvalCmd P) extendEval (.stmt stmt env_init) (.terminal env_final))
    (hNotFail₁ : env_final.hasFailure = false) :
    StepKleeneStar P (EvalCmd P) (.stmt kstmt env_init) (.terminal env_final) := by
  sorry"""

    # Create the "our file" (variant) that the writer will modify
    imports = """\
import Strata.Transform.DetToKleene
import Strata.DL.Imperative.Stmt
import Strata.DL.Imperative.StmtSemantics
import Strata.DL.Imperative.CmdSemantics
import Strata.DL.Imperative.KleeneStmt
import Strata.DL.Imperative.KleeneStmtSemantics
import Strata.DL.Imperative.KleeneSemanticsProps

open Imperative

variable {P : PureExpr} [HasFvar P] [HasBool P] [HasNot P] [HasIntOrder P] [HasVal P] [HasBoolVal P]
"""

    our_file_content = imports + "\n" + variant_statement + "\n"
    our_file_path = WORK_DIR / "variant.lean"
    our_file_path.write_text(our_file_content)

    # Also write the ancestor file (for _merge_imports reference)
    ancestor_file_content = imports + "\n" + ancestor_statement + "\n"
    ancestor_file_path = WORK_DIR / "ancestor.lean"
    ancestor_file_path.write_text(ancestor_file_content)

    our_rel = str(our_file_path.relative_to(PROJECT_ROOT))
    ancestor_rel = str(ancestor_file_path.relative_to(PROJECT_ROOT))

    log(f"Workspace: {WORK_DIR}")
    log(f"Our file (variant): {our_rel}")
    log(f"Ancestor file: {ancestor_rel}")
    log("")

    # Create a minimal swarm context for sub-agent spawning
    swarm = Swarm(
        backend_factory=ClaudeBackend,
        name="cycle_test",
        cwd=str(PROJECT_ROOT),
    )

    # Create a dummy parent agent that the cycle detection uses to spawn writers
    parent_spec = AgentSpec(
        name="test_parent",
        prompt="You are a test harness.",
        tools=ToolSet(),
        max_turns=1,
    )
    parent_agent = SwarmAgent(
        spec=parent_spec,
        backend=ClaudeBackend(),
        channel_bus=swarm._channel_bus,
        cancellation=CancellationToken(),
        pause=PauseToken(),
    )
    parent_agent.swarm = swarm
    parent_agent._cwd = str(PROJECT_ROOT)

    log("--- Spawning proof_writer_v2 (5 turns) ---")
    log(f"Instruction: Prove variant from ancestor using exact/apply/rw")
    log("")

    # Instead of calling verify_ancestor_match directly (which cleans up the temp file),
    # we manually build the temp file and call _run_short_writer so we can inspect results.
    from strataswarm.modules.cycle_detection import _merge_imports

    merged_imports = _merge_imports(our_rel, ancestor_rel)
    temp_content = "\n".join(f"import {imp}" for imp in merged_imports) + "\n\n"
    temp_content += "open Imperative\n\n"
    temp_content += "variable {P : PureExpr} [HasFvar P] [HasBool P] [HasNot P] [HasIntOrder P] [HasVal P] [HasBoolVal P]\n\n"
    temp_content += "-- Ancestor (given, has sorry)\n"
    temp_content += ancestor_statement + "\n\n"
    temp_content += "-- Variant: prove from ancestor\n"
    temp_content += variant_statement + "\n"

    temp_path = WORK_DIR / "_cycle_check_temp.lean"
    temp_path.write_text(temp_content)
    temp_rel = str(temp_path.relative_to(PROJECT_ROOT))

    log(f"Temp file created: {temp_rel}")
    log(f"Contents before writer:")
    log(temp_content)
    log("")

    # Verify it compiles (with sorry)
    cr = tools.check_compiles(temp_rel)
    log(f"Pre-check: compiles={cr.success}, has_sorry={cr.has_sorry}")
    log("")

    # Run the writer
    success = await _run_short_writer(
        parent_agent, temp_rel,
        f"This file has two theorems. The first (`sim_terminal_stmt`) has sorry. "
        f"Prove the SECOND theorem (`helper_sim_terminal_stmt_renamed`) using the first. "
        f"Try: exact sim_terminal_stmt extendEval stmt kstmt hConvert env_init env_final hWF hNotFail hStar hNotFail₁ "
        f"or similar. You have 5 turns. Just close the second sorry."
    )

    log(f"--- Result ---")
    log(f"_run_short_writer returned: {success}")
    log("")

    # Check what's in the file now
    if temp_path.exists():
        final_content = temp_path.read_text()
        log(f"Temp file after writer:")
        log(final_content)
        log("")
        cr2 = tools.check_compiles(temp_rel)
        # Only check sorry in the VARIANT theorem (ancestor keeps sorry — it's the "given")
        sorry_by_thm = tools.get_sorries_by_theorem(temp_rel)
        variant_has_sorry = "helper_sim_terminal_stmt_renamed" in sorry_by_thm
        log(f"Post-check: compiles={cr2.success}")
        log(f"  sorry_by_theorem: {sorry_by_thm}")
        log(f"  variant still has sorry: {variant_has_sorry}")
        if cr2.success and not variant_has_sorry:
            log("")
            log("✅ PASSED: proof_writer successfully proved variant from ancestor!")
            log("   Cycle CONFIRMED by real agent.")
            success = True
        else:
            log("")
            log("❌ FAILED: proof_writer could NOT close the variant's sorry in 5 turns.")
            success = False
    else:
        log("Temp file was deleted (writer restored original on failure).")
        log("❌ FAILED")
        success = False

    log("")


    # Preserve files for inspection
    log("=" * 70)
    log(f"Files preserved in: {WORK_DIR}")
    log(f"  ancestor.lean    — original theorem (sorry)")
    log(f"  variant.lean     — renamed variant (sorry)")
    if (WORK_DIR / "_cycle_check_temp.lean").exists():
        log(f"  _cycle_check_temp.lean — equivalence proof file")
    log("=" * 70)

    # Write log
    LOG_DIR.mkdir(parents=True, exist_ok=True)
    (LOG_DIR / "cycle_integration_test_log.txt").write_text("\n".join(log_lines))

    return success


if __name__ == "__main__":
    result = asyncio.run(test_verify_ancestor_match_with_writer())
    sys.exit(0 if result else 1)
