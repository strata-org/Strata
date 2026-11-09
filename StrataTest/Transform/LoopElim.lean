/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

import StrataDDM.Integration.Lean
meta import StrataDDM.Util.Format
meta import Strata.Languages.Core
meta import Strata.Languages.Core.DDMTransform.Translate
meta import Strata.Transform.CoreTransform
meta import Strata.Transform.LoopElim
meta import Strata.Languages.Core.Verifier

meta section

open Core
private abbrev testLoc : ExprSourceLoc := ExprSourceLoc.synthesized "test"
open Core.Transform
open Strata

/-! ## LoopElim examples

`LoopElim` performs only the structural conversion of a *bare* loop (guard +
body, with its invariants/measure already stripped by `InsertLoopInvariantAsserts`)
into an acyclic `if` with havocs and guard assumptions. If it is handed a loop
that still carries invariants or a measure, it fails fast rather than silently
dropping those verification conditions. -/
section LoopElimExamples

def translate (t : StrataDDM.SourcedProgram) : Core.Program :=
  (TransM.run Inhabited.default (translateProgram t)).fst

/-- Run `loopElim` with a fresh transform state, formatting the transformed
    program on success or the diagnostic on failure. -/
def runLoopElim (p : Core.Program) : String :=
  match run p loopElim with
  | .ok (_, res) => toString res.eraseTypes
  | .error e => s!"error: {e}"

/-- A bare loop (no invariant, no measure) is converted into its passive
    `if` encoding with two havocs and the guard assumptions. -/
def bareLoopPgm :=
#strata
program Core;
procedure bareLoop(n : int)
{
  var i : int;
  i := 0;
  while (int.lt(i, n))
  {
    i := int.add(i, 1);
  }
};
#end

/--
info: program Core;

procedure bareLoop (n : int)
{
  var i : int;
  i := 0;
  if (int.lt(i, n)) {
    $__loopElim_arbitrary_iter_facts_loop_0: {
      $__loopElim_havoc_loop_0: {
        havoc i;
      }
      assume [$__loopElimAssume_guard_loop_0]: int.lt(i, n);
      i := int.add(i, 1);
    }
    $__loopElim_havoc_loop_0: {
      havoc i;
    }
    assume [$__loopElimAssume_not_guard_loop_0]: !(int.lt(i, n));
  }
};
-/
#guard_msgs in
#eval IO.println (runLoopElim (translate bareLoopPgm))

/-- A bare *nondeterministic* loop (`while *`) is converted into an `if *`
    with two havocs and no guard assumptions (the `.nondet` branch of the guard
    handling emits neither a `guard` nor a `not_guard` assume). -/
def bareNondetLoopPgm :=
#strata
program Core;
procedure bareNondetLoop(n : int)
{
  var i : int;
  i := 0;
  while *
  {
    i := int.add(i, 1);
  }
};
#end

/--
info: program Core;

procedure bareNondetLoop (n : int)
{
  var i : int;
  i := 0;
  if * {
    $__loopElim_arbitrary_iter_facts_loop_0: {
      $__loopElim_havoc_loop_0: {
        havoc i;
      }
      i := int.add(i, 1);
    }
    $__loopElim_havoc_loop_0: {
      havoc i;
    }
  }
};
-/
#guard_msgs in
#eval IO.println (runLoopElim (translate bareNondetLoopPgm))

/-- A loop that still carries an `invariant` is rejected: its verification
    conditions must first be materialized by `InsertLoopInvariantAsserts`. -/
def invLoopPgm :=
#strata
program Core;
procedure invLoop(n : int)
{
  var i : int;
  i := 0;
  while (int.lt(i, n))
    invariant int.le(0, i)
  {
    i := int.add(i, 1);
  }
};
#end

/-- info: error: LoopElim invoked on a loop that still carries invariants/measure; run InsertLoopInvariantAsserts first (or use the built-in verify pipeline) -/
#guard_msgs in
#eval IO.println (runLoopElim (translate invLoopPgm))

/-- A loop that still carries a `decreases` measure is likewise rejected. -/
def measureLoopPgm :=
#strata
program Core;
procedure measureLoop(n : int)
{
  var i : int;
  i := 0;
  while (int.lt(i, n))
    decreases int.sub(n, i)
  {
    i := int.add(i, 1);
  }
};
#end

/-- info: error: LoopElim invoked on a loop that still carries invariants/measure; run InsertLoopInvariantAsserts first (or use the built-in verify pipeline) -/
#guard_msgs in
#eval IO.println (runLoopElim (translate measureLoopPgm))

/-- A loop body whose `exit` targets a label with the prefix reserved for the blocks LoopElim
    mints (`$__loopElim`) is rejected, since a generated block would otherwise capture that
    exit. -/
def labelConflictPgm :=
#strata
program Core;
procedure conflict(n : int)
{
  var i : int;
  i := 0;
  while (int.lt(i, n))
  {
    exit $__loopElim_havoc_loop_0;
  }
};
#end

/-- info: error: Exit target in loop body uses the reserved label prefix $__loopElim (loop loop_0) -/
#guard_msgs in
#eval IO.println (runLoopElim (translate labelConflictPgm))

/-- A program with a CFG procedure body and no loops is still rejected. -/
def cfgOnlyPgm : Core.Program :=
  { decls := [.proc
      { (default : Procedure) with
          header := { (default : Procedure.Header) with name := ⟨"cfgProc", ()⟩ }
          body := .cfg { entry := "entry", blocks := [] } }
      default] }

/-- info: error: runProgram: cannot apply statement-level transform to CFG body (procedure 'cfgProc') -/
#guard_msgs in
#eval IO.println (runLoopElim cfgOnlyPgm)

end LoopElimExamples

/-! ## Loop-elimination pipeline phase obligation tests -/
section LoopElimPhaseTests
open Strata.SMT
open Core.SMT (Result)

private def satResult : Result := .sat []
private def unknownResult : Result := .unknown (some [])

/-- Obligation with loop-elimination labels in path conditions. -/
private def loopElimObligation : Imperative.ProofObligation Core.Expression :=
  { label := "test_loopElim", property := .assert,
    assumptions := [[.assumption "$__loopElimAssume_invariant_loop_0_0" (.true testLoc), .assumption
        "$__loopElimAssume_guard_loop_0" (.true testLoc)]],
    obligation := .true testLoc, metadata := {} }

/-- Obligation with no abstraction labels — models are sound. -/
private def cleanObligation : Imperative.ProofObligation Core.Expression :=
  { label := "test_clean", property := .assert,
    assumptions := [[.assumption "precond_x_positive" (.true testLoc)]],
    obligation := .true testLoc, metadata := {} }

-- loopElimPipelinePhase: rejects sat when obligation has loop-elim labels
#guard (satResult.adjustForPhases [loopElimPipelinePhase.phase] loopElimObligation).1 == unknownResult

-- loopElimPipelinePhase: preserves sat when obligation has no loop-elim labels
#guard (satResult.adjustForPhases [loopElimPipelinePhase.phase] cleanObligation).1 == satResult

end LoopElimPhaseTests
end
