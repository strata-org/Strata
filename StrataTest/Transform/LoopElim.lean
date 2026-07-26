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
  while (i < n)
  {
    i := (i + 1);
  }
};
#end

/--
info: program Core;

procedure bareLoop (n : int)
{
  var i : int;
  i := 0;
  if (i < n) {
    loopElim_arbitrary_iter_facts_loop_0: {
      loopElim_havoc_loop_0: {
        havoc i;
      }
      assume [loopElimAssume_guard_loop_0]: i < n;
      i := i + 1;
    }
    loopElim_havoc_loop_0: {
      havoc i;
    }
    assume [loopElimAssume_not_guard_loop_0]: !(i < n);
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
    i := (i + 1);
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
    loopElim_arbitrary_iter_facts_loop_0: {
      loopElim_havoc_loop_0: {
        havoc i;
      }
      i := i + 1;
    }
    loopElim_havoc_loop_0: {
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
  while (i < n)
    invariant 0 <= i
  {
    i := (i + 1);
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
  while (i < n)
    decreases n - i
  {
    i := (i + 1);
  }
};
#end

/-- info: error: LoopElim invoked on a loop that still carries invariants/measure; run InsertLoopInvariantAsserts first (or use the built-in verify pipeline) -/
#guard_msgs in
#eval IO.println (runLoopElim (translate measureLoopPgm))

/-- A loop body whose `exit` target collides with a block label that LoopElim
    would mint (`loopElim_havoc_loop_0`) is rejected, since the generated block
    would otherwise silently capture that exit. -/
def labelConflictPgm :=
#strata
program Core;
procedure conflict(n : int)
{
  var i : int;
  i := 0;
  while (i < n)
  {
    exit loopElim_havoc_loop_0;
  }
};
#end

/-- info: error: Generated loop block label conflicts with exit target in loop body (loop loop_0) -/
#guard_msgs in
#eval IO.println (runLoopElim (translate labelConflictPgm))

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
    assumptions := [[.assumption "loopElimAssume_invariant_loop_0_0" (.true ()), .assumption "loopElimAssume_guard_loop_0" (.true ())]],
    obligation := .true (), metadata := {} }

/-- Obligation with no abstraction labels — models are sound. -/
private def cleanObligation : Imperative.ProofObligation Core.Expression :=
  { label := "test_clean", property := .assert,
    assumptions := [[.assumption "precond_x_positive" (.true ())]],
    obligation := .true (), metadata := {} }

-- loopElimPipelinePhase: rejects sat when obligation has loop-elim labels
#guard (satResult.adjustForPhases [loopElimPipelinePhase.phase] loopElimObligation).1 == unknownResult

-- loopElimPipelinePhase: preserves sat when obligation has no loop-elim labels
#guard (satResult.adjustForPhases [loopElimPipelinePhase.phase] cleanObligation).1 == satResult

end LoopElimPhaseTests
end
