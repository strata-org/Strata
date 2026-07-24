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
meta import Strata.Transform.InsertLoopInvariantAsserts
meta import Strata.Languages.Core.Verifier

meta section

open Core
open Core.Transform
open Strata

/-! ## InsertLoopInvariantAsserts examples

`InsertLoopInvariantAsserts` materializes each loop's invariant and measure
verification conditions as explicit `assert`/`assume` statements, and strips the
loop's invariants/measure so the loop becomes "bare" (guard + decorated body
only). It does not convert the loop into an `if` — that is `LoopElim`'s job. -/
section InsertLoopInvariantAssertsExamples

def translate (t : StrataDDM.SourcedProgram) : Core.Program :=
  (TransM.run Inhabited.default (translateProgram t)).fst

/-- Run the pass with a fresh transform state, returning
    `(anyLoopDecorated, transformedProgram)`. -/
def runInsert (p : Core.Program) : Bool × Core.Program :=
  match (run p insertLoopInvariantAsserts) with
  | .ok (changed, res) => (changed, res)
  | .error e => panic! (toString e) -- nopanic:ok

/-- A loop with both an invariant and a `decreases` measure. -/
def invAndMeasurePgm :=
#strata
program Core;
procedure countUp(n : int)
{
  var i : int;
  i := 0;
  while (i < n)
    decreases n - i
    invariant 0 <= i
    invariant i <= n
  {
    i := (i + 1);
  }
};
#end

/--
info: program Core;

procedure countUp (n : int)
{
  var i : int;
  i := 0;
  assert [insertLoopInvAssert_entry_invariant_loop_0_0]: 0 <= i;
  assert [insertLoopInvAssert_entry_invariant_loop_0_1]: i <= n;
  assume [insertLoopInvAssume_entry_invariant_loop_0_0]: 0 <= i;
  assume [insertLoopInvAssume_entry_invariant_loop_0_1]: i <= n;
  while (i < n)
  {
    assume [insertLoopInvAssume_invariant_loop_0_0]: 0 <= i;
    assume [insertLoopInvAssume_invariant_loop_0_1]: i <= n;
    var $__loop_measure_loop_0 : int;
    assume [insertLoopInvAssume_measure_loop_0]: $__loop_measure_loop_0 == n - i;
    assert [insertLoopInvAssert_measure_lb_loop_0]: !($__loop_measure_loop_0 < 0);
    i := i + 1;
    assert [insertLoopInvAssert_arbitrary_iter_maintain_invariant_loop_0_0]: 0 <= i;
    assert [insertLoopInvAssert_arbitrary_iter_maintain_invariant_loop_0_1]: i <= n;
    assert [insertLoopInvAssert_measure_decrease_loop_0]: n - i < $__loop_measure_loop_0;
  }
  assume [insertLoopInvAssume_exit_invariant_loop_0_0]: 0 <= i;
  assume [insertLoopInvAssume_exit_invariant_loop_0_1]: i <= n;
  assume [insertLoopInvAssume_exit_not_guard_loop_0]: !(i < n);
};
-/
#guard_msgs in
#eval IO.println (toString (runInsert (translate invAndMeasurePgm)).2.eraseTypes)

/-- Nested loops, each with an invariant: the pass decorates both, at a fixed
    point, giving them distinct loop numbers. -/
def nestedPgm :=
#strata
program Core;
procedure nested(n : int, m : int)
{
  var i : int;
  var j : int;
  i := 0;
  while (i < n)
    invariant 0 <= i
  {
    j := 0;
    while (j < m)
      invariant 0 <= j
    {
      j := (j + 1);
    }
    i := (i + 1);
  }
};
#end

/--
info: program Core;

procedure nested (n : int, m : int)
{
  var i : int;
  var j : int;
  i := 0;
  assert [insertLoopInvAssert_entry_invariant_loop_0_0]: 0 <= i;
  assume [insertLoopInvAssume_entry_invariant_loop_0_0]: 0 <= i;
  while (i < n)
  {
    assume [insertLoopInvAssume_invariant_loop_0_0]: 0 <= i;
    j := 0;
    assert [insertLoopInvAssert_entry_invariant_loop_1_0]: 0 <= j;
    assume [insertLoopInvAssume_entry_invariant_loop_1_0]: 0 <= j;
    while (j < m)
    {
      assume [insertLoopInvAssume_invariant_loop_1_0]: 0 <= j;
      j := j + 1;
      assert [insertLoopInvAssert_arbitrary_iter_maintain_invariant_loop_1_0]: 0 <= j;
    }
    assume [insertLoopInvAssume_exit_invariant_loop_1_0]: 0 <= j;
    assume [insertLoopInvAssume_exit_not_guard_loop_1]: !(j < m);
    i := i + 1;
    assert [insertLoopInvAssert_arbitrary_iter_maintain_invariant_loop_0_0]: 0 <= i;
  }
  assume [insertLoopInvAssume_exit_invariant_loop_0_0]: 0 <= i;
  assume [insertLoopInvAssume_exit_not_guard_loop_0]: !(i < n);
};
-/
#guard_msgs in
#eval IO.println (toString (runInsert (translate nestedPgm)).2.eraseTypes)

/-- A loop with neither invariant nor measure is left untouched: the pass
    reports no change. -/
def noInvPgm :=
#strata
program Core;
procedure bare()
{
  var i : int;
  i := 0;
  while (i < 10)
  {
    i := (i + 1);
  }
};
#end

/-- info: false -/
#guard_msgs in
#eval (runInsert (translate noInvPgm)).1

-- And the program is left unchanged: the (bare) loop is preserved intact rather
-- than being rewritten, so pinning `false` above is not masking a silent edit.
/-- info: true -/
#guard_msgs in
#eval toString (runInsert (translate noInvPgm)).2 ==
      toString (translate noInvPgm)

/-- A nondeterministic loop (`while *`) that carries a `decreases` measure is
    ill-formed — it iterates an arbitrary number of times and so cannot be shown
    to terminate by a measure — so the pass rejects it with a diagnostic. -/
def nondetWithMeasurePgm :=
#strata
program Core;
procedure nondetMeasure(n : int)
{
  var i : int;
  i := 0;
  while *
    decreases n - i
    invariant 0 <= i
  {
    i := (i + 1);
  }
};
#end

/-- info: rejected: nondeterministic loop (`while *`) cannot carry a `decreases` measure: it iterates an arbitrary number of times and so cannot be shown to terminate -/
#guard_msgs in
#eval match run (translate nondetWithMeasurePgm) insertLoopInvariantAsserts with
  | .ok _ => IO.println "unexpected: the transform did not reject the loop"
  | .error e => IO.println s!"rejected: {e}"

/-- A nondeterministic loop with an invariant but no measure is decorated
    normally. Because there is no guard, the exit assumption is just the
    invariant (no negated guard is added). -/
def nondetInvOnlyPgm :=
#strata
program Core;
procedure nondetInv()
{
  var i : int;
  i := 0;
  while *
    invariant 0 <= i
  {
    i := (i + 1);
  }
};
#end

/--
info: program Core;

procedure nondetInv ()
{
  var i : int;
  i := 0;
  assert [insertLoopInvAssert_entry_invariant_loop_0_0]: 0 <= i;
  assume [insertLoopInvAssume_entry_invariant_loop_0_0]: 0 <= i;
  while *
  {
    assume [insertLoopInvAssume_invariant_loop_0_0]: 0 <= i;
    i := i + 1;
    assert [insertLoopInvAssert_arbitrary_iter_maintain_invariant_loop_0_0]: 0 <= i;
  }
  assume [insertLoopInvAssume_exit_invariant_loop_0_0]: 0 <= i;
};
-/
#guard_msgs in
#eval IO.println (toString (runInsert (translate nondetInvOnlyPgm)).2.eraseTypes)

/-- A deterministic loop with only a `decreases` measure and no invariant.
    This exercises the measure-only path: because the invariant list is empty,
    the entry asserts/assumes, the mid-loop invariant assume, and the maintain
    asserts are all absent, while the measure setup (`init`/`assume`/`measure_lb`)
    and the strict-decrease assert are still emitted inside the body. The only
    statement left after the loop is the negated guard assume (there is no exit
    invariant assume, since there is no invariant). -/
def measureOnlyPgm :=
#strata
program Core;
procedure measureOnly(n : int)
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

/--
info: program Core;

procedure measureOnly (n : int)
{
  var i : int;
  i := 0;
  while (i < n)
  {
    var $__loop_measure_loop_0 : int;
    assume [insertLoopInvAssume_measure_loop_0]: $__loop_measure_loop_0 == n - i;
    assert [insertLoopInvAssert_measure_lb_loop_0]: !($__loop_measure_loop_0 < 0);
    i := i + 1;
    assert [insertLoopInvAssert_measure_decrease_loop_0]: n - i < $__loop_measure_loop_0;
  }
  assume [insertLoopInvAssume_exit_not_guard_loop_0]: !(i < n);
};
-/
#guard_msgs in
#eval IO.println (toString (runInsert (translate measureOnlyPgm)).2.eraseTypes)

end InsertLoopInvariantAssertsExamples

/-! ## InsertLoopInvariantAsserts pipeline phase obligation tests -/
section InsertLoopInvariantAssertsPhaseTests
open Strata.SMT
open Core.SMT (Result)

private def satResult : Result := .sat []
private def unknownResult : Result := .unknown (some [])

/-- Obligation whose path includes an inserted invariant assumption: the loop
    was over-approximated, so a sat model must be demoted to unknown. -/
private def insertObligation : Imperative.ProofObligation Core.Expression :=
  { label := "test_insert", property := .assert,
    assumptions := [[.assumption "insertLoopInvAssume_invariant_loop_0_0" (.true ())]],
    obligation := .true (), metadata := {} }

/-- Obligation with no abstraction labels — models are sound. -/
private def cleanObligation : Imperative.ProofObligation Core.Expression :=
  { label := "test_clean", property := .assert,
    assumptions := [[.assumption "precond_x_positive" (.true ())]],
    obligation := .true (), metadata := {} }

-- rejects sat when obligation has an inserted invariant assumption
#guard (satResult.adjustForPhases [insertLoopInvariantAssertsPipelinePhase.phase] insertObligation).1 == unknownResult

-- preserves sat when obligation has no such labels
#guard (satResult.adjustForPhases [insertLoopInvariantAssertsPipelinePhase.phase] cleanObligation).1 == satResult

end InsertLoopInvariantAssertsPhaseTests
