/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Core.Verifier

---------------------------------------------------------------------
namespace Strata

-- `second`'s obligation is checked once. `first`'s `post` is checked on two
-- paths but mergeByAssertion deduplicates the results.
def issue419TestPgm :=
#strata
program Core;
procedure first(x : int) returns (r : int)
spec { ensures [post]: (r >= 0); }
{
  body: {
    if (x < 0) { r := 0 - x; exit body; }
    r := x;
    exit body;
  }
};

procedure second() returns () { assert [a]: true; };
#end


/--
info:
Obligation: post
Property: assert
Result: ✅ pass

Obligation: a
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval verify issue419TestPgm (options := .quiet)

def sequentialExitPgm :=
#strata
program Core;


procedure wrong(c1 : bool, c2 : bool) returns (r : int)
spec { ensures r > 0; }
{
  done: {
    if (c1) { r := -1; exit done; }
    if (c2) { r := 2; exit done; }
    r := 3;
  }
};
#end


/--
info:
Obligation: wrong_ensures_0
Property: assert
Result: ❌ fail
-/
#guard_msgs in
#eval verify sequentialExitPgm (options := .quiet)

---------------------------------------------------------------------
-- Dead-branch obligation tests
--
-- When an ITE condition is a concrete `true` or `false`, one branch is
-- unreachable. The evaluator must still generate obligations for any
-- `assert` or `cover` commands in the dead branch. Dead-branch
-- obligations come before any live-branch obligations.
---------------------------------------------------------------------

def concreteTrueDeadElse :=
#strata
program Core;
procedure p() returns () {
  if (true) {
    assert [live_then]: true;
  } else {
    assert [dead_else]: true;
  }
};
#end

/--
info:
Obligation: dead_else
Property: assert
Result: ✅ pass

Obligation: live_then
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval verify concreteTrueDeadElse (options := .quiet)

def concreteFalseDeadThen :=
#strata
program Core;
procedure p() returns () {
  if (false) {
    assert [dead_then]: true;
  } else {
    assert [live_else]: true;
  }
};
#end

/--
info:
Obligation: dead_then
Property: assert
Result: ✅ pass

Obligation: live_else
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval verify concreteFalseDeadThen (options := .quiet)

def concreteFalseDeadThenCover :=
#strata
program Core;
procedure p() returns () {
  if (false) {
    cover [dead_cover]: true;
  } else {
    assert [live_else]: true;
  }
};
#end

/--
info:
Obligation: dead_cover
Property: cover
Result: ❌ fail

Obligation: live_else
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval verify concreteFalseDeadThenCover (options := .quiet)

def programOrderConcreteFalse :=
#strata
program Core;
procedure p() returns () {
  assert [pre]: true;
  if (false) {
    assert [dead_then]: true;
  } else {
    assert [live_else]: true;
  }
  assert [post]: true;
};
#end

/--
info:
Obligation: dead_then
Property: assert
Result: ✅ pass

Obligation: pre
Property: assert
Result: ✅ pass

Obligation: live_else
Property: assert
Result: ✅ pass

Obligation: post
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval verify programOrderConcreteFalse (options := .quiet)

-- Unreachable annotation test: with full check level, dead-branch asserts carry
-- `(❗path unreachable)` and dead-branch covers fail with the same annotation.
-- Within a dead branch, covers are emitted before asserts (collectDeadBranchDeferred
-- calls createUnreachableCoverObligations ++ createUnreachableAssertObligations).
def deadBranchAnnotations :=
#strata
program Core;
procedure p() returns () {
  if (true) {
  } else {
    assert [dead_assert]: true;
    cover  [dead_cover]:  true;
  }
};
#end

/--
info:
Obligation: dead_cover
Property: cover
Result: ❌ fail (❗path unreachable)

Obligation: dead_assert
Property: assert
Result: ✅ pass (❗path unreachable)
-/
#guard_msgs in
#eval verify deadBranchAnnotations
        (options := { Core.VerifyOptions.default with verbose := .quiet, checkLevel := .full })

---------------------------------------------------------------------
-- No-duplication tests
--
-- When a concrete ITE's live branch contains a symbolic ITE with an exit
-- (producing multiple paths via processIteBranches), mergeResults unions
-- all paths' deferred obligations. Pre-ITE and dead-branch obligations
-- must appear exactly once — they are attached only to the first result.
---------------------------------------------------------------------

def noDupConcreteTrue :=
#strata
program Core;
procedure p(x : bool) returns () {
  assert [pre]: true;
  if (true) {
    done: {
      if (x) {
        assert [then_path]: true;
        exit done;
      } else {
        assert [else_path]: true;
      }
    }
  } else {
    assert [dead_else]: true;
  }
  assert [post]: true;
};
#end

/--
info:
Obligation: dead_else
Property: assert
Result: ✅ pass

Obligation: pre
Property: assert
Result: ✅ pass

Obligation: then_path
Property: assert
Result: ✅ pass

Obligation: post
Property: assert
Result: ✅ pass

Obligation: else_path
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval verify noDupConcreteTrue (options := .quiet)

def noDupConcreteFalse :=
#strata
program Core;
procedure q(x : bool) returns () {
  assert [pre]: true;
  if (false) {
    assert [dead_then]: true;
  } else {
    done: {
      if (x) {
        assert [then_path]: true;
        exit done;
      } else {
        assert [else_path]: true;
      }
    }
  }
  assert [post]: true;
};
#end

/--
info:
Obligation: dead_then
Property: assert
Result: ✅ pass

Obligation: pre
Property: assert
Result: ✅ pass

Obligation: then_path
Property: assert
Result: ✅ pass

Obligation: post
Property: assert
Result: ✅ pass

Obligation: else_path
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval verify noDupConcreteFalse (options := .quiet)

---------------------------------------------------------------------
-- Evaluator statistics tests
--
-- These verify that path splitting is observable in the evaluator stats
-- (diverged count, obligation count) independently of mergeByAssertion
-- which only deduplicates at the outcome/display level.
---------------------------------------------------------------------

/-- Extract evaluator statistics from a program without running the solver. -/
private def getEvalStats (program : Strata.Program) : IO (Statistics × Nat) := do
  let (coreProgram, _) := Core.getProgram program
  match Core.typeCheckAndEval .quiet coreProgram with
  | .error _ => return ({}, 0)
  | .ok (envs, stats) =>
    let numObligations := envs.foldl (fun acc e => acc + e.deferred.size) 0
    return (stats, numObligations)

-- issue419TestPgm: the evaluator produces 2 paths (1 diverged ITE) and
-- 3 obligations (2 for `post`, 1 for `a`). mergeByAssertion collapses
-- the 2 `post` results into 1 displayed result, but the evaluator still
-- explored both paths.
/--
info: diverged=1 obligations=3
-/
#guard_msgs in
#eval do
  let (stats, numObs) ← getEvalStats issue419TestPgm
  let key := s!"{Core.Evaluator.Stats.processIteBranches_diverged}"
  IO.println s!"diverged={stats.get key} obligations={numObs}"

-- sequentialExitPgm: 2 diverged ITEs, 3 paths, 3 obligations for
-- `wrong_ensures_0`. mergeByAssertion collapses to 1 displayed result.
/--
info: diverged=2 obligations=3
-/
#guard_msgs in
#eval do
  let (stats, numObs) ← getEvalStats sequentialExitPgm
  let key := s!"{Core.Evaluator.Stats.processIteBranches_diverged}"
  IO.println s!"diverged={stats.get key} obligations={numObs}"
