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
-- Path cap tests
--
-- When `pathCap` is set, the evaluator merges paths to stay under the
-- cap. Merging happens at two sites:
-- 1. processIteBranches: same-exit-label groups merged via Env.merge
-- 2. Block boundary: condition-equality matching pairs paths from
--    different exits that reconverge after exit-label consumption
---------------------------------------------------------------------

-- Cap 1 on issue419TestPgm: merges the two `post` paths at the block
-- boundary (different exit labels during ITE, same after block consumes).
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
#eval verify issue419TestPgm
  (options := { Core.VerifyOptions.quiet with pathCap := some 1 })

-- Cap 1 on sequentialExitPgm: 3 paths collapse to 1 via nested
-- condition-equality matching at the block boundary.
/--
info:
Obligation: wrong_ensures_0
Property: assert
Result: ❌ fail
-/
#guard_msgs in
#eval verify sequentialExitPgm
  (options := { Core.VerifyOptions.quiet with pathCap := some 1 })

-- Same exit label in both branches: merged directly in processIteBranches.
def sameExitCapPgm :=
#strata
program Core;
procedure p(c1 : bool) returns (r : int)
spec { ensures [post]: (r >= 0); }
{
  done: {
    if (c1) { r := 1; exit done; } else { r := 2; exit done; }
  }
};
#end

/--
info:
Obligation: post
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval verify sameExitCapPgm (options := .quiet)

/--
info:
Obligation: post
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval verify sameExitCapPgm
  (options := { Core.VerifyOptions.quiet with pathCap := some 1 })

-- Cap 4 on a 2-ITE program: under cap, paths diverge but
-- mergeByAssertion deduplicates the displayed results.
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
#eval verify issue419TestPgm
  (options := { Core.VerifyOptions.quiet with pathCap := some 4 })

---------------------------------------------------------------------
-- Evaluator statistics tests
--
-- These verify that path splitting is observable in the evaluator stats
-- (diverged count, obligation count) independently of mergeByAssertion
-- which only deduplicates at the outcome/display level.
---------------------------------------------------------------------

/-- Extract evaluator statistics from a program without running the solver. -/
private def getEvalStats (program : Strata.Program)
    (options : Core.VerifyOptions := .quiet) : IO (Statistics × Nat) := do
  let (coreProgram, _) := Core.getProgram program
  match Core.typeCheckAndEval options coreProgram with
  | .error _ => return ({}, 0)
  | .ok (envs, stats) =>
    let numObligations := envs.foldl (fun acc e => acc + e.deferred.size) 0
    return (stats, numObligations)

private def statsLine (stats : Statistics) (numObs : Nat) : String :=
  let merged := stats.get s!"{Core.Evaluator.Stats.processIteBranches_merged}"
  let diverged := stats.get s!"{Core.Evaluator.Stats.processIteBranches_diverged}"
  let stmtMerged := stats.get s!"{Core.Evaluator.Stats.betweenStmt_capMerged}"
  s!"merged={merged} diverged={diverged} stmtMerged={stmtMerged} obligations={numObs}"

-- issue419TestPgm without cap: 1 diverged ITE, 3 obligations.
/--
info: merged=0 diverged=1 stmtMerged=0 obligations=3
-/
#guard_msgs in
#eval do
  let (stats, numObs) ← getEvalStats issue419TestPgm
  IO.println (statsLine stats numObs)

-- issue419TestPgm with cap 1: ITE diverges, between-statement merge
-- collapses the 2 continuing paths before the next statement.
/--
info: merged=0 diverged=1 stmtMerged=1 obligations=2
-/
#guard_msgs in
#eval do
  let (stats, numObs) ← getEvalStats issue419TestPgm
    (options := { Core.VerifyOptions.quiet with pathCap := some 1 })
  IO.println (statsLine stats numObs)

-- sequentialExitPgm without cap: 2 diverged ITEs, 3 obligations.
/--
info: merged=0 diverged=2 stmtMerged=0 obligations=3
-/
#guard_msgs in
#eval do
  let (stats, numObs) ← getEvalStats sequentialExitPgm
  IO.println (statsLine stats numObs)

-- sequentialExitPgm with cap 1: ITEs diverge, between-statement merge
-- keeps the fallthrough path to 1, exiting paths accumulate linearly.
/--
info: merged=0 diverged=2 stmtMerged=1 obligations=1
-/
#guard_msgs in
#eval do
  let (stats, numObs) ← getEvalStats sequentialExitPgm
    (options := { Core.VerifyOptions.quiet with pathCap := some 1 })
  IO.println (statsLine stats numObs)

-- sameExitCapPgm without cap: 1 diverged, 2 obligations.
/--
info: merged=0 diverged=1 stmtMerged=0 obligations=2
-/
#guard_msgs in
#eval do
  let (stats, numObs) ← getEvalStats sameExitCapPgm
  IO.println (statsLine stats numObs)

-- sameExitCapPgm with cap 1: ITE diverges, between-statement merge
-- collapses the 2 paths (both have .none exit after block consumes).
/--
info: merged=0 diverged=1 stmtMerged=1 obligations=1
-/
#guard_msgs in
#eval do
  let (stats, numObs) ← getEvalStats sameExitCapPgm
    (options := { Core.VerifyOptions.quiet with pathCap := some 1 })
  IO.println (statsLine stats numObs)

---------------------------------------------------------------------
-- Sequential ITE path explosion tests
--
-- These test between-statement merging: after each ITE produces
-- multiple paths, the cap is enforced before the next statement.
---------------------------------------------------------------------

-- Sequential ITEs where one branch exits: each ITE splits the
-- fallthrough into (exit, continue). Between-statement merge keeps
-- the continuing paths to 1.
def sequentialExitItePgm :=
#strata
program Core;
procedure p(c1 : bool, c2 : bool, c3 : bool, c4 : bool) returns (r : int)
spec { ensures [post]: (r >= 0); }
{
  done: {
    if (c1) { r := 1; exit done; }
    if (c2) { r := 2; exit done; }
    if (c3) { r := 3; exit done; }
    if (c4) { r := 4; exit done; }
    r := 5;
  }
};
#end

-- Without cap: 4 diverged ITEs, 5 paths (linear — each ITE only
-- splits the single fallthrough path).
/--
info: merged=0 diverged=4 stmtMerged=0 obligations=5
-/
#guard_msgs in
#eval do
  let (stats, numObs) ← getEvalStats sequentialExitItePgm
  IO.println (statsLine stats numObs)

-- With cap 1: between-statement merge keeps fallthrough to 1 path.
-- Exiting paths accumulate linearly (4 exits + 1 fallthrough → merged
-- by procedure-level mergeResults).
/--
info: merged=0 diverged=4 stmtMerged=1 obligations=1
-/
#guard_msgs in
#eval do
  let (stats, numObs) ← getEvalStats sequentialExitItePgm
    (options := { Core.VerifyOptions.quiet with pathCap := some 1 })
  IO.println (statsLine stats numObs)

-- Exponential path explosion: sequential ITEs where both branches
-- modify state and continue. Each ITE has a block+exit so the
-- special-case merge doesn't fire. 4 ITEs → 2^4 = 16 paths without
-- cap. With cap 1, between-statement merge collapses paths after
-- each ITE.
def exponentialItePgm :=
#strata
program Core;
procedure p(c1 : bool, c2 : bool, c3 : bool, c4 : bool) returns (r : int)
spec { ensures [post]: (r >= 0); }
{
  b1: { if (c1) { r := 1; exit b1; } r := 2; }
  b2: { if (c2) { r := r + 10; exit b2; } r := r + 20; }
  b3: { if (c3) { r := r + 100; exit b3; } r := r + 200; }
  b4: { if (c4) { r := r + 1000; exit b4; } r := r + 2000; }
};
#end

-- Without cap: 15 diverged ITEs (exponential), 16 obligations.
/--
info: merged=0 diverged=15 stmtMerged=0 obligations=16
-/
#guard_msgs in
#eval do
  let (stats, numObs) ← getEvalStats exponentialItePgm
  IO.println (statsLine stats numObs)

-- With cap 1: between-statement merge after each block keeps paths
-- to 1 throughout. 4 statement merges, 1 obligation.
/--
info: merged=0 diverged=4 stmtMerged=4 obligations=1
-/
#guard_msgs in
#eval do
  let (stats, numObs) ← getEvalStats exponentialItePgm
    (options := { Core.VerifyOptions.quiet with pathCap := some 1 })
  IO.println (statsLine stats numObs)
