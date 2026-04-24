/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Core.Verifier

---------------------------------------------------------------------
namespace Strata

/-- Extract evaluator statistics from a program without running the solver. -/
private def getEvalStats (program : Strata.Program)
    (options : Core.VerifyOptions := .quiet) : IO (Statistics × Nat) := do
  let (coreProgram, _) := Core.getProgram program
  let coreProgram ← IO.ofExcept (Core.typeCheck options coreProgram)
  match Core.buildEnv options coreProgram with
  | .error _ => return ({}, 0)
  | .ok (E, declStats) =>
    match Core.Program.eval E with
    | .error _ => return ({}, 0)
    | .ok (envs, evalStats) =>
      let numObligations := envs.foldl (fun acc e => acc + e.deferred.size) 0
      let stats := declStats.merge evalStats
      return (stats, numObligations)

private def statsLine (stats : Statistics) (numObs : Nat) : String :=
  let merged := stats.get s!"{Core.Evaluator.Stats.processIteBranches_merged}"
  let diverged := stats.get s!"{Core.Evaluator.Stats.processIteBranches_diverged}"
  let stmtMerged := stats.get s!"{Core.Evaluator.Stats.betweenStmt_capMerged}"
  s!"merged={merged} diverged={diverged} stmtMerged={stmtMerged} obligations={numObs}"

---------------------------------------------------------------------
-- issue419TestPgm
---------------------------------------------------------------------

def issue419TestPgm :=
#strata
program Core;
procedure first(x : int, out r : int)
spec { ensures [post]: (r >= 0); }
{
  body: {
    if (x < 0) { r := 0 - x; exit body; }
    r := x;
    exit body;
  }
};

procedure second() { assert [a]: true; };
#end

-- No cap: two separate `post` VCs, one per path.
-- `second`'s obligation is checked once. `first`'s `post` is checked
-- on two paths but mergeByAssertion deduplicates the results.

/--
info: [Strata.Core] Type checking succeeded.


VCs:
Label: post
Property: assert
Assumptions:
<label_ite_cond_true: x < 0>: $__x0 < 0
Obligation:
0 - $__x0 >= 0

Label: post
Property: assert
Assumptions:
<label_ite_cond_false: !(x < 0)>: if $__x0 < 0 then false else true
Obligation:
$__x0 >= 0

Label: a
Property: assert
Obligation:
true

---
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

/--
info: merged=0 diverged=1 stmtMerged=0 obligations=3
-/
#guard_msgs in
#eval do
  let (stats, numObs) ← getEvalStats issue419TestPgm
  IO.println (statsLine stats numObs)

-- Cap 1: two paths merged into one `post` VC with an ITE obligation.
/--
info: [Strata.Core] Type checking succeeded.


VCs:
Label: post
Property: assert
Assumptions:
<label_ite_cond_true: x < 0>: if $__x0 < 0 then $__x0 < 0 else true
<label_ite_cond_false: !(x < 0)>: if if $__x0 < 0 then false else true then if $__x0 < 0 then false else true else true
Obligation:
if $__x0 < 0 then 0 - $__x0 else $__x0 >= 0

Label: a
Property: assert
Obligation:
true

---
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
  (options := { Core.VerifyOptions.default with pathCap := some 1 })

/--
info: merged=0 diverged=1 stmtMerged=1 obligations=2
-/
#guard_msgs in
#eval do
  let (stats, numObs) ← getEvalStats issue419TestPgm
    (options := { Core.VerifyOptions.quiet with pathCap := some 1 })
  IO.println (statsLine stats numObs)

-- Cap 4: under cap, same as no cap.
/--
info: merged=0 diverged=1 stmtMerged=0 obligations=3
-/
#guard_msgs in
#eval do
  let (stats, numObs) ← getEvalStats issue419TestPgm
    (options := { Core.VerifyOptions.quiet with pathCap := some 4 })
  IO.println (statsLine stats numObs)

---------------------------------------------------------------------
-- sequentialExitItePgm
---------------------------------------------------------------------

-- Each ITE has one branch that exits the enclosing block, so
-- paths grow linearly even without the cap.
def sequentialExitItePgm :=
#strata
program Core;


procedure p(c1 : bool, c2 : bool, c3 : bool, c4 : bool, out r : int)
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

/--
info:
Obligation: post
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval verify sequentialExitItePgm (options := .quiet)
/--
info: merged=0 diverged=4 stmtMerged=0 obligations=5
-/
#guard_msgs in
#eval do
  let (stats, numObs) ← getEvalStats sequentialExitItePgm
  IO.println (statsLine stats numObs)

-- Cap 1: between-statement merge keeps fallthrough to 1 path.
/--
info:
Obligation: post
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval verify sequentialExitItePgm
  (options := { Core.VerifyOptions.quiet with pathCap := some 1 })

/--
info: merged=0 diverged=4 stmtMerged=1 obligations=1
-/
#guard_msgs in
#eval do
  let (stats, numObs) ← getEvalStats sequentialExitItePgm
    (options := { Core.VerifyOptions.quiet with pathCap := some 1 })
  IO.println (statsLine stats numObs)

---------------------------------------------------------------------
-- exponentialItePgm
---------------------------------------------------------------------

-- Each ITE has both branches continuing (exit from the inner block), so
-- paths double at each ITE: 2^4 = 16 without cap.
def exponentialItePgm :=
#strata
program Core;
procedure p(c1 : bool, c2 : bool, c3 : bool, c4 : bool, out r : int)
spec { ensures [post]: (r >= 0); }
{
  b1: { if (c1) { r := 1; exit b1; } r := 2; }
  b2: { if (c2) { r := r + 10; exit b2; } r := r + 20; }
  b3: { if (c3) { r := r + 100; exit b3; } r := r + 200; }
  b4: { if (c4) { r := r + 1000; exit b4; } r := r + 2000; }
};
#end

/--
info: merged=0 diverged=15 stmtMerged=0 obligations=16
-/
#guard_msgs in
#eval do
  let (stats, numObs) ← getEvalStats exponentialItePgm
  IO.println (statsLine stats numObs)

-- Cap 1: 4 statement merges, 1 obligation.
/--
info: merged=0 diverged=4 stmtMerged=4 obligations=1
-/
#guard_msgs in
#eval do
  let (stats, numObs) ← getEvalStats exponentialItePgm
    (options := { Core.VerifyOptions.quiet with pathCap := some 1 })
  IO.println (statsLine stats numObs)

-- Cap 2: batch processes both paths through each block, merges to 2.
/--
info: merged=0 diverged=7 stmtMerged=3 obligations=2
-/
#guard_msgs in
#eval do
  let (stats, numObs) ← getEvalStats exponentialItePgm
    (options := { Core.VerifyOptions.quiet with pathCap := some 2 })
  IO.println (statsLine stats numObs)

---------------------------------------------------------------------
-- nestedItePgm
---------------------------------------------------------------------

-- Outer ITEs whose branches contain inner ITEs with exits. Each outer branch
-- produces 2 results, so the outer ITE produces 4 (not 2). Two such outer ITEs
-- give 4×4 = 16.
def nestedItePgm :=
#strata
program Core;
procedure p(c1 : bool, c2 : bool, x : bool, y : bool, out r : int)
spec { ensures [post]: (r >= 0); }
{
  b1: {
    if (c1) {
      inner1: { if (x) { r := 1; exit inner1; } r := 2; }
    } else {
      inner2: { if (y) { r := 3; exit inner2; } r := 4; }
    }
  }
  b2: {
    if (c2) {
      inner3: { if (x) { r := r + 10; exit inner3; } r := r + 20; }
    } else {
      inner4: { if (y) { r := r + 30; exit inner4; } r := r + 40; }
    }
  }
};
#end

/--
info: merged=0 diverged=15 stmtMerged=0 obligations=16
-/
#guard_msgs in
#eval do
  let (stats, numObs) ← getEvalStats nestedItePgm
  IO.println (statsLine stats numObs)

-- Cap 1:
/--
info: merged=2 diverged=4 stmtMerged=4 obligations=1
-/
#guard_msgs in
#eval do
  let (stats, numObs) ← getEvalStats nestedItePgm
    (options := { Core.VerifyOptions.quiet with pathCap := some 1 })
  IO.println (statsLine stats numObs)

---------------------------------------------------------------------
-- sameExitCapPgm
---------------------------------------------------------------------

-- Both branches exit to the same label.
def sameExitCapPgm :=
#strata
program Core;
procedure p(c1 : bool, out r : int)
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
info: merged=0 diverged=1 stmtMerged=0 obligations=2
-/
#guard_msgs in
#eval do
  let (stats, numObs) ← getEvalStats sameExitCapPgm
  IO.println (statsLine stats numObs)

/--
info: merged=0 diverged=1 stmtMerged=1 obligations=1
-/
#guard_msgs in
#eval do
  let (stats, numObs) ← getEvalStats sameExitCapPgm
    (options := { Core.VerifyOptions.quiet with pathCap := some 1 })
  IO.println (statsLine stats numObs)

---------------------------------------------------------------------
-- buggyPgm — negative soundness test
---------------------------------------------------------------------

-- The else branch sets `r := 0`, violating `ensures (r > 0)`.
-- This must fail both without and with `--path-cap <n>`, confirming
-- that merging paths does not weaken VCs.
def buggyPgm :=
#strata
program Core;
procedure buggy(c1 : bool, out r : int)
spec { ensures [post]: (r > 0); }
{
  done: {
    if (c1) { r := 1; exit done; }
    r := 0;
  }
};
#end

/--
info:
Obligation: post
Property: assert
Result: ❌ fail
-/
#guard_msgs in
#eval verify buggyPgm (options := .quiet)

/-- info: merged=0 diverged=1 stmtMerged=0 obligations=2 -/
#guard_msgs in
#eval do
  let (stats, numObs) ← getEvalStats buggyPgm (options := .quiet)
  IO.println (statsLine stats numObs)

/--
info:
Obligation: post
Property: assert
Result: ❌ fail
-/
#guard_msgs in
#eval verify buggyPgm
  (options := { Core.VerifyOptions.quiet with pathCap := some 1 })

/-- info: merged=0 diverged=1 stmtMerged=1 obligations=1 -/
#guard_msgs in
#eval do
  let (stats, numObs) ← getEvalStats buggyPgm
    (options := { Core.VerifyOptions.quiet with pathCap := some 1 })
  IO.println (statsLine stats numObs)

/--
info:
Obligation: post
Property: assert
Result: ❌ fail
-/
#guard_msgs in
#eval verify buggyPgm
  (options := { Core.VerifyOptions.quiet with pathCap := some 5 })

/-- info: merged=0 diverged=1 stmtMerged=0 obligations=2 -/
#guard_msgs in
#eval do
  let (stats, numObs) ← getEvalStats buggyPgm
    (options := { Core.VerifyOptions.quiet with pathCap := some 5 })
  IO.println (statsLine stats numObs)

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
procedure p() {
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
procedure p() {
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
procedure p() {
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
procedure p() {
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
procedure p() {
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
procedure p(x : bool) {
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
procedure q(x : bool) {
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
