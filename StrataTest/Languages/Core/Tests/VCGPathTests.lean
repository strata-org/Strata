/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Core.Verifier

---------------------------------------------------------------------
namespace Strata

-- `second`'s obligation is checked once. However, `first`'s `post` is checked
-- twice because we don't (yet) do within-procedure path merging.
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

Obligation: wrong_ensures_0
Property: assert
Result: ✅ pass

Obligation: wrong_ensures_0
Property: assert
Result: ✅ pass
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

Obligation: post
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

Obligation: post
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval verify noDupConcreteFalse (options := .quiet)
