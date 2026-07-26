/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

meta import Strata.Transform.CommonSubexprElim
meta import Strata.Transform.CoreTransform
meta import Strata.Languages.Core.DDMTransform.Translate
meta import Strata.Languages.Core.DDMTransform.ASTtoCST
import StrataDDM.Integration.Lean.HashCommands


meta section

namespace Core.CSE.Tests

open Strata Lambda Imperative Core Core.Transform Core.CSE

private def translateCore (p : StrataDDM.Program) : Core.Program :=
  (TransM.run Inhabited.default (translateProgram p)).fst

/-- Translate and run common-subexpression elimination, returning the
    transformed program. -/
private def cseProgram (p : StrataDDM.Program) : Core.Program :=
  match Core.Transform.run (translateCore p) Core.CSE.runCSE
      { Core.Transform.CoreTransformState.emp with factory := some Core.Factory } with
  | .error e => panic! s!"CSE failed: {e}"
  | .ok (_changed, program) => program

/-! ## CSE across ITE branches and condition -/

private def iteDupProg :=
#strata
program Core;
procedure test(x : int, y : int) {
  if (x + y > 0) {
    assert (x + y >= 1);
  } else {
    assert (x + y <= 0);
  }
};
#end

/--
info: program Core;

procedure test (x : int, y : int)
{
  var $__cse.0 : int := x + y;
  if ($__cse.0 > 0) {
    assert [assert_0]: $__cse.0 >= 1;
  } else {
    assert [assert_1]: $__cse.0 <= 0;
  }
};
-/
#guard_msgs in
#eval IO.println (toString (cseProgram iteDupProg))

/-! ## No duplicates leaves body unchanged -/

private def noDupProg :=
#strata
program Core;
procedure test(x : int, y : int) {
  assume (x >= 5);
  assert (y <= 10);
};
#end

/--
info: program Core;

procedure test (x : int, y : int)
{
  assume [assume_0]: x >= 5;
  assert [assert_0]: y <= 10;
};
-/
#guard_msgs in
#eval IO.println (toString (cseProgram noDupProg))

/-! ## Duplicate ITE expression is lifted -/

private def iteDupExprProg :=
#strata
program Core;
procedure test(x : int, y : int) {
  assert ((if x > 0 then x else y) >= 0);
  assert ((if x > 0 then x else y) <= 100);
};
#end

/--
info: program Core;

procedure test (x : int, y : int)
{
  var $__cse.0 : int := if x > 0 then x else y;
  assert [assert_0]: $__cse.0 >= 0;
  assert [assert_1]: $__cse.0 <= 100;
};
-/
#guard_msgs in
#eval IO.println (toString (cseProgram iteDupExprProg))

/-! ## Subexpressions within function calls are lifted when duplicated -/

private def fnCallDupArgProg :=
#strata
program Core;
procedure test(x : int, y : int) {
  assert (x + y > 0);
  assert (x + y < 100);
};
#end

/--
info: program Core;

procedure test (x : int, y : int)
{
  var $__cse.0 : int := x + y;
  assert [assert_0]: $__cse.0 > 0;
  assert [assert_1]: $__cse.0 < 100;
};
-/
#guard_msgs in
#eval IO.println (toString (cseProgram fnCallDupArgProg))

/-! ## Unique subexpressions are not lifted -/

private def uniqueSubexprProg :=
#strata
program Core;
procedure test(x : int, y : int) {
  assert (x + 1 > 0);
  assert (y + 2 < 100);
};
#end

/--
info: program Core;

procedure test (x : int, y : int)
{
  assert [assert_0]: x + 1 > 0;
  assert [assert_1]: y + 2 < 100;
};
-/
#guard_msgs in
#eval IO.println (toString (cseProgram uniqueSubexprProg))

/-! ## Multi-pass: outer subsumes inner duplicate -/

-- `(x + 1) * 2` and `x + 1` are both duplicated, but `x + 1` is a subexpression
-- of `(x + 1) * 2` and so is dropped by `removeSubsumed` in pass 1. After pass
-- 1 lifts `(x + 1) * 2` into a var declaration, `x + 1` appears once in that
-- var-decl init AND once in the third assert, exposing a fresh duplicate that
-- pass 2 then extracts. Without fixpoint iteration the third assert would
-- still hold a free `(x + 1)` that duplicates the var-decl's init.
private def nestedDupProg :=
#strata
program Core;
procedure test(x : int) {
  assert ((x + 1) * 2 > 0);
  assert ((x + 1) * 2 < 100);
  assert (x + 1 > 50);
};
#end

/--
info: program Core;

procedure test (x : int)
{
  var $__cse.1 : int := x + 1;
  var $__cse.0 : int := $__cse.1 * 2;
  assert [assert_0]: $__cse.0 > 0;
  assert [assert_1]: $__cse.0 < 100;
  assert [assert_2]: $__cse.1 > 50;
};
-/
#guard_msgs in
#eval IO.println (toString (cseProgram nestedDupProg))

/-! ## Subexpression spanning a quantifier boundary

These tests exhibit the behavior of the current implementation of CSE.
-/

-- `x + 1` appears once outside a quantifier and once inside a `forall` body.
-- `collectSubexprs` resets `seen`/`dups` at the binder (only `memoHash` is
-- threaded), so the occurrence inside the quantifier is not counted as a
-- duplicate: `x + 1` is seen only once overall and is therefore NOT lifted.
-- Pins the conservative binder behavior of the `.quant` arm.
private def quantBoundaryProg :=
#strata
program Core;
procedure test (x : int)
{
  assert [a0]: x + 1 > 0;
  assert [a1]: forall y : int :: (x + 1) > y;
};
#end

/--
info: program Core;

procedure test (x : int)
{
  assert [a0]: x + 1 > 0;
  assert [a1]: forall y : int :: x + 1 > y;
};
-/
#guard_msgs in
#eval IO.println (toString (cseProgram quantBoundaryProg))

/-! ### A bound variable under a quantifier is never hoisted -/

-- `y + 1` references the quantifier-bound `y` and appears twice inside the
-- `forall` body. It must never be lifted: hoisting it would move a bound
-- variable out of its binder's scope. Output is unchanged.
private def quantBvarProg :=
#strata
program Core;
procedure test (x : int)
{
  assert [a0]: forall y : int :: (y + 1) > 0 && (y + 1) < 10;
};
#end

/--
info: program Core;

procedure test (x : int)
{
  assert [a0]: forall y : int :: y + 1 > 0 && y + 1 < 10;
};
-/
#guard_msgs in
#eval IO.println (toString (cseProgram quantBvarProg))

/-! ### A bound variable under a lambda (`abs`) is never hoisted -/

-- `y + 1` references the lambda-bound `y` and appears twice inside the `fun`
-- body. `collectSubexprs` does not descend into `abs` bodies at all, so it is
-- never recorded and never lifted (no scope escape). Output is unchanged.
private def absBvarProg :=
#strata
program Core;
procedure test (x : int)
{
  var g : int -> int := fun y : int => (y + 1) * (y + 1);
  assert [a0]: x > 0;
};
#end

/--
info: program Core;

procedure test (x : int)
{
  var g : int -> int := fun y : int => (y + 1) * (y + 1);
  assert [a0]: x > 0;
};
-/
#guard_msgs in
#eval IO.println (toString (cseProgram absBvarProg))

/-! ### A bvar-free duplicate is lifted and substituted even inside a quantifier -/

-- `x + 1` is duplicated *outside* any binder (asserts `a0`/`a1`), so it is
-- lifted to `$__cse.0`. It is bvar-free, so substituting it is sound even for
-- the occurrence inside the `forall` body — `replaceExprs` rewrites there too.
private def quantLiftProg :=
#strata
program Core;
procedure test (x : int)
{
  assert [a0]: x + 1 > 0;
  assert [a1]: x + 1 < 100;
  assert [a2]: forall y : int :: (x + 1) > y;
};
#end

/--
info: program Core;

procedure test (x : int)
{
  var $__cse.0 : int := x + 1;
  assert [a0]: $__cse.0 > 0;
  assert [a1]: $__cse.0 < 100;
  assert [a2]: forall y : int :: $__cse.0 > y;
};
-/
#guard_msgs in
#eval IO.println (toString (cseProgram quantLiftProg))

end Core.CSE.Tests
end
