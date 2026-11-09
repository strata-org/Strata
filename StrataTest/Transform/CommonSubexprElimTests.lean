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
      { Core.Transform.CoreTransformState.emp with factory := Core.Factory } with
  | .error e => panic! s!"CSE failed: {e}"
  | .ok (_changed, program) => program

/-! ## CSE across ITE branches and condition -/

private def iteDupProg :=
#strata
program Core;
procedure test(x : int, y : int) {
  if (int.gt(int.add(x, y), 0)) {
    assert (int.ge(int.add(x, y), 1));
  } else {
    assert (int.le(int.add(x, y), 0));
  }
};
#end

/--
info: program Core;

procedure test (x : int, y : int)
{
  var $__cse.0 : int := int.add(x, y);
  if (int.gt($__cse.0, 0)) {
    assert [assert_0]: int.ge($__cse.0, 1);
  } else {
    assert [assert_1]: int.le($__cse.0, 0);
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
  assume (int.ge(x, 5));
  assert (int.le(y, 10));
};
#end

/--
info: program Core;

procedure test (x : int, y : int)
{
  assume [assume_0]: int.ge(x, 5);
  assert [assert_0]: int.le(y, 10);
};
-/
#guard_msgs in
#eval IO.println (toString (cseProgram noDupProg))

/-! ## Duplicate ITE expression is lifted -/

private def iteDupExprProg :=
#strata
program Core;
procedure test(x : int, y : int) {
  assert (int.ge((if int.gt(x, 0) then x else y), 0));
  assert (int.le((if int.gt(x, 0) then x else y), 100));
};
#end

/--
info: program Core;

procedure test (x : int, y : int)
{
  var $__cse.0 : int := if int.gt(x, 0) then x else y;
  assert [assert_0]: int.ge($__cse.0, 0);
  assert [assert_1]: int.le($__cse.0, 100);
};
-/
#guard_msgs in
#eval IO.println (toString (cseProgram iteDupExprProg))

/-! ## Subexpressions within function calls are lifted when duplicated -/

private def fnCallDupArgProg :=
#strata
program Core;
procedure test(x : int, y : int) {
  assert (int.gt(int.add(x, y), 0));
  assert (int.lt(int.add(x, y), 100));
};
#end

/--
info: program Core;

procedure test (x : int, y : int)
{
  var $__cse.0 : int := int.add(x, y);
  assert [assert_0]: int.gt($__cse.0, 0);
  assert [assert_1]: int.lt($__cse.0, 100);
};
-/
#guard_msgs in
#eval IO.println (toString (cseProgram fnCallDupArgProg))

/-! ## Unique subexpressions are not lifted -/

private def uniqueSubexprProg :=
#strata
program Core;
procedure test(x : int, y : int) {
  assert (int.gt(int.add(x, 1), 0));
  assert (int.lt(int.add(y, 2), 100));
};
#end

/--
info: program Core;

procedure test (x : int, y : int)
{
  assert [assert_0]: int.gt(int.add(x, 1), 0);
  assert [assert_1]: int.lt(int.add(y, 2), 100);
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
  assert (int.gt(int.mul(int.add(x, 1), 2), 0));
  assert (int.lt(int.mul(int.add(x, 1), 2), 100));
  assert (int.gt(int.add(x, 1), 50));
};
#end

/--
info: program Core;

procedure test (x : int)
{
  var $__cse.1 : int := int.add(x, 1);
  var $__cse.0 : int := int.mul($__cse.1, 2);
  assert [assert_0]: int.gt($__cse.0, 0);
  assert [assert_1]: int.lt($__cse.0, 100);
  assert [assert_2]: int.gt($__cse.1, 50);
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
  assert [a0]: int.gt(int.add(x, 1), 0);
  assert [a1]: forall y : int :: int.gt(int.add(x, 1), y);
};
#end

/--
info: program Core;

procedure test (x : int)
{
  assert [a0]: int.gt(int.add(x, 1), 0);
  assert [a1]: forall y : int :: int.gt(int.add(x, 1), y);
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
  assert [a0]: forall y : int :: int.gt(int.add(y, 1), 0) && int.lt(int.add(y, 1), 10);
};
#end

/--
info: program Core;

procedure test (x : int)
{
  assert [a0]: forall y : int :: int.gt(int.add(y, 1), 0) && int.lt(int.add(y, 1), 10);
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
  var g : int -> int := fun y : int => int.mul(int.add(y, 1), int.add(y, 1));
  assert [a0]: int.gt(x, 0);
};
#end

/--
info: program Core;

procedure test (x : int)
{
  var g : int -> int := fun y : int => int.mul(int.add(y, 1), int.add(y, 1));
  assert [a0]: int.gt(x, 0);
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
  assert [a0]: int.gt(int.add(x, 1), 0);
  assert [a1]: int.lt(int.add(x, 1), 100);
  assert [a2]: forall y : int :: int.gt(int.add(x, 1), y);
};
#end

/--
info: program Core;

procedure test (x : int)
{
  var $__cse.0 : int := int.add(x, 1);
  assert [a0]: int.gt($__cse.0, 0);
  assert [a1]: int.lt($__cse.0, 100);
  assert [a2]: forall y : int :: int.gt($__cse.0, y);
};
-/
#guard_msgs in
#eval IO.println (toString (cseProgram quantLiftProg))

/-! ## Each abbreviated occurrence keeps its own source location

The three occurrences of `int.add(x, y)` below are at different source ranges.
CSE finds them as duplicates although their locations differ, and each
`$__cse.0` that replaces one carries the range of the occurrence it replaces. -/

private def locDupProg :=
#strata
program Core;
procedure test(x : int, y : int) {
  assert (int.gt(int.add(x, y), 0));
  assert (int.lt(int.add(x, y), 9));
  assert (int.le(int.add(x, y), 5));
};
#end

/-- The source ranges of the `$__cse.0` references in `p`'s first procedure. -/
private def cseVarRanges (p : Core.Program) : List (Nat × Nat) :=
  let rec go : Expression.Expr → List (Nat × Nat)
    | .fvar m x _ => if x.name == "$__cse.0" then [(m.range.start.byteIdx,
        m.range.stop.byteIdx)] else []
    | .app _ f a => go f ++ go a
    | .ite _ c t e => go c ++ go t ++ go e
    | .eq _ a b => go a ++ go b
    | .abs _ _ _ b => go b
    | .quant _ _ _ _ tr b => go tr ++ go b
    | _ => []
  match p.decls.findSome? (fun | .proc pr _ => some pr | _ => none) with
  | some pr =>
    match pr.body with
    | .structured ss => (Statements.collectExprs ss).flatMap go
    | .cfg _ => []
  | none => []

-- The duplicate is found, and its three uses have three distinct ranges: each
-- abbreviated occurrence carries the range of the occurrence it replaces.
#guard ((toString (cseProgram locDupProg)).splitOn "var $__cse.0").length == 2
#guard (cseVarRanges (cseProgram locDupProg)).length == 3
#guard (cseVarRanges (cseProgram locDupProg)).eraseDups.length == 3

/-! ## `beqIgnoringMetadata` compares modulo metadata and by structure

CSE deduplicates by `beqIgnoringMetadata`, which ignores every node's source
location and decides equality purely by structure. The accelerated runtime
implementation (`beqIgnoringMetadataUnsafe`, a per-level pointer-equality fast
path) decides the same relation as the pure definition, which is why it is a
sound `@[implemented_by]`: a pointer hit means the two nodes are literally the
same object, and `beqIgnoringMetadata_refl` makes the pure function return `true`
there too. These guards pin both halves: equal structure under different
locations is still equal (so duplicates are found), and different structure at
the *same* location is still unequal (so unrelated terms are never merged). -/

private def mdA : ExprSourceLoc := ExprSourceLoc.synthesized "A"
private def mdB : ExprSourceLoc := ExprSourceLoc.synthesized "B"
private def vx : Expression.Expr := .fvar mdA ⟨"x", ()⟩ none
/-- `int.add(x, x)`, with the shared child `vx` under both arguments, rooted at
    location A. -/
private def addA : Expression.Expr :=
  .app mdA (.app mdA (.op mdA ⟨"int.Add", ()⟩ none) vx) vx
/-- The same structure as `addA`, but its root carries location B instead of A
    (as a metadata re-tag produces). -/
private def addB : Expression.Expr :=
  .app mdB (.app mdA (.op mdA ⟨"int.Add", ()⟩ none) vx) vx
/-- `int.mul(x, x)`: a different operator from `addA`, but rooted at the *same*
    location A. -/
private def mulA : Expression.Expr :=
  .app mdA (.app mdA (.op mdA ⟨"int.Mul", ()⟩ none) vx) vx
/-- A doubling chain of depth `k`: `int.add` nested `k` deep, both arguments the
    same shared subterm, so its shared DAG is `O(k)` while its logical tree is
    `2^k` -- the shape CSE deduplicates. -/
private def dblTerm : Nat → Expression.Expr
  | 0 => vx
  | k + 1 => let w := dblTerm k; .app mdA (.app mdA (.op mdA ⟨"int.Add", ()⟩ none) w) w

-- The pointer-accelerated impl (`beqIgnoringMetadataFast`) must decide exactly
-- the pure spec (`beqIgnoringMetadata`) on every pair, so a drift in either the
-- impl or the spec fails the build. Pairs cover: equal modulo metadata but NOT
-- pointer-equal (the recursive path, `addA`/`addB` -- the `locDupProg` pattern
-- of `int.add` at two source locations), reflexive (the pointer shortcut), and
-- the doubling chain with a root re-tag (the exact shape CSE deduplicates).
#guard LExpr.beqIgnoringMetadataFast addA addB == addA.beqIgnoringMetadata addB
#guard LExpr.beqIgnoringMetadataFast addA addA == addA.beqIgnoringMetadata addA
#guard LExpr.beqIgnoringMetadataFast addA mulA == addA.beqIgnoringMetadata mulA
#guard LExpr.beqIgnoringMetadataFast (dblTerm 8) (dblTerm 8)
         == (dblTerm 8).beqIgnoringMetadata (dblTerm 8)
#guard LExpr.beqIgnoringMetadataFast (dblTerm 8) (LExpr.replaceMetadata1 mdB (dblTerm 8))
         == (dblTerm 8).beqIgnoringMetadata (LExpr.replaceMetadata1 mdB (dblTerm 8))
-- The intended outcomes: a duplicate is found (equal modulo metadata), and two
-- subterms of different meaning at the same location are NOT merged.
#guard addA.beqIgnoringMetadata addB
#guard !(addA.beqIgnoringMetadata mulA)


end Core.CSE.Tests
end
