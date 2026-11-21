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
    | .structured ss _ => (Statements.collectExprs ss).flatMap go
    | .cfg _ _ | .abstract => []
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


/-! ## `stmtRunCSESinglePass` agrees with `stmtRunCSE`

`runCSE` runs `stmtRunCSESinglePass`; `stmtRunCSE` is its specification. The
checks below run both on the same bodies and compare the results: the same next
index, and the same statements once locations are erased (the two may keep the
location of different occurrences; `toString` prints no location, so the printed
programs are equal too). -/

/-- `ss` with every location of its expressions erased. -/
private def eraseStmts (ss : Statements) : Statements :=
  Statements.mapExprs Core.eraseLocs ss

/-- Whether `stmtRunCSE` and `stmtRunCSESinglePass` agree on `ss` from index `idx`:
    the same next index, the same statements up to locations, and the same
    printed statements. -/
private def agree (ss : Statements) (idx : Nat := 0) : Bool :=
  let (a, i) := stmtRunCSE ss idx
  let (b, j) := stmtRunCSESinglePass ss idx
  i == j && decide (eraseStmts a = eraseStmts b) &&
    toString (Std.format a) == toString (Std.format b)

/-- `agree` on every structured procedure body of `p`, threading the index from
    one procedure to the next as `runCSE` does. -/
private def progAgree (p : Core.Program) : Bool := Id.run do
  let mut idx := 0
  let mut ok := Bool.true
  for d in p.decls do
    match d with
    | .proc proc _ =>
      match proc.body with
      | .structured ss _ =>
        ok := ok && agree ss idx
        idx := (stmtRunCSE ss idx).2
      | .cfg _ _ | .abstract => pure ()
    | _ => pure ()
  return ok

#guard progAgree (translateCore iteDupProg)
#guard progAgree (translateCore noDupProg)
#guard progAgree (translateCore iteDupExprProg)
#guard progAgree (translateCore fnCallDupArgProg)
#guard progAgree (translateCore uniqueSubexprProg)
#guard progAgree (translateCore nestedDupProg)
#guard progAgree (translateCore quantBoundaryProg)
#guard progAgree (translateCore quantBvarProg)
#guard progAgree (translateCore absBvarProg)
#guard progAgree (translateCore quantLiftProg)
#guard progAgree (translateCore locDupProg)

/-! ### Bodies built directly

Expressions built as shared DAGs, so that a nesting depth of 20 or more does not
need an exponentially long program text. -/

private def mT : ExprSourceLoc := ExprSourceLoc.synthesized "T"
private def mU : ExprSourceLoc := ExprSourceLoc.synthesized "U"
/-- An `int` variable. -/
private def vI (n : String) : Expression.Expr := .fvar mT ⟨n, ()⟩ (some .int)
/-- A `bool` variable. -/
private def vB (n : String) : Expression.Expr := .fvar mT ⟨n, ()⟩ (some .bool)
/-- A variable without a type: every expression containing it is untyped. -/
private def vU (n : String) : Expression.Expr := .fvar mT ⟨n, ()⟩ none
/-- An integer constant. -/
private def cI (i : Int) : Expression.Expr := .intConst mT i
/-- A binary `int` operator. -/
private def op2 (n : String) : Expression.Expr :=
  .op mT ⟨n, ()⟩ (some (.arrow .int (.arrow .int .int)))
/-- `int.add(a, b)`. -/
private def add (a b : Expression.Expr) : Expression.Expr := .app mT (.app mT (op2 "Int.Add") a) b
/-- `int.mul(a, b)`. -/
private def mul (a b : Expression.Expr) : Expression.Expr := .app mT (.app mT (op2 "Int.Mul") a) b
/-- `int.lt(a, b)`. -/
private def lt (a b : Expression.Expr) : Expression.Expr :=
  .app mT (.app mT (.op mT ⟨"Int.Lt", ()⟩ (some (.arrow .int (.arrow .int .bool)))) a) b
/-- `assert [l]: e`. -/
private def asrt (l : String) (e : Expression.Expr) : Statement := Statement.assert l e .empty
/-- `assume [l]: e`. -/
private def asm (l : String) (e : Expression.Expr) : Statement := Statement.assume l e .empty

/-- The value of `y` after `k` merged branches `if (g_i) { y := y * i + y }`:
    `ite(g_k, e_{k-1} * k + e_{k-1}, e_{k-1})`, the shape symbolic execution's
    merges produce. Every `e_i` occurs twice in `e_{i+1}`, so the duplicates nest
    `k` deep. -/
private def mergeChain : Nat → Expression.Expr
  | 0 => vI "y"
  | k + 1 =>
    let e := mergeChain k
    .ite mT (vB s!"g{k}") (add (mul e (cI (k + 1))) e) e

/-- Two checks of the value of a chain of `k` merges. -/
private def chainBody (k : Nat) : Statements :=
  [asrt "a0" (lt (cI 0) (mergeChain k)), asrt "a1" (lt (mergeChain k) (cI 100))]

#guard agree (chainBody 1)
#guard agree (chainBody 5)
#guard agree (chainBody 25)
-- `e_1, …, e_25` are named.
#guard (stmtRunCSESinglePass (chainBody 25) 0).2 == 25

-- Deeply nested duplicates take the single pass, without falling back to rounds.
#guard !singlePassFallsBack (chainBody 25)
#guard !singlePassFallsBack (chainBody 400)
#guard (stmtRunCSESinglePass (chainBody 400) 0).2 == 400

/-- An untyped duplicate `h(u, int.add(x, y))` holding the typed duplicate
    `int.add(x, y)`, which also occurs twice outside it. The untyped duplicate is
    never named, and nothing below it is either; `int.mul(x, y)`, a duplicate
    outside it, is. -/
private def blockerBody : Statements :=
  let t := add (vI "x") (vI "y")
  let b := .app mT (.app mT (.op mT ⟨"h", ()⟩ none) (vU "u")) t
  [asrt "a0" (.eq mT b b), asrt "a1" (lt t (mul (vI "x") (vI "y"))),
   asrt "a2" (lt (mul (vI "x") (vI "y")) t), asrt "a3" (.eq mT b (cI 0))]

#guard agree blockerBody
#guard (stmtRunCSESinglePass blockerBody 0).2 == 1

/-- Duplicates inside a quantifier and a lambda: `int.add(x, 1)` occurs twice
    outside any binder and once under each binder; `int.add(z, 1)` mentions the
    bound variable. An application holding a quantifier is not bvar-free, so the
    walk expands it at each of its two occurrences and `int.mul(x, x)` below it is
    counted twice. -/
private def binderBody : Statements :=
  let t := add (vI "x") (cI 1)
  let q : Expression.Expr := .quant mT .all "z" (some .int) (.bvar mT 0)
    (lt (add (.bvar mT 0) (cI 1)) t)
  let l : Expression.Expr := .abs mT "z" (some .int) (add (.bvar mT 0) t)
  let andQ := .app mT (.app mT (.op mT ⟨"Bool.And", ()⟩
    (some (.arrow .bool (.arrow .bool .bool)))) (lt (mul (vI "x") (vI "x")) (cI 3))) q
  [asrt "a0" (lt t (cI 0)), asrt "a1" (lt t (cI 9)), asrt "a2" q,
   asrt "a3" (lt (.app mT l (cI 2)) (cI 4)), asrt "a4" andQ, asrt "a5" andQ]

#guard agree binderBody

/-- Partial applications: `int.add(x + 1)` is the argument of two different functions,
    `g` and `h`, so it is a duplicate, and it is also the function of
    `int.add(x + 1, w)`. Naming it would change how often that application's arguments
    are counted, so `stmtRunCSESinglePass` uses `stmtRunCSE` on this body. -/
private def partialBody : Statements :=
  let w := mul (vI "y") (vI "y")
  let pa := .app mT (op2 "Int.Add") (add (vI "x") (cI 1))
  let fnTy : Option LMonoTy := some (.arrow (.arrow .int .int) .int)
  let g (e : Expression.Expr) := .app mT (.op mT ⟨"g", ()⟩ fnTy) e
  let h (e : Expression.Expr) := .app mT (.op mT ⟨"h", ()⟩ fnTy) e
  [asrt "a0" (lt (g pa) (cI 0)), asrt "a1" (lt (h pa) (cI 1)),
   asrt "a2" (lt (.app mT pa w) (cI 2)), asrt "a3" (lt w (cI 3))]

#guard agree partialBody
#guard singlePassFallsBack partialBody

/-- Partial applications on spines only: `int.add(x + 1)` is shared by two full
    applications but is never an argument, so it is not a duplicate. -/
private def spineBody : Statements :=
  let pa := .app mT (op2 "Int.Add") (add (vI "x") (cI 1))
  [asrt "a0" (lt (.app mT pa (cI 2)) (cI 0)), asrt "a1" (lt (.app mT pa (cI 3)) (cI 0))]

#guard agree spineBody

/-- A body that already declares `$__cse.0`: starting at index 1 avoids it. -/
private def collisionBody : Statements :=
  let c := vI "$__cse.0"
  [asrt "a0" (lt (add c (vI "x")) (cI 0)), asrt "a1" (lt (add c (vI "x")) (cI 1))]

#guard agree collisionBody 1
#guard (stmtRunCSESinglePass collisionBody 1).2 == 2

/-- Many duplicates at the same level, named in hash order, and their copies at
    other locations. -/
private def bucketBody : Statements :=
  let ts := (List.range 12).map fun i => add (vI s!"x{i}") (cI (Int.ofNat i))
  ts.flatMap fun t =>
    [asrt "a" (lt t (cI 0)), asm "b" (lt (LExpr.replaceMetadata1 mU t) (cI 1))]

#guard agree bucketBody
#guard agree bucketBody 7

/-! ### Random bodies

`randomBody seed` builds pools of shared `int`, `bool` and function-valued
expressions from a few variables (one untyped) by applying operators, shared
partial applications, `ite`, `eq`, quantifiers and lambdas to earlier pool
entries (mostly recent ones, so duplicates nest), and copies entries at another
location; it then checks some of them in assertions, assumptions, an `init` and
an `if`. -/

/-- One step of a 64-bit linear congruential generator. -/
private def lcg (s : Nat) : Nat :=
  (s * 6364136223846793005 + 1442695040888963407) % 18446744073709551616

/-- An entry of `pool` picked by `s`: one of the last three with probability 2/3. -/
private def pickFrom (pool : Array Expression.Expr) (s : Nat) : Expression.Expr :=
  let n := pool.size
  let i := if s % 3 == 0 then (s / 3) % n else n - 1 - (s / 3) % (min n 3)
  pool[i]!

/-- `Bool.And(a, b)`. -/
private def andE (a b : Expression.Expr) : Expression.Expr :=
  .app mT (.app mT (.op mT ⟨"Bool.And", ()⟩ (some (.arrow .bool (.arrow .bool .bool)))) a) b

/-- A random body (see above). -/
private def randomBody (seed : Nat) : Statements := Id.run do
  let mut s := lcg (seed + 1)
  let mut ints : Array Expression.Expr := #[vI "x", vI "y", vI "$__cse.0", cI 1]
  let mut bools : Array Expression.Expr := #[vB "b", vB "c"]
  let mut fns : Array Expression.Expr := #[.op mT ⟨"f", ()⟩ (some (.arrow .int .int))]
  let steps := 8 + seed % 30
  for _ in [0:steps] do
    s := lcg s
    let r := s / 64
    let i₁ := pickFrom ints r
    let i₂ := pickFrom ints (lcg r)
    let b₁ := pickFrom bools (lcg (lcg r))
    let b₂ := pickFrom bools (lcg (lcg (lcg r)))
    let f₁ := pickFrom fns (lcg (lcg (lcg (lcg r))))
    match s % 19 with
    | 0 | 1 => ints := ints.push (add i₁ i₂)
    | 2 => ints := ints.push (mul i₁ i₂)
    | 3 | 4 => ints := ints.push (.ite mT b₁ i₁ i₂)
    | 5 => ints := ints.push (.app mT f₁ i₁)
    | 6 => ints := ints.push (LExpr.replaceMetadata1 mU i₁)
    | 7 => ints := ints.push (.app mT (.app mT (.op mT ⟨"h", ()⟩ none) (vU "u")) i₁)
    | 8 =>
      let g : Expression.Expr := .op mT ⟨"g", ()⟩ (some (.arrow (.arrow .int .int) .int))
      ints := ints.push (.app mT g f₁)
    | 9 | 10 => bools := bools.push (lt i₁ i₂)
    | 11 => bools := bools.push (.eq mT i₁ i₂)
    | 12 => bools := bools.push (.ite mT b₁ b₂ (lt i₂ i₁))
    | 13 =>
      let q : Expression.Expr := .quant mT .all "z" (some .int) (.bvar mT 0) (lt (.bvar mT 0) i₁)
      bools := bools.push q
    | 14 => bools := bools.push (andE b₁ b₂)
    | 15 =>
      let q : Expression.Expr :=
        .quant mT .exist "z" (some .int) (.bvar mT 0) (.eq mT (.bvar mT 0) (add i₁ i₂))
      bools := bools.push (andE b₁ q)
    | 16 => fns := fns.push (.app mT (op2 "Int.Add") i₁)
    | 17 => fns := fns.push (.abs mT "z" (some .int) (add (.bvar mT 0) i₁))
    | _ => bools := bools.push (LExpr.replaceMetadata1 mU b₁)
  let bool (k : Nat) : Expression.Expr := pickFrom bools (lcg (s + k))
  let int (k : Nat) : Expression.Expr := pickFrom ints (lcg (s + k))
  let stmts : Statements :=
    [asrt "a0" (bool 0), asm "a1" (bool 1),
     Statement.init ⟨"v", ()⟩ (.forAll [] .int) (.det (int 2)) .empty,
     Imperative.Stmt.ite (.det (bool 3)) [asrt "a2" (bool 4)] [asrt "a3" (lt (int 5) (int 6))]
       .empty,
     asrt "a4" (bool 7), asrt "a5" (.eq mT (int 8) (int 9))]
  return stmts.take (2 + seed % 5) ++ stmts.drop 5

/-- The seeds below 600 on which the two passes disagree. -/
private def randomDisagreements : List Nat :=
  (List.range 600).filter fun seed => !agree (randomBody seed) (seed % 3)

/-- info: [] -/
#guard_msgs in
#eval randomDisagreements

end Core.CSE.Tests
end
