/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
import Strata.Transform.GuardProp
import Strata.Languages.Core
import Strata.MetaVerifier
import StrataTest.Languages.Core.Tests.ObligationProgramTestUtils

/-! # Guard propagation on examples

`guardProp` on obligation programs: an assumption `g` or `ite(g, false, true)` makes `g` a fact
of the statements after it on its path, so a later condition reads `true` or `false` for `g`
and the selected arm of a merge guarded by `g`; inside `ite(g, A, B)` the arm `A` reads `g` as
`true` and `B` as `false`, also below operators; every statement is kept, a marker assumption
whose condition becomes `false` included; the facts of one arm of an `ite *` are unknown in the
other arm and after it; definitions are not rewritten, and a merge is replaced only by a
variable or literal arm.
The WP pipeline runs the phase in its rewrite loop (`wpLoop`), and on the mutual-summary
example its query holds the guarded applications with the branch's arguments that the
quantifier's trigger matches. -/

namespace GuardPropTest

open Core Lambda Imperative Imperative.GuardProp ObligationProgramTestUtils

def bv (n : String) : Expression.Expr := .fvar Core.valueLoc (id' n) (some .bool)
def ite (c t f : Expression.Expr) : Expression.Expr := .ite Core.valueLoc c t f
def initT (x : String) (ty : LMonoTy) (e : Expression.Expr) : Statement :=
  .cmd (.cmd (.init (id' x) (.forAll [] ty) (.det e) md))
def havocT (x : String) (ty : LMonoTy) : Statement :=
  .cmd (.cmd (.init (id' x) (.forAll [] ty) .nondet md))
def assume' (l : String) (e : Expression.Expr) : Statement := .cmd (.cmd (.assume l e md))

/-- The printed list after guard propagation. -/
def gp (ss : Statements) : String := toString (Std.format (guardProp ss))

/-! ## A reach assumption

After `assume [wp$reach]: g`, the merge `x@5 := ite(g, x@4, x@1)` reads `x@4`, and `g` reads
`true` in the conditions; the definition is unchanged. -/

#guard gp [havocT "g" .bool, havocT "x@4" .int, havocT "x@1" .int,
    initT "x@5" .int (ite (bv "g") (iv "x@4") (iv "x@1")),
    assume' "wp$reach" (bv "g"),
    assume' "h" (ite (bv "g") (gt (iv "x@4") (int 0)) Core.true),
    assert' "a" (gt (iv "x@5") (int 0))] == lines [
    "{",
    "  var g : bool;",
    "  var x@4 : int;",
    "  var x@1 : int;",
    "  var x@5 : int := if g then x@4 else x@1;",
    "  assume [wp$reach]: g;",
    "  assume [h]: if true then int.gt(x@4, 0) else true;",
    "  assert [a]: int.gt(x@4, 0);",
    "}"]

/-! ## A branch that ends in `assume false`, and a kept marker

`assume ite(c, false, true)` makes `c` false: the merge `s := ite(c, k, a)` reads `a` after it.
The marker assumption of the loop elimination, whose condition becomes `false`, is kept with its
label. -/

#guard gp [havocT "c" .bool, havocT "k" .int, havocT "a" .int,
    initT "s" .int (ite (bv "c") (iv "k") (iv "a")),
    assume' "branch" (ite (bv "c") Core.false Core.true),
    assume' "$__loopElimAssume_guard_loop_0" (bv "c"),
    assert' "p" (gt (iv "s") (int 0))] == lines [
    "{",
    "  var c : bool;",
    "  var k : int;",
    "  var a : int;",
    "  var s : int := if c then k else a;",
    "  assume [|branch|]: if c then false else true;",
    "  assume [$__loopElimAssume_guard_loop_0]: false;",
    "  assert [p]: int.gt(a, 0);",
    "}"]

/-! ## A definition after a fact, and a fact about a non-Boolean variable

After `assume [wp$reach]: g`, the definition `d := m + ite(g, 1, 2)` is kept as it is, and the
assertion reads `d`; a fact about a variable of a type other than `bool` is not learned. -/

#guard gp [havocT "g" .bool, havocT "x" .int, havocT "y" .int,
    initT "m" .int (ite (bv "g") (iv "x") (iv "y")),
    assume' "wp$reach" (bv "g"),
    initT "d" .int (add (iv "m") (ite (bv "g") (int 1) (int 2))),
    assert' "a" (gt (iv "d") (int 0))] == lines [
    "{",
    "  var g : bool;",
    "  var x : int;",
    "  var y : int;",
    "  var m : int := if g then x else y;",
    "  assume [wp$reach]: g;",
    "  var d : int := int.add(m, if g then 1 else 2);",
    "  assert [a]: int.gt(d, 0);",
    "}"]

#guard gp [havocT "n" .int, havocT "x" .int, havocT "y" .int,
    initT "m" .int (ite (.fvar Core.valueLoc (id' "n") (some .int)) (iv "x") (iv "y")),
    assume' "r" (.fvar Core.valueLoc (id' "n") (some .int)),
    assert' "a" (gt (iv "m") (int 0))] == lines [
    "{",
    "  var n : int;",
    "  var x : int;",
    "  var y : int;",
    "  var m : int := if n then x else y;",
    "  assume [r]: n;",
    "  assert [a]: int.gt(m, 0);",
    "}"]

/-! ## Contextual simplification below operators

In the guarded assumption `ite(g, x + (ite(g, 1, y)) > 0, true)`, the inner conditional sits
below an operator of the `then` arm, where `g` reads `true`. -/

#guard gp [havocT "g" .bool, havocT "x" .int, havocT "y" .int,
    assume' "h" (ite (bv "g") (gt (add (iv "x") (ite (bv "g") (int 1) (iv "y"))) (int 0))
      Core.true),
    assert' "a" (gt (iv "x") (int 0))] == lines [
    "{",
    "  var g : bool;",
    "  var x : int;",
    "  var y : int;",
    "  assume [h]: if g then int.gt(int.add(x, if true then 1 else y), 0) else true;",
    "  assert [a]: int.gt(x, 0);",
    "}"]

/-! ## Scoping

A fact of the `then` arm of an `ite *` is unknown in the `else` arm and after the `ite *`. -/

#guard gp [havocT "g" .bool, havocT "x" .int, havocT "y" .int,
    initT "m" .int (ite (bv "g") (iv "x") (iv "y")),
    ndIte [assume' "r" (bv "g"), assert' "t" (gt (iv "m") (int 0))]
      [assert' "e" (gt (iv "m") (int 0))],
    assert' "after" (gt (iv "m") (int 0))] == lines [
    "{",
    "  var g : bool;",
    "  var x : int;",
    "  var y : int;",
    "  var m : int := if g then x else y;",
    "  if * {",
    "    assume [r]: g;",
    "    assert [t]: int.gt(x, 0);",
    "  }",
    "  else {",
    "    assert [e]: int.gt(m, 0);",
    "  }",
    "  assert [after]: int.gt(m, 0);",
    "}"]

/-! ## The phase in the WP pipeline

`--vcgen wp` runs guard propagation as a pass of the rewrite loop (`wpLoop`), which follows the
SSA phase; beta reduction follows the loop, and lambda lifting ends the order. -/

/-- info: true -/
#guard_msgs in
#eval do
  let opts : Core.VerifyOptions := { Core.VerifyOptions.quiet with vcgen := .wp }
  let names := (Strata.Core.corePipelinePhases opts).map Strata.Core.phaseName
  IO.println (names.dropWhile (· != "ssa") == ["ssa", "wpLoop", "betaReduce", "lambdaLift"])

/-! ## The mutual-summary example

`MS_check` of `Examples/DDMTransform.lean` assumes `Foo1_token` and `Foo2_token` under the guards
of their branches, with the arguments merged over those guards.  After guard propagation each
guarded application reads its branch's arguments, the ground terms the trigger of the
precondition's quantifier needs. -/

def msPgm : StrataDDM.Program :=
#strata
program Core;

function MS(x1: int, x2: int, g1: int, g2: int, g1': int, g2': int, r1: int, r2: int) : bool
{
    ((x1 == x2) && int.ge(x1, 0) && int.le(g1, g2)) ==> int.le(g1', g2')
}

function Foo1_token(x1: int, g1: int, g1': int, r1: int) : bool;
function Foo2_token(x2: int, g2: int, g2': int, r2: int) : bool;

procedure Foo1(x1: int, g: int, out r1: int, out g': int)
  spec {
    free ensures Foo1_token(x1,g,g',r1);
  };

procedure Foo2(x2: int, g: int, out r2: int, out g': int)
  spec {
    free ensures Foo2_token(x2,g,g',r2);
  };

procedure MS_check (x1: int, x2: int, g: int, out r1: int, out r2: int, out g': int)
  spec {

  requires (forall x1: int, x2: int, g1: int, g2: int, g1': int, g2': int, r1: int, r2: int ::
    {Foo1_token(x1,g1,g1',r1), Foo2_token(x2,g2,g2',r2)}
    Foo1_token(x1, g1, g1', r1) && Foo2_token(x2, g2, g2', r2) ==>
      MS(x1, x2, g1, g2, g1', g2', r1, r2));

  }
{
  var g1: int; var g1': int; var g2: int; var g2': int;
  var g_cur: int;

  g_cur := g;
  g1 := g_cur;

  if (int.lt(x1, 100)) {
    g_cur := int.add(g_cur, x1);
    call Foo1(int.add(x1, 1), g_cur, out r1, out g_cur);
  }
  g1' := g_cur;

  havoc g_cur;
  g2 := g_cur;

  if (int.lt(x2, 100)) {
    g_cur := int.add(g_cur, int.mul(2, x2));
    call Foo2(int.add(x2, 1), g_cur, out r2, out g_cur);
  }
  g2' := g_cur;

  g' := g_cur;

  assert MS(x1, x2, g1, g2, g1', g2', r1, r2);
};
#end

/-- The SMT queries written for `pgm` under `--vcgen wp`, concatenated. -/
def queries (pgm : StrataDDM.Program) : IO String :=
  wpQueries pgm "_test_vcs_guard_prop"

/-- info: true -/
#guard_msgs in
#eval do
  let q ← queries msPgm
  let lines := q.splitOn "\n"
  IO.println (decide (
    lines.contains "(assert (ite g@11 (Foo1_token (+ x1@0 1) (+ g@2 x1@0) g_cur@24 r1@22) true))" ∧
    lines.contains
      "(assert (ite g@27 (Foo2_token (+ x2@1 1) (+ g_cur@26 (* 2 x2@1)) g_cur@39 r2@37) true))"))

end GuardPropTest
