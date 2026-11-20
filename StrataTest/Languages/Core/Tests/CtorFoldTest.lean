/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
import Strata.Transform.CtorFold
import Strata.Languages.Core
import Strata.MetaVerifier
import StrataTest.Languages.Core.Tests.ObligationProgramTestUtils

/-! # The constructor fold on examples

`Core.DefInline.iteLit` on its own: a conditional whose condition is a Boolean literal becomes
the arm the literal selects when both arms are self-typed at one type, and is left alone when an
arm is not, since a conditional has a value only when both arms have one.

`Core.CtorFold.ctorFold` on obligation programs: a chain of conditionals over the testers of a
name whose `init` gives it a constructor application collapses to the arm the constructor
selects, the arms the chain does not take are discarded with the functions only they named, and
the `init`, left unread, is erased.  A name none of whose reads fold is left alone, with its
`init`.  The selector of the taken arm need not fold — what the phase is for is discarding the
other arms, not reaching a literal. -/

namespace CtorFoldTest

open Core Lambda Imperative Core.CtorFold Core.DefInline ObligationProgramTestUtils

/-! ## A datatype to fold over

`Opt` with `None` and `Some (val : int)`, whose generated functions give the testers `isNone`
and `isSome` and the destructor `val`. -/

def optT : LMonoTy := .tcons "Opt" []
def optD : LDatatype Unit :=
  { name := "Opt", typeArgs := [], constrs_ne := rfl,
    constrs := [{ name := ⟨"None", ()⟩, args := [] },
      { name := ⟨"Some", ()⟩, args := [(⟨"val", ()⟩, .int)] }] }

/-- `Core.Factory` extended by the functions generated for `Opt`, as `Core.wpFactory` extends it
    for the datatypes a program declares. -/
def fac : Lambda.Factory CoreLParams :=
  (do
    let f ← Core.Factory.addFactory Lambda.Factory.default
    f.addFactory (← Lambda.genBlockFactory (T := CoreLParams) [optD])).toOption.getD default

def arr (a b : LMonoTy) : LMonoTy := .tcons "arrow" [a, b]
def opE (n : String) (ty : LMonoTy) : Expression.Expr := .op valueLoc (id' n) (some ty)
/-- `Some a`. -/
def some' (a : Expression.Expr) : Expression.Expr := .app valueLoc (opE "Some" (arr .int optT)) a
/-- The tester `n` applied to `a`. -/
def test (n : String) (a : Expression.Expr) : Expression.Expr :=
  .app valueLoc (opE n (arr optT .bool)) a
/-- The total destructor of `Some`, `Opt..val!`, applied to `a`. -/
def val' (a : Expression.Expr) : Expression.Expr :=
  .app valueLoc (opE "Opt..val!" (arr optT .int)) a
def ov (n : String) : Expression.Expr := .fvar valueLoc (id' n) (some optT)
def initO (x : String) (e : Expression.Expr) : Statement :=
  .cmd (.cmd (.init (id' x) (.forAll [] optT) (.det e) md))
def ite (c t f : Expression.Expr) : Expression.Expr := .ite valueLoc c t f

/-- The printed list after the constructor fold at `fac`. -/
def cf (ss : Statements) : String := toString (Std.format (ctorFold fac ss))

/-! ## `iteLit` on its own

A literal condition with both arms self-typed at `bool` selects the arm; the arms need not be
literals, only self-typed. -/

#guard iteLit (ite Core.true Core.false Core.true) == Core.false
#guard iteLit (ite Core.false Core.false Core.true) == Core.true
#guard iteLit (ite Core.true (gt (iv "x") (int 0)) Core.true) == gt (iv "x") (int 0)

/-! Left alone: an arm that is not self-typed, here a variable with no type annotation, may
    have no value, so dropping the other arm would give the conditional one where it has
    none. -/
#guard iteLit (ite Core.true (.fvar valueLoc (id' "u") none) Core.true)
  == ite Core.true (.fvar valueLoc (id' "u") none) Core.true

/-! Left alone: a condition that is not a Boolean literal. -/
#guard iteLit (ite (.fvar valueLoc (id' "c") (some .bool)) Core.false Core.true)
  == ite (.fvar valueLoc (id' "c") (some .bool)) Core.false Core.true

/-! ## A tester chain over a constructor application

`y := Some 2` is read by two testers and the condition is a chain over them.  Each tester folds
to its literal, `iteLit` then collapses the chain, and the `init` of `y`, left unread, is
erased: the whole assertion becomes the literal the chain denotes. -/

#guard cf [initO "y" (some' (int 2)),
    assert' "a" (ite (test "isSome" (ov "y")) (test "isNone" (ov "y")) Core.true)]
  == lines ["{", "  assert [a]: false;", "}"]

/-! The other order: `isNone(Some 2)` is `false`, so the chain takes its second arm, which is
    `isSome(Some 2)`, that is `true`. -/
#guard cf [initO "y" (some' (int 2)),
    assert' "a" (ite (test "isNone" (ov "y")) Core.false (test "isSome" (ov "y")))]
  == lines ["{", "  assert [a]: true;", "}"]

/-! The selector of the arm the chain selects is kept, folded or not: here `Opt..val!` has no
fold, and what the phase achieves is that the `init` of `y` and the arm the chain does not take
are gone, leaving the selector applied to the constructor. -/
#guard ctorFold fac [initO "y" (some' (int 2)),
    assert' "a" (ite (test "isSome" (ov "y")) (val' (ov "y")) (int 0))]
  == [assert' "a" (val' (some' (int 2)))]

/-! ## Names and reads the fold leaves alone

A name read only where no application folds it is not selected, so its right-hand side is never
copied; the normalization still rewrites the conditions, as it does under every selection.  Here
`y` is read only by an equality, which `DefInline.bodyFold` does not fold, so `y` is not
selected, and it is the equality's own rewrite (`decEq`: `y == y` is `true`) that leaves the
`init` of `y` unread for the erasure to drop.  These are compared as statement lists rather than
as printed text, because the printer does not know the test's datatype. -/

#guard ctorFold fac [initO "y" (some' (int 2)), assert' "a" (.eq valueLoc (ov "y") (ov "y"))]
  == [assert' "a" Core.true]

/-! A name with no `init` right-hand side is never a candidate. -/
#guard ctorFold fac [.cmd (.cmd (.init (id' "y") (.forAll [] optT) .nondet md)),
    assert' "a" (test "isSome" (ov "y"))]
  == [.cmd (.cmd (.init (id' "y") (.forAll [] optT) .nondet md)),
      assert' "a" (test "isSome" (ov "y"))]

end CtorFoldTest
