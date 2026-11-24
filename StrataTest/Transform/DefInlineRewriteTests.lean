/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

meta import Strata.Transform.DefInlineRewrite
meta import Strata.Languages.Core.Factory

meta section

/-! # The normalization of the rewrite loop

Each rewrite of `Core.DefInline.rwAll` on the shapes of the goals the WP pipeline leaves to the
solver, the expressions it must leave unchanged, and the substituted expressions it does not
rewrite again. -/

namespace Core.DefInline.Tests

open Lambda

private def intT : LMonoTy := .tcons "int" []
private def boolT : LMonoTy := .tcons "bool" []
private def arr (a b : LMonoTy) : LMonoTy := .tcons "arrow" [a, b]
private def lit (n : Int) : Expression.Expr := .const Core.valueLoc (.intConst n)
private def bin (o : String) (a r : LMonoTy) (x y : Expression.Expr) : Expression.Expr :=
  .app Core.valueLoc (.app Core.valueLoc (.op Core.valueLoc ⟨o, ()⟩ (some (arr a (arr a r)))) x) y
private def x : Expression.Expr := .fvar Core.valueLoc ⟨"x@0", ()⟩ (some intT)
private def xBare : Expression.Expr := .fvar Core.valueLoc ⟨"x@0", ()⟩ none
private def c : Expression.Expr := .fvar Core.valueLoc ⟨"c@0", ()⟩ (some boolT)
private def cBare : Expression.Expr := .fvar Core.valueLoc ⟨"c@0", ()⟩ none
private def rw : Expression.Expr → Expression.Expr := rwAll Core.Factory fun _ => none

-- Decided equality of an annotated variable and of a typed operator application.
#guard rw (.eq Core.valueLoc x x) == Core.true
#guard rw (.eq Core.valueLoc (bin "Int.Add" intT intT x (lit 1)) (bin "Int.Add" intT intT x (lit 1)))
  == Core.true
-- Constant folding, below a connective and through an equality.
#guard rw (bin "Bool.And" boolT boolT (.eq Core.valueLoc (lit 5) (lit 5)) (.eq Core.valueLoc (lit 6) (lit 6)))
  == Core.true
#guard rw (.eq Core.valueLoc (bin "Int.Mul" intT intT (lit 5) (lit 2)) (lit 10)) == Core.true
#guard rw (.eq Core.valueLoc (lit 1) (lit 2)) == .const Core.valueLoc (.boolConst false)
-- An operator into a conditional of literals, whose arms then agree.
#guard rw (bin "Int.Ge" intT boolT (.ite Core.valueLoc c (lit 1) (lit 2)) (lit 0)) == Core.true
#guard rw (bin "Int.Ge" intT boolT (.ite Core.valueLoc c (lit 1) (lit (-2))) (lit 0))
  == .ite Core.valueLoc c (.const Core.valueLoc (.boolConst true)) (.const Core.valueLoc (.boolConst false))
-- Unchanged: a variable without annotation may have no value, nor a bare condition.
#guard rw (.eq Core.valueLoc xBare xBare) == .eq Core.valueLoc xBare xBare
#guard rw (bin "Int.Ge" intT boolT (.ite Core.valueLoc cBare (lit 1) (lit 2)) (lit 0))
  == .ite Core.valueLoc cBare (.const Core.valueLoc (.boolConst true)) (.const Core.valueLoc (.boolConst true))
-- Unchanged: an operator annotated with a type variable.
#guard rw (.eq Core.valueLoc (.op Core.valueLoc ⟨"f", ()⟩ (some (.ftvar "a"))) (.op Core.valueLoc ⟨"f", ()⟩ (some (.ftvar "a"))))
  == .eq Core.valueLoc (.op Core.valueLoc ⟨"f", ()⟩ (some (.ftvar "a"))) (.op Core.valueLoc ⟨"f", ()⟩ (some (.ftvar "a")))

-- Contraction of a redex with a self-typed argument, then decided equality.
private def lam (b : Expression.Expr) : Expression.Expr := .abs Core.valueLoc "x" (some intT) b
private def bv : Expression.Expr := .bvar Core.valueLoc 0
#guard rw (.app Core.valueLoc (lam (.eq Core.valueLoc bv (lit 5))) (lit 5)) == Core.true
#guard rw (.app Core.valueLoc (lam (.eq Core.valueLoc bv bv)) x) == Core.true
-- Unchanged: an argument that is not self-typed, and a compound argument for a bound variable
-- used twice.
#guard rw (.app Core.valueLoc (lam (.eq Core.valueLoc bv (lit 5))) xBare) == .app Core.valueLoc (lam (.eq Core.valueLoc bv (lit 5))) xBare
#guard rw (.app Core.valueLoc (lam (.eq Core.valueLoc bv bv)) (bin "Int.Add" intT intT x (lit 1)))
  == .app Core.valueLoc (lam (.eq Core.valueLoc bv bv)) (bin "Int.Add" intT intT x (lit 1))
#guard rw (.app Core.valueLoc (lam (bin "Int.Add" intT intT bv (lit 1))) (bin "Int.Add" intT intT x (lit 1)))
  == bin "Int.Add" intT intT (bin "Int.Add" intT intT x (lit 1)) (lit 1)

-- An expression the substitution puts in is not rewritten again; the other parts are.
private def y : Expression.Expr := .fvar Core.valueLoc ⟨"y@0", ()⟩ (some boolT)
private def g5 (z : Expression.Ident) : Option Expression.Expr :=
  if z.name = "y@0" then some (.eq Core.valueLoc (lit 5) (lit 5)) else none
#guard rwAll Core.Factory g5 y == .eq Core.valueLoc (lit 5) (lit 5)
#guard rwAll Core.Factory g5 (bin "Bool.And" boolT boolT y (.eq Core.valueLoc (lit 6) (lit 6)))
  == bin "Bool.And" boolT boolT (.eq Core.valueLoc (lit 5) (lit 5)) Core.true

-- A tester applied to a constructor application, under the functions of two datatypes: the
-- tested constructor folds to `true`, another constructor to `false`, also with a variable field.
private def optT : LMonoTy := .tcons "Opt" []
private def listT : LMonoTy := .tcons "IntList" []
private def optD : LDatatype Unit :=
  { name := "Opt", typeArgs := [], constrs_ne := rfl,
    constrs := [{ name := ⟨"None", ()⟩, args := [] },
      { name := ⟨"Some", ()⟩, args := [(⟨"val", ()⟩, intT)] }] }
private def listD : LDatatype Unit :=
  { name := "IntList", typeArgs := [], constrs_ne := rfl,
    constrs := [{ name := ⟨"Nil", ()⟩, args := [] },
      { name := ⟨"Cons", ()⟩, args := [(⟨"hd", ()⟩, intT), (⟨"tl", ()⟩, listT)] }] }
private def dtFac : Lambda.Factory CoreLParams :=
  ((genBlockFactory (T := CoreLParams) [optD]) >>= fun f =>
    genBlockFactory (T := CoreLParams) [listD] >>= f.addFactory).toOption.getD default
private def opE (n : String) (ty : LMonoTy) : Expression.Expr := .op Core.valueLoc ⟨n, ()⟩ (some ty)
private def some' (a : Expression.Expr) : Expression.Expr := .app Core.valueLoc (opE "Some" (arr intT optT)) a
private def test (n : String) (ty : LMonoTy) (a : Expression.Expr) : Expression.Expr :=
  .app Core.valueLoc (opE n (arr ty boolT)) a
private def rwD : Expression.Expr → Expression.Expr := rwAll dtFac fun _ => none
#guard rwD (test "isSome" optT (some' x)) == Core.true
#guard rwD (test "isNone" optT (some' (lit 2))) == .const Core.valueLoc (.boolConst false)
#guard rwD (test "isSome" optT (opE "None" optT)) == .const Core.valueLoc (.boolConst false)
#guard rwD (.eq Core.valueLoc (test "isNone" optT (opE "None" optT)) Core.true) == Core.true
-- Unchanged: a field without annotation may have no value; a constructor with a field of the
-- datatype itself, whose eliminator case receives the recursive call unannotated.
#guard rwD (test "isSome" optT (some' xBare)) == test "isSome" optT (some' xBare)
private def cons' : Expression.Expr :=
  .app Core.valueLoc (.app Core.valueLoc (opE "Cons" (arr intT (arr listT listT))) (lit 1)) (opE "Nil" listT)
#guard rwD (test "isCons" listT cons') == test "isCons" listT cons'

end Core.DefInline.Tests

end
