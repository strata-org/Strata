/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.DL.Imperative.PureExpr

namespace Imperative

public section

/-! # Pure Expression Variable Lookup : HasVarsPure -/

class HasVarsPure (P : PureExpr) (α : Type) where
  getVars : α → List P.Ident

/-! # Imperative Variable Lookup : HasVarsImp -/

class HasVarsImp (P : PureExpr) (α : Type) where
  definedVars : α → List P.Ident
  modifiedVars : α → List P.Ident
  modifiedOrDefinedVars : α → List P.Ident
          := λ e ↦ definedVars e ++ modifiedVars e

---------------------------------------------------------------------

/-! # Procedure Aware Variable Lookup : HasVarsTrans -/

/--
  Extends HasVarsImp, but transitively look up on the procedures
  `modifiedVarsTrans` differs from `modifiedVars` by taking a procedure lookup function
  Note: This is still not fully transitive, in the sense that if the procedure body contains call statement,
  the procedures associated with those call statements won't be looked up.
  The problem with fully transitive lookup is that it does not guarantee termination.
  E.g. mutually recursive procedure calls
-/
class HasVarsTrans
  (P : PureExpr) (α : Type) (PT : Type)
  where
  definedVarsTrans : (String → Option PT) → α → List P.Ident
  modifiedVarsTrans : (String → Option PT) → α → List P.Ident
  getVarsTrans : (String → Option PT) → α → List P.Ident
  modifiedOrDefinedVarsTrans : (String → Option PT) → α → List P.Ident
  allVarsTrans : (String → Option PT) → α → List P.Ident
  := λ π a ↦ modifiedVarsTrans π a ++ getVarsTrans π a

@[expose] abbrev HasVarsProcTrans (P : PureExpr) (PT : Type) := HasVarsTrans P PT PT

---------------------------------------------------------------------

/-! # Lawful Typeclasses

These typeclasses bundle the algebraic laws that the various `Has*` typeclasses
on `PureExpr` are expected to satisfy with respect to free-variable computation.
They allow downstream proofs (e.g., the `stmtsToCFG` correctness proof) to
consume the laws as instance arguments rather than as explicit hypotheses.
-/

/-- Lawfulness of `HasFvar`: the round-trip `getFvar (mkFvar x) = some x`,
    and the variable list of an `mkFvar x` expression is a subset of `[x]`. -/
class LawfulHasFvar (P : PureExpr) [HasFvar P] [HasVarsPure P P.Expr] where
  getFvar_mkFvar : ∀ x : P.Ident,
    HasFvar.getFvar (HasFvar.mkFvar (P := P) x) = some x
  mkFvar_getVars : ∀ x : P.Ident,
    HasVarsPure.getVars (HasFvar.mkFvar (P := P) x) ⊆ [x]

/-- Lawfulness of `HasBool`: `tt` has no free variables. -/
class LawfulHasBool (P : PureExpr) [HasBool P] [HasVarsPure P P.Expr] where
  tt_getVars : HasVarsPure.getVars (P := P) (HasBool.tt : P.Expr) = []

/-- Lawfulness of `HasIdent`: the canonical identifier-injection is injective. -/
class LawfulHasIdent (P : PureExpr) [HasIdent P] where
  ident_inj : Function.Injective (HasIdent.ident (P := P))

/-- Lawfulness of `HasIntOrder`: variable lists of compound integer-order
    expressions are bounded above by their argument variable lists, and the
    canonical `zero` constant has no free variables. -/
class LawfulHasIntOrder (P : PureExpr) [HasIntOrder P] [HasVarsPure P P.Expr] where
  eq_getVars : ∀ a b : P.Expr,
    HasVarsPure.getVars (P := P) (HasIntOrder.eq a b)
      ⊆ HasVarsPure.getVars (P := P) a ++ HasVarsPure.getVars (P := P) b
  lt_getVars : ∀ a b : P.Expr,
    HasVarsPure.getVars (P := P) (HasIntOrder.lt a b)
      ⊆ HasVarsPure.getVars (P := P) a ++ HasVarsPure.getVars (P := P) b
  zero_getVars : HasVarsPure.getVars (P := P) (HasIntOrder.zero : P.Expr) = []

/-- Lawfulness of `HasNot`: the variable list of a negation is bounded above
    by the variable list of its argument. -/
class LawfulHasNot (P : PureExpr) [HasNot P] [HasVarsPure P P.Expr] where
  not_getVars : ∀ a : P.Expr,
    HasVarsPure.getVars (P := P) (HasNot.not a) ⊆ HasVarsPure.getVars (P := P) a

end -- public section
end Imperative
