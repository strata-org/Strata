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
  definedVars :
    α →
    Bool/-If true, the returned List P.Ident excludes vars not visible from outside.
      For example, if the first argument (whose type is α) is:
      ```
      var x := 1;
      {
        var y := 2;
      }
      ```
      and this flag is true, definedVars will only return 'x'.
      (example: Stmt.definedVars) -/ →
    List P.Ident
  modifiedVars : α → List P.Ident

/-! # Operator/Function Name Lookup over Commands : HasOpsImp

`HasOpsImp` collects the operator (function) names referenced by a command,
parallel to `HasOps` for expressions. -/

class HasOpsImp (P : PureExpr) (α : Type) where
  getOps : α → List P.Ident

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
class LawfulHasFvar (P : PureExpr) [HasFvar P] [HasFvars P] where
  getFvar_mkFvar : ∀ x : P.Ident,
    HasFvar.getFvar (HasFvar.mkFvar (P := P) x) = some x
  mkFvar_getVars : ∀ x : P.Ident,
    HasFvars.getFvars (HasFvar.mkFvar (P := P) x) ⊆ [x]

/-- Lawfulness of `HasBool`: `tt` has no free variables. -/
class LawfulHasBool (P : PureExpr) [HasBool P] [HasFvars P] where
  tt_getVars : HasFvars.getFvars (P := P) (HasBool.tt : P.Expr) = []

/-- Lawfulness of `HasIdent`: the canonical identifier-injection is injective. -/
class LawfulHasIdent (P : PureExpr) [HasIdent P] where
  ident_inj : Function.Injective (HasIdent.ident (P := P))

/-- Lawfulness of `HasInt`/`HasIntOps`: variable lists of compound integer-order
    expressions are bounded above by their argument variable lists, and the
    canonical `zero` constant has no free variables. -/
class LawfulHasIntOrder (P : PureExpr)
    [HasBool P] [HasFvars P] [HasInt P] [HasIntOps P] where
  eq_getVars : ∀ a b : P.Expr,
    HasFvars.getFvars (P := P) (HasIntOps.eq a b)
      ⊆ HasFvars.getFvars (P := P) a ++ HasFvars.getFvars (P := P) b
  lt_getVars : ∀ a b : P.Expr,
    HasFvars.getFvars (P := P) (HasIntOps.lt a b)
      ⊆ HasFvars.getFvars (P := P) a ++ HasFvars.getFvars (P := P) b
  zero_getVars : HasFvars.getFvars (P := P) (HasInt.zero : P.Expr) = []

/-- Lawfulness of `HasBoolOps.not`: the variable list of a negation is bounded
    above by the variable list of its argument. -/
class LawfulHasNot (P : PureExpr) [HasBoolOps P] [HasFvars P] where
  not_getVars : ∀ a : P.Expr,
    HasFvars.getFvars (P := P) (HasBoolOps.not a) ⊆ HasFvars.getFvars (P := P) a

end -- public section
end Imperative
