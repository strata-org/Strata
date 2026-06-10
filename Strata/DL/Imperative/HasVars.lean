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
      For example, if α is:
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

end -- public section
end Imperative
