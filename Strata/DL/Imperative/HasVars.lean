/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.DL.Imperative.PureExpr

namespace Imperative

/-! # Pure Expression Variable Lookup : HasVarsPure -/

class HasVarsPure (P : PureExpr) (α : Type) where
  getVars : α → List P.Ident

/-! # Imperative Variable Lookup : HasVarsImp -/

class HasVarsImp (P : PureExpr) (α : Type) where
  definedVars : α → List P.Ident
  modifiedVars : α → List P.Ident
  touchedVars : α → List P.Ident
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
  touchedVarsTrans : (String → Option PT) → α → List P.Ident
  allVarsTrans : (String → Option PT) → α → List P.Ident
  := λ π a ↦ modifiedVarsTrans π a ++ getVarsTrans π a

abbrev HasVarsProcTrans (P : PureExpr) (PT : Type) := HasVarsTrans P PT PT

end Imperative
