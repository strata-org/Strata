/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.DL.Imperative.PureExpr

namespace Imperative

public section

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
  /-- Free variables read by the construct, i.e. the variables referenced in
    the expressions it contains. -/
  readVars : α → List P.Ident

/-! # Operator/Function Name Lookup over Commands : HasOpsImp

`HasOpsImp` collects the operator (function) names referenced by a command,
parallel to `HasOps` for expressions. -/

class HasOpsImp (P : PureExpr) (α : Type) where
  getOps : α → List P.Ident

end -- public section
end Imperative
