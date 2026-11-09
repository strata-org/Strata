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

/-! # Typed variable lookup over commands : HasTypedVarsImp

`HasTypedVarsImp` gives the type annotations a command carries, for the free-variable
annotation check (`Stmt.fvarTypesWellAnnotated`).  Only command types implement it, and it has
no default, so a construct without an instance cannot be checked rather than passing
trivially. -/

class HasTypedVarsImp (P : PureExpr) (α : Type) where
  /-- The annotated free-variable reads of the construct, with their annotations
    (`HasFvars.getTypedFvars` of the expressions it contains). -/
  typedReadVars : α → List (P.Ident × P.Ty)
  /-- The variables the construct defines in its own scope, with their declared types. -/
  typedDefinedVars : α → List (P.Ident × P.Ty)

/-! # Operator/Function Name Lookup over Commands : HasOpsImp

`HasOpsImp` collects the operator (function) names referenced by a command,
parallel to `HasOps` for expressions. -/

class HasOpsImp (P : PureExpr) (α : Type) where
  getOps : α → List P.Ident

/-! # Init-Type Lookup over Commands : HasInitTypesImp

`HasInitTypesImp` collects the declared types of the variable-initialization
(`init`) commands a construct contains, parallel to `HasVarsImp` for the
variables themselves. -/

class HasInitTypesImp (P : PureExpr) (α : Type) where
  /-- The declared types of the `init` commands contained in the construct. -/
  initTypes : α → List P.Ty

end -- public section
end Imperative
