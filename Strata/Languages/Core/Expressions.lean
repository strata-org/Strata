/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/



import Strata.DL.Lambda.Lambda
import Strata.DL.Imperative.PureExpr
import Strata.Languages.Core.Identifiers
import Strata.DL.Imperative.HasVars
import Strata.DDM.Util.SourceRange

namespace Core
open Std (ToFormat Format format)
---------------------------------------------------------------------

def ExpressionMetadata := Strata.SourceRange

abbrev Expression : Imperative.PureExpr :=
   { Ident := CoreIdent,
     EqIdent := inferInstanceAs (DecidableEq (Lambda.Identifier _))
     Expr := Lambda.LExpr ⟨⟨ExpressionMetadata, Visibility⟩, Lambda.LMonoTy⟩,
     Ty := Lambda.LTy,
     ExprMetadata := ExpressionMetadata,
     TyEnv := @Lambda.TEnv Visibility,
     TyContext := @Lambda.LContext ⟨ExpressionMetadata, Visibility⟩,
     EvalEnv := Lambda.LState ⟨ExpressionMetadata, Visibility⟩ }

instance : Imperative.HasVarsPure Expression Expression.Expr where
  getVars := Lambda.LExpr.LExpr.getVars

instance : Inhabited Expression.Expr where
  default := .intConst Strata.SourceRange.none 0

---------------------------------------------------------------------

end Core
