/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/



import Strata.DL.Lambda.Lambda
import Strata.DL.Imperative.PureExpr
import Strata.Languages.Boogie.Identifiers
import Strata.DL.Imperative.HasVars

namespace Boogie
open Std (ToFormat Format format)
---------------------------------------------------------------------

def ExpressionMetadata := Unit

abbrev Expression : Imperative.PureExpr :=
   { Ident := BoogieIdent,
     EqIdent := inferInstanceAs (DecidableEq (Lambda.Identifier _))
     Expr := Lambda.LExpr ⟨⟨ExpressionMetadata, Visibility⟩, Lambda.LMonoTy⟩,
     Ty := Lambda.LTy,
     TyEnv := @Lambda.TEnv Visibility,
     TyContext := @Lambda.LContext ⟨ExpressionMetadata, Visibility⟩,
     EvalEnv := Lambda.LState ⟨ExpressionMetadata, Visibility⟩ }

instance : Imperative.HasVarsPure Expression Expression.Expr where
  getVars := Lambda.LExpr.LExpr.getVars

instance : Inhabited Expression.Expr where
  default := .intConst () 0

---------------------------------------------------------------------

end Boogie
