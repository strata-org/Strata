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
     Expr := Lambda.LExpr ⟨⟨ExpressionMetadata, BoogieIdent⟩, Lambda.LMonoTy⟩,
     Ty := Lambda.LTy,
     TyEnv := @Lambda.TEnv ⟨ExpressionMetadata, BoogieIdent⟩,
     EvalEnv := Lambda.LState ⟨ExpressionMetadata, BoogieIdent⟩
     EqIdent := instDecidableEqBoogieIdent }

instance : Imperative.HasVarsPure Expression Expression.Expr where
  getVars := Lambda.LExpr.LExpr.getVars

---------------------------------------------------------------------

end Boogie
