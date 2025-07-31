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

abbrev Expression : Imperative.PureExpr :=
   { Ident := BoogieIdent,
     Expr := Lambda.LExpr BoogieIdent,
     Ty := Lambda.LTy,
     TyEnv := @Lambda.TEnv BoogieIdent,
     EvalEnv := Lambda.LState BoogieIdent
     EqIdent := instDecidableEqBoogieIdent }

instance : Imperative.HasVarsPure Expression Expression.Expr where
  getVars := Lambda.LExpr.LExpr.getVars

---------------------------------------------------------------------

end Boogie
