/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/



import Strata.DL.Util.MetaData
import Strata.DL.Lambda.Lambda
import Strata.DL.Imperative.PureExpr
import Strata.Languages.Boogie.Identifiers
import Strata.DL.Imperative.HasVars

namespace Boogie
open Std (ToFormat Format format)
---------------------------------------------------------------------

abbrev BoogieLParamsT : Lambda.LExprParamsT := ⟨BoogieLParams, Lambda.LMonoTy⟩

abbrev Expression : Imperative.PureExpr :=
   { Ident := BoogieIdent,
     Expr := Lambda.LExpr BoogieLParamsT,
     Ty := Lambda.LTy,
     TyEnv := @Lambda.TEnv Visibility,
     TyContext := @Lambda.LContext ⟨BoogieExprMetadata, Visibility⟩,
     EvalEnv := Lambda.LState ⟨BoogieExprMetadata, Visibility⟩
     EqIdent := inferInstanceAs (DecidableEq (Lambda.Identifier _)) }

instance : Imperative.HasVarsPure Expression Expression.Expr where
  getVars := Lambda.LExpr.LExpr.getVars

instance : Inhabited Expression.Expr where
  default := .intConst .empty 0

---------------------------------------------------------------------

end Boogie
