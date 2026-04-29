/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.DL.Lambda.Lambda
public import Strata.DL.Imperative.PureExpr
public import Strata.Languages.Core.Identifiers
public import Strata.Languages.Core.CoreOp
public import Strata.DL.Imperative.HasVars

namespace Core
open Std (ToFormat Format format)
---------------------------------------------------------------------

public section

@[expose] abbrev ExpressionMetadata := Unit

@[expose]
abbrev Expression : Imperative.PureExpr :=
   { Ident := CoreIdent,
     EqIdent := inferInstanceAs (DecidableEq (Lambda.Identifier Unit))
     Expr := Lambda.LExpr ⟨⟨ExpressionMetadata, Unit⟩, Lambda.LMonoTy⟩,
     Ty := Lambda.LTy,
     ExprMetadata := ExpressionMetadata,
     TyEnv := @Lambda.TEnv Unit,
     TyContext := @Lambda.LContext ⟨ExpressionMetadata, Unit⟩,
     EvalEnv := Lambda.LState ⟨ExpressionMetadata, Unit⟩ }

instance : Imperative.HasVarsPure Expression Expression.Expr where
  getVars := Lambda.LExpr.LExpr.getVars

instance : Inhabited Expression.Expr where
  default := .intConst () 0

/-- Build an `LExpr.op` node from a structured `CoreOp`. -/
def coreOpExpr (op : CoreOp) (ty : Option Lambda.LMonoTy := none) : Expression.Expr :=
  .op () op.toString ty

---------------------------------------------------------------------

end

end Core
