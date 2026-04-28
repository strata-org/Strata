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
public import Strata.DDM.Util.SourceRange

namespace Core
open Std (ToFormat Format format)
---------------------------------------------------------------------

public section

@[expose] abbrev ExpressionMetadata := Strata.SourceRange

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

-- Inhabited default; no meaningful source location
instance : Inhabited Expression.Expr where
  default := .intConst Strata.SourceRange.none 0

/-- Build an `LExpr.op` node from a structured `CoreOp`.
    `CoreOp` values are language-level operators with no source location. -/
def coreOpExpr (op : CoreOp) (ty : Option Lambda.LMonoTy := none) : Expression.Expr :=
  .op Strata.SourceRange.none op.toString ty

---------------------------------------------------------------------

end

end Core
