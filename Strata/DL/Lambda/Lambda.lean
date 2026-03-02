/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.DL.Lambda.LExprEval
import Strata.DL.Lambda.LExprType
import Strata.DL.Lambda.LExpr
import Strata.DL.Lambda.Semantics
import Strata.DL.Lambda.TypeFactory
import Strata.DL.Lambda.Reflect

namespace Lambda
open Strata
open Std (ToFormat Format format)

/-! # Lambda Dialect

The Lambda dialect provides an implementation of simply-typed lambda
calculus, along with a Hindley-Milner type system. It also comes with an
extensible partial evaluator that is parameterized by an (optional) map from
operator names to their specific evaluations. This allows adding evaluation
support for new operators without changing the core logic or extending the AST.

See module `Strata.DL.Lambda.LExpr` for the formalization of expressions,
`Strata.DL.Lambda.LTy` for the formalization of mono- and poly-types,
`Strata.DL.Lambda.LExprT` for the type inference implementation, and
`Strata.DL.Lambda.LExprEval` for the partial evaluator.
-/

variable {T: LExprParams} [ToString T.IDMeta] [DecidableEq T.IDMeta] [ToFormat T.IDMeta] [HasGen T.IDMeta] [ToFormat (LFunc T)] [Inhabited (LExpr T.mono)] [BEq T.Metadata] [Traceable LExpr.EvalProvenance T.Metadata]

/--
Top-level type checking and partial evaluation function for the Lambda
dialect.
-/
def typeCheckAndPartialEval
  [Inhabited T.Metadata]
  [Inhabited T.IDMeta]
  (t: TypeFactory (IDMeta:=T.IDMeta) := TypeFactory.default)
  (f : Factory (T:=T) := Factory.default)
  (e : LExpr T.mono) :
  Except DiagnosticModel (LExpr T.mono) := do
  let E := TEnv.default
  let C := LContext.default.addFactoryFunctions f
  let C ← C.addTypeFactory t
  let (et, _T) ← LExpr.annotate C E e |>.mapError DiagnosticModel.fromFormat
  dbg_trace f!"Annotated expression:{Format.line}{et}{Format.line}"
  let σ ← (LState.init).addFactory C.functions
  return (LExpr.eval σ.config.fuel σ et)

end Lambda

---------------------------------------------------------------------
