/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.DL.Lambda.LExprEval
import Strata.DL.Lambda.LExprType
import Strata.DL.Lambda.LExpr

namespace Lambda

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

variable {T: LExprParams} [ToString T.Identifier] [DecidableEq T.Identifier] [ToFormat T.Identifier] [HasGen T] [ToFormat (LFunc T)] [Inhabited (LExpr T.mono)] [BEq T.Metadata] [Traceable LExpr.EvalProvenance T.Metadata]

/--
Top-level type checking and partial evaluation function for the Lambda
dialect.
-/
def typeCheckAndPartialEval
  (f : Factory (T:=T) := Factory.default)
  (e : (LExpr T.mono)) :
  Except Std.Format (LExpr T.mono) := do
  let Env := TEnv.default.addFactoryFunctions f
  let (et, _Env) ← LExpr.annotate Env e
  dbg_trace f!"Annotated expression:{Format.line}{et}{Format.line}"
  let σ ← (LState.init).addFactory f
  return (LExpr.eval σ.config.fuel σ et)

end Lambda

---------------------------------------------------------------------
