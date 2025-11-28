/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Dialects.Lambda.LExprEval
import Strata.Dialects.Lambda.LExprType
import Strata.Dialects.Lambda.LExpr
import Strata.Dialects.Lambda.Semantics
import Strata.Dialects.Lambda.TypeFactory
import Strata.Dialects.Lambda.Reflect

namespace Lambda

open Std (ToFormat Format format)

/-! # Lambda Dialect

The Lambda dialect provides an implementation of simply-typed lambda
calculus, along with a Hindley-Milner type system. It also comes with an
extensible partial evaluator that is parameterized by an (optional) map from
operator names to their specific evaluations. This allows adding evaluation
support for new operators without changing the core logic or extending the AST.

See module `Strata.Dialects.Lambda.LExpr` for the formalization of expressions,
`Strata.Dialects.Lambda.LTy` for the formalization of mono- and poly-types,
`Strata.Dialects.Lambda.LExprT` for the type inference implementation, and
`Strata.Dialects.Lambda.LExprEval` for the partial evaluator.
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
  Except Std.Format (LExpr T.mono) := do
  let fTy ← t.genFactory
  let fAll ← Factory.addFactory fTy f
  let T := TEnv.default
  let C := LContext.default.addFactoryFunctions fAll
  let C ← C.addKnownTypes t.toKnownTypes
  let (et, _T) ← LExpr.annotate C T e
  dbg_trace f!"Annotated expression:{Format.line}{et}{Format.line}"
  let σ ← (LState.init).addFactory fAll
  return (LExpr.eval σ.config.fuel σ et)

end Lambda

---------------------------------------------------------------------
