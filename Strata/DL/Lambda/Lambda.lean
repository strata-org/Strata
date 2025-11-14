/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.DL.Lambda.LExprEval
import Strata.DL.Lambda.LExprType
import Strata.DL.Lambda.LExpr
import Strata.DL.Lambda.TypeFactory
import Strata.DL.Lambda.Reflect

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

variable {IDMeta : Type} [ToString IDMeta] [DecidableEq IDMeta] [HasGen IDMeta] [Inhabited IDMeta]
/--
Top-level type checking and partial evaluation function for the Lambda
dialect.
-/
def typeCheckAndPartialEval
  (t: TypeFactory (IDMeta:=IDMeta) := TypeFactory.default)
  (f : Factory (IDMeta:=IDMeta) := Factory.default)
  (e : (LExpr LMonoTy IDMeta)) :
  Except Std.Format (LExpr LMonoTy IDMeta) := do
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
