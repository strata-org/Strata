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

This dialect provides an implementation of simply-typed lambda
calculus (see `LExpr`), along with a Hindley-Milner type system (see
`LTy`). It also comes with an extensible partial evaluator that is
parameterized by an (optional) map from operator names to their
specific evaluations. This allows adding evaluation support for new
operators without changing the core logic or extending the AST.  -/

variable {Identifier : Type} [ToString Identifier] [DecidableEq Identifier] [ToFormat Identifier] [HasGen Identifier]

/--
Top-level type checking and partial evaluation function for the Lambda
dialect.
-/
def typeCheckAndPartialEval
  (f : Factory (Identifier:=Identifier) := Factory.default)
  (e : (LExpr Identifier)) :
  Except Std.Format (LExpr Identifier) := do
  let T := TEnv.default.addFactoryFunctions f
  let (et, _T) ← LExpr.annotate T e
  dbg_trace f!"Annotated expression:{Format.line}{et}{Format.line}"
  let σ ← (LState.init).addFactory f
  return (LExpr.eval σ.config.fuel σ et)

end Lambda

---------------------------------------------------------------------
