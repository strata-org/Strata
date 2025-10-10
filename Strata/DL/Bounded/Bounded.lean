/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.DL.Lambda.LExprEval
-- import Strata.DL.Lambda.LExprType
import Strata.DL.Bounded.BExpr

namespace Bounded

open Std (ToFormat Format format)
open Lambda

/-! # Bounded Dialect

The Bounded dialect is an extension of Lambda (see `Strata.DL.Lambda`) with support for bounded integer types. See `Stata.DL.Bounded.BExpr` for the translation from Bounded to Lambda.
-/

variable {Identifier : Type} [ToString Identifier] [DecidableEq Identifier] [ToFormat Identifier] [HasGen Identifier] [Coe String Identifier]

/--
Top-level type checking and partial evaluation function for the Lambda
dialect.
-/
def typeCheckAndPartialEval
  (f : Factory (Identifier:=Identifier) (ExtraRestrict:=BoundTyRestrict) := Factory.default)
  (e : (LExpr (LMonoTy BoundTyRestrict) Identifier)) :
  Except Std.Format (List (LExpr LMonoTy Identifier)) := do
  let T := TEnv.default.addFactoryFunctions f
  let (et, T1) ← LExprT.fromLExpr T e
  -- dbg_trace f!"Annotated expression:{Format.line}{et}{Format.line}"
  -- TODO: transform factory
  let σ ← (LState.init).addFactory f
  -- Need to transform environment into non-bounded one
  -- Translate and give well-foundness conditions
  let res ← translateAndWfBounded T1 et;
  List.mapM (fun x => pure (LExpr.eval σ.config.fuel σ (LExprT.toLExpr x))) (res.1 :: res.2.1)

end Bounded

---------------------------------------------------------------------
