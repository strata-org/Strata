/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/



import Strata.Languages.Boogie.Function
import Strata.Languages.Boogie.Program

---------------------------------------------------------------------

namespace Boogie

namespace Function

open Lambda Imperative
open Std (ToFormat Format format)

def typeCheck (T : Boogie.Expression.TyEnv) (func : Function) :
  Except Format (Function × Boogie.Expression.TyEnv) := do
  -- (FIXME) Very similar to `Lambda.inferOp`, except that the body is annotated
  -- using `LExprT.fromLExpr`. Can we share code here?
  --
  -- `LFunc.type` below will also catch any ill-formed functions (e.g.,
  -- where there are duplicates in the formals, etc.).
  let type ← func.type
  let (_ty, T) ← LTy.instantiateWithCheck type T
  match func.body with
  | none => .ok (func, T)
  | some body =>
    -- Temporarily add formals in the context.
    let T := T.pushEmptyContext
    let T := T.addToContext func.inputPolyTypes
    -- Type check and annotate the body, and ensure that it unifies with the
    -- return type.
    let (bodya, T) ← LExprT.fromLExpr T body
    let bodyty := bodya.toLMonoTy
    let (retty, T) ← func.outputPolyType.instantiateWithCheck T
    let S ← Constraints.unify [(retty, bodyty)] T.state.substInfo
    let T := T.updateSubst S
    let T := T.popContext
    let new_func := { func with body := bodya.toLExpr }
    .ok (new_func, T)

end Function

---------------------------------------------------------------------
end Boogie
