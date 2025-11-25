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

def typeCheck (C: Boogie.Expression.TyContext) (Env : Boogie.Expression.TyEnv) (func : Function) :
  Except Format (Function × Boogie.Expression.TyEnv) := do
  -- (FIXME) Very similar to `Lambda.inferOp`, except that the body is annotated
  -- using `LExprT.resolve`. Can we share code here?
  --
  -- `LFunc.type` below will also catch any ill-formed functions (e.g.,
  -- where there are duplicates in the formals, etc.).
  let type ← func.type
  let (_ty, Env) ← LTy.instantiateWithCheck type C Env
  match func.body with
  | none => .ok (func, Env)
  | some body =>
    -- Temporarily add formals in the context.
    let Env := Env.pushEmptyContext
    let Env := Env.addToContext func.inputPolyTypes
    -- Type check and annotate the body, and ensure that it unifies with the
    -- return type.
    let (bodya, Env) ← LExpr.resolve C Env body
    let bodyty := bodya.toLMonoTy
    let (retty, Env) ← func.outputPolyType.instantiateWithCheck C Env
    let S ← Constraints.unify [(retty, bodyty)] Env.stateSubstInfo
    let Env := Env.updateSubst S
    let Env := Env.popContext
    let new_func := func
    .ok (new_func, Env)

end Function

---------------------------------------------------------------------
end Boogie
