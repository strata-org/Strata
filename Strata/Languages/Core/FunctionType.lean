/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/



import Strata.Languages.Core.Function
import Strata.Languages.Core.Program

---------------------------------------------------------------------

namespace Core

namespace Function

open Lambda Imperative
open Std (ToFormat Format format)

def typeCheck (C: Core.Expression.TyContext) (Env : Core.Expression.TyEnv) (func : Function) :
    Except Format (Function × Core.Expression.TyEnv) := do
  -- (FIXME) Very similar to `Lambda.inferOp`, except that the body is annotated
  -- using `LExprT.resolve`. Can we share code here?
  --
  -- `LFunc.type` below will also catch any ill-formed functions (e.g.,
  -- where there are duplicates in the formals, etc.).
  let type ← func.type
  let (monoty, Env) ← LTy.instantiateWithCheck type C Env
  let monotys := monoty.destructArrow
  let input_mtys := monotys.dropLast
  let output_mty := monotys.getLast (by exact LMonoTy.destructArrow_non_empty monoty)
  -- Resolve type aliases and monomorphize inputs and output.
  let func := { func with
                  typeArgs := monoty.freeVars.eraseDups,
                  inputs := func.inputs.keys.zip input_mtys,
                  output := output_mty}
  match func.body with
  | none => .ok (func, Env)
  | some body =>
    -- Temporarily add formals in the context.
    let Env := Env.pushEmptyContext
    let Env := Env.addInNewestContext (LFunc.inputPolyTypes func)
    -- Type check and annotate the body, and ensure that it unifies with the
    -- return type.
    let (bodya, Env) ← LExpr.resolve C Env body
    let bodyty := bodya.toLMonoTy
    let (retty, Env) ← (LFunc.outputPolyType func).instantiateWithCheck C Env
    let S ← Constraints.unify [(retty, bodyty)] (TEnv.stateSubstInfo Env) |>.mapError format
    let Env := TEnv.updateSubst Env S
    let Env := TEnv.popContext Env
    -- Resolve type aliases and monomorphize the body.
    let new_func := { func with body := some bodya.unresolved }
    .ok (new_func, Env)

end Function

/--
If `Function.typeCheck` succeeds, the inputs of the resulting function have no duplicate names.
-/
theorem Function.typeCheck_inputs_nodup (C: Core.Expression.TyContext) (Env : Core.Expression.TyEnv)
    (func : Function) (func' : Function) (Env' : Core.Expression.TyEnv) :
    Function.typeCheck C Env func = .ok (func', Env') → func.inputs.keys.Nodup := by
  intro h
  simp only [Function.typeCheck, bind, Except.bind] at h
  split at h <;> try contradiction
  rename_i ty hty
  -- func.type succeeded, so we can use LFunc.type_inputs_nodup
  exact Lambda.LFunc.type_inputs_nodup func ty hty

namespace PureFunc

open Lambda Imperative
open Std (ToFormat Format format)

/--
Type check a `PureFunc Expression` (used in statement-level function declarations).
Converts to `Function`, type checks, and returns both the type-checked `PureFunc`
and the `Function` (for adding to the context).
-/
def typeCheck (C: Core.Expression.TyContext) (Env : Core.Expression.TyEnv) (decl : PureFunc Expression) :
    Except Format (PureFunc Expression × Function × Core.Expression.TyEnv) := do
  -- Convert PureFunc to Function for type checking
  let func : Function := {
    name := decl.name,
    typeArgs := decl.typeArgs,
    isConstr := decl.isConstr,
    inputs := decl.inputs.map (fun (id, ty) => (id, Lambda.LTy.toMonoTypeUnsafe ty)),
    output := Lambda.LTy.toMonoTypeUnsafe decl.output,
    body := decl.body,
    attr := decl.attr,
    concreteEval := none,  -- Can't convert concreteEval safely
    axioms := decl.axioms
  }
  let (func', Env) ← Function.typeCheck C Env func
  -- Convert back by wrapping monotypes in trivial polytypes
  let decl' : PureFunc Expression := {
    name := func'.name,
    typeArgs := func'.typeArgs,
    isConstr := func'.isConstr,
    inputs := func'.inputs.map (fun (id, mty) => (id, .forAll [] mty)),
    output := .forAll [] func'.output,
    body := func'.body,
    attr := func'.attr,
    concreteEval := decl.concreteEval,  -- Preserve original
    axioms := func'.axioms
  }
  .ok (decl', func', Env)

end PureFunc

---------------------------------------------------------------------
end Core
