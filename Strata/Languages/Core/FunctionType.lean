/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Core.Function
public import Strata.Languages.Core.Program

---------------------------------------------------------------------

public section

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
  let origTypeArgs := func.typeArgs
  let type ← func.type
  let undeclaredVars := LTy.freeVars type
  if undeclaredVars != [] then
    .error f!"Function '{func.name}': type variables {undeclaredVars} appear in \
              the signature but are not declared in typeArgs {func.typeArgs}"
  let (monoty, Env) ← LTy.instantiateWithCheck type C Env
  let monotys := monoty.destructArrow
  -- Use the number of formal parameters to determine which arrow components are
  -- inputs.
  let numInputs := func.inputs.keys.length
  let input_mtys := monotys.take numInputs
  let remaining := monotys.drop numInputs
  -- Reconstruct the output type from the arrow components after the `numInputs`
  -- inputs.
  let output_mty : LMonoTy :=
    let last := remaining.getLast? |>.getD
      (monotys.getLast (by exact LMonoTy.destructArrow_non_empty monoty))
    LMonoTy.mkArrow' last remaining.dropLast
  -- Resolve type aliases and monomorphize inputs and output.
  let func := { func with
                  typeArgs := monoty.freeVars.eraseDups,
                  inputs := func.inputs.keys.zip input_mtys,
                  output := output_mty}
  match func.body with
  | none => .ok (func, Env)
  | some body =>
    -- Reject body annotations referencing type variables not in typeArgs.
    let bodyVars := body.annotationTyVars
    let strayVars := bodyVars.filter (· ∉ origTypeArgs)
    if !strayVars.isEmpty then
      .error f!"Function '{func.name}': body contains undeclared type variables \
                {strayVars.toList} (not in typeArgs {origTypeArgs})"
    -- Treat each declared type parameter as an opaque (rigid) 0-ary type
    -- constructor while checking the body. This gives parametric polymorphism:
    -- type parameters are fixed within the body and cannot be unified with
    -- any concrete type or with each other (Boogie/Java-generic style).
    --
    -- The transformation: for each `v ∈ func.typeArgs`, replace `.ftvar v`
    -- with `.tcons v []` in the input/output types. After body checking, the
    -- inverse transformation is applied to body annotations so that the
    -- resulting `Function` reports its types using `.ftvar` for type
    -- parameters (matching the rest of the type system's conventions).
    let rigidTyArgs := func.typeArgs
    let rigidSubst : Subst := [rigidTyArgs.map (fun v => (v, LMonoTy.tcons v []))]
    let rigidInputs := func.inputs.map (fun (id, mty) => (id, LMonoTy.subst rigidSubst mty))
    let rigidOutput := LMonoTy.subst rigidSubst func.output
    -- Register the rigid type-parameter constructors as known 0-ary types
    -- so that `LExpr.resolve` accepts them.
    let knownTypesWithRigids : Lambda.KnownTypes :=
      rigidTyArgs.foldl (fun ks v => ks.insert v 0) C.knownTypes
    let C' := { C with knownTypes := knownTypesWithRigids }
    -- Add formals with rigidified types to the body's typing context.
    let Env := Env.pushEmptyContext
    let monoInputs : @LTySignature Unit :=
      rigidInputs.map (fun (id, mty) => (id, .forAll [] mty))
    let Env := Env.addInNewestContext monoInputs
    -- Type check the body. Any attempt to constrain a rigid type parameter
    -- to a concrete type (or to identify two distinct parameters) shows up
    -- as a unification failure here.
    let (bodya, Env) ← (LExpr.resolve C' Env body).mapError
      fun e => f!"Function '{func.name}': body is incompatible with declared \
                  polymorphic signature. {e}"
    let bodyty := bodya.toLMonoTy
    let S ← Constraints.unify [(rigidOutput, bodyty)] (TEnv.stateSubstInfo Env)
              |>.mapError fun e =>
                f!"Function '{func.name}': body type {format bodyty} is incompatible \
                   with declared signature. {format e}"
    let Env := TEnv.updateSubst Env S
    -- Apply the unification substitution and then strip the rigidification:
    -- replace `.tcons v []` (for `v ∈ rigidTyArgs`) back with `.ftvar v`.
    let bodya := LExpr.applySubstT bodya S.subst
    let bodya := LExpr.unrigidifyTyArgs rigidTyArgs bodya
    -- Validate the measure expression type for int-recursive functions.
    -- Only validates non-fvar measures (fvar measures are validated in TermCheck
    -- using the TypeFactory, which has ADT information).
    match func.measure with
    | some measure =>
      match measure with
      | .fvar _ _ _ => pure ()
      | _ =>
        let (measurea, _) ← LExpr.resolve C Env measure
        let measurety := measurea.toLMonoTy
        if measurety != .int then
          .error f!"recursive function '{func.name}': non-variable decreases expression must have type int, got '{measurety}'. For structural recursion, use a parameter name"
    | none => pure ()
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
  let func ← Function.ofPureFunc decl
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

end -- public section
