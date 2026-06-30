/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Core.Function
import Strata.DL.Lambda.LExprT
import Strata.Languages.Core.Procedure

---------------------------------------------------------------------

public section

namespace Core

namespace Function

open Lambda Imperative
open Std (ToFormat Format format)

def typeCheck (C: Core.Expression.TyContext) (Env : Core.Expression.TyEnv) (func : Function) :
    Except Format (Function × Core.Expression.TyEnv) := do
  -- `LFunc.type` below will also catch any ill-formed functions (e.g.,
  -- where there are duplicates in the formals, etc.).
  let origTypeArgs := func.typeArgs
  -- Ambient context types, for the #1399 generalization check (preserved by instantiation).
  let ambientTypes := Env.context.types
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
  -- Substitution to rename fresh type variables back to user-supplied names.
  -- Only pairs where the fresh name actually survived alias resolution are included.
  let userTypeArgs := func.typeArgs.zip origTypeArgs
  let userSubst : Subst :=
    [userTypeArgs.map (fun (fresh, orig) => (fresh, .ftvar orig))]
  match func.body with
  | none =>
    -- A measure (decreases clause) is only meaningful for a function with a
    -- body; reject one on a bodiless function so it is never left unvalidated.
    if func.measure.isSome then
      .error f!"Function '{func.name}': a decreases clause was supplied but the \
                function has no body"
    let func := { func with
      typeArgs := userTypeArgs.map (·.2),
      inputs := func.inputs.map (fun (id, mty) => (id, LMonoTy.subst userSubst mty)),
      output := LMonoTy.subst userSubst func.output }
    .ok (func, Env)
  | some body =>
    -- Reject body annotations referencing type variables not in typeArgs.
    let bodyVars := body.tyVarsOfBinderAnnotations
    let strayVars := bodyVars.filter (· ∉ origTypeArgs)
    if !strayVars.isEmpty then
      .error f!"Function '{func.name}': body contains undeclared type variables \
                {strayVars.toList} (not in typeArgs {origTypeArgs})"
    -- Add formals with monomorphic types (type parameters are fixed in the body).
    let Env := Env.pushEmptyContext
    let Env := Env.addInNewestContext (LFunc.inputMonoSignature func)
    -- Save this initial context (formals pushed, before the body's unification)
    -- so the measure can be type-checked independently against the same context.
    let measureBaseEnv := Env
    -- Type check the body and unify with the return type.
    let (bodya, Env) ← LExpr.resolve C Env body
    let bodyty := bodya.toLMonoTy
    let retty := func.output
    let S ← Constraints.unify [(retty, bodyty)] (TEnv.stateSubstInfo Env) |>.mapError format
    -- The inferred type must be alpha-equivalent to the declared signature.
    -- Unlike OCaml, where annotations are lower bounds (the body may be more
    -- specific), we require exact polymorphism: if f<a>(x:a):a is declared,
    -- the body cannot force a=int. This is appropriate for an IR where
    -- the user can give annotations as needed.
    let inferredTy := LMonoTy.subst S.subst monoty
    -- Reject check: the body must not over-constrain the polymorphic signature.
    -- `alphaEquivMap` succeeds iff `S.subst` acts as a bijective variable renaming on
    -- `monoty`'s type variables (anything else — e.g. pinning a parameter to a concrete
    -- type — fails the match). We only consume the success bit here; the renaming itself
    -- is reconstructed directly from `S.subst` below, as its inverse on `monoty`'s fresh
    -- instantiation variables.
    match LMonoTy.alphaEquivMap monoty inferredTy with
      | some _ => pure ()
      | none =>
        let displayInferred := LMonoTy.subst userSubst inferredTy
        let displayMono := LMonoTy.subst userSubst monoty
        .error f!"Function '{func.name}': body constrains the type to '{displayInferred}', \
                  incompatible with declared polymorphic signature '{displayMono}'"
    let Env := TEnv.updateSubst Env S
    -- Ambient type variables (e.g. an enclosing procedure's type parameters) are
    -- rigid in the body: the function body may not refine them to concrete types.
    -- This mirrors the var-initializer check in `CmdType.checkAnnotCompat`; without
    -- it, a nested `function f() : int { y }` over an ambient `y : t` would silently
    -- specialize the rigid `t := int`.
    let Sb := Env.stateSubstInfo.subst
    match C.rigidTypeVars.find? (fun v => LMonoTy.subst Sb (.ftvar v) != .ftvar v) with
    | some v =>
      let inferred := LMonoTy.subst Sb (.ftvar v)
      .error f!"Function '{func.name}': rigid type variable '{v}' was refined to \
                '{inferred}' by the body"
    | none => pure ()
    -- Generalization side condition (#1399): may only generalize over `ftv(τ) \ ftv(Γ)`.
    let ambientFreeVars := Lambda.TContext.types.knownTypeVars
      (Lambda.TContext.types.subst ambientTypes Sb)
    let genVars := (LMonoTy.subst Sb monoty).freeVars
    match genVars.find? (fun v => ambientFreeVars.contains v) with
    | some v =>
      .error f!"Function '{func.name}': type variable '{v}' is free in the enclosing \
                context and cannot be generalized; the body pins a declared type \
                parameter to an ambient type"
    | none => pure ()
    -- Apply S to the body, then rename type variables back to the instantiation
    -- variables so that body annotations are consistent. The `alphaEquivMap` check
    -- above guarantees `S.subst` acts as a bijective renaming on `monoty`'s type
    -- variables, so the renaming is exactly the *inverse* of `S.subst` on those
    -- variables: each instantiation var `x` is sent by `S.subst` to some `ftvar y`,
    -- and we map `y ↦ ftvar x` (dropping identity entries `x = y`). Building it
    -- directly from the instantiation's own variable list `monoty.freeVars.eraseDups`
    -- makes this inverse definitional, rather than recovering it from `alphaEquivMap`.
    let bodya := LExpr.applySubstT bodya S.subst
    let renameSubst : Subst :=
      [monoty.freeVars.eraseDups.filterMap (fun x =>
        match LMonoTy.subst S.subst (.ftvar x) with
        | .ftvar y => if x == y then none else some (y, .ftvar x)
        | _ => none)]
    let bodya := LExpr.applySubstT bodya renameSubst
    -- Validate the measure expression type for int-recursive functions.
    -- Only validates non-fvar measures (fvar measures are validated in TermCheck
    -- using the TypeFactory, which has ADT information).
    let measure' ← match func.measure with
    | some measure =>
      match measure with
      | .fvar _ _ _ => pure func.measure
      | _ =>
        -- Type-check the measure independently of the body, against the SAME
        -- initial context (formals at their declared types). The signature's
        -- type parameters (`func.typeArgs`, now fresh instantiation vars) are
        -- rigid here, exactly as in the body: the measure may not specialize
        -- the function's polymorphic signature. Without this, a measure like
        -- `decreases (x + 0)` for `f<a>(x:a)` would pin `a := int` while the
        -- signature stays polymorphic, so the formal `x : a` would not actually
        -- carry an int-typed measure.
        let measureRigid := func.typeArgs ++ C.rigidTypeVars
        let Cm := { C with rigidTypeVars := measureRigid }
        let (measurea, measureEnv) ← LExpr.resolve Cm measureBaseEnv measure
        let Sm := measureEnv.stateSubstInfo.subst
        let measurety := measurea.toLMonoTy
        if measurety != .int then
          .error f!"recursive function '{func.name}': non-variable decreases expression must have type int, got '{measurety}'. For structural recursion, use a parameter name"
        else
          match measureRigid.find? (fun v => LMonoTy.subst Sm (.ftvar v) != .ftvar v) with
          | some v =>
            let inferred := LMonoTy.subst Sm (.ftvar v)
            .error f!"recursive function '{func.name}': decreases expression refines type \
                      variable '{v}' to '{inferred}'; a measure may not constrain the \
                      function's polymorphic signature or an enclosing rigid type variable"
          | none =>
            pure (some (LExpr.applySubstT measurea userSubst).unresolved)
    | none => pure none
    let Env := TEnv.popContext Env
    -- Rename back to user type variable names.
    let bodya := LExpr.applySubstT bodya userSubst
    let new_func := { func with
      typeArgs := userTypeArgs.map (·.2),
      inputs := func.inputs.map (fun (id, mty) => (id, LMonoTy.subst userSubst mty)),
      output := LMonoTy.subst userSubst func.output,
      body := some bodya.unresolved,
      measure := measure' }
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
