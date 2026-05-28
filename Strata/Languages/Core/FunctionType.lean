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

/--
Check if two monotypes are alpha-equivalent (equal up to consistent renaming of
free type variables). Returns the backward mapping (ty2 vars → ty1 vars) on
success, which can be used to rename annotations in the body back to the
declared type parameter names.

This check is equivalent to treating declared type parameters as rigid/skolem
constants during body checking: both formulations reject programs where the body
constrains a type parameter to a concrete type or identifies distinct parameters.
-/
def LMonoTy.alphaEquiv (ty1 ty2 : LMonoTy) :
    Option (Std.HashMap TyIdentifier TyIdentifier) :=
  (go ty1 ty2 {} {}).map (·.2)
where
  go (t1 t2 : LMonoTy) (fwd : Std.HashMap TyIdentifier TyIdentifier)
     (bwd : Std.HashMap TyIdentifier TyIdentifier) :
     Option (Std.HashMap TyIdentifier TyIdentifier × Std.HashMap TyIdentifier TyIdentifier) :=
    match t1, t2 with
    | .ftvar x, .ftvar y =>
      match fwd[x]? with
      | some y' => if y' == y then some (fwd, bwd) else none
      | none =>
        match bwd[y]? with
        | some x' => if x' == x then some (fwd, bwd) else none
        | none => some (fwd.insert x y, bwd.insert y x)
    | .bitvec n, .bitvec m => if n == m then some (fwd, bwd) else none
    | .tcons n1 args1, .tcons n2 args2 =>
      if n1 != n2 then none
      else goList args1 args2 fwd bwd
    | _, _ => none
  goList (ts1 ts2 : List LMonoTy) (fwd : Std.HashMap TyIdentifier TyIdentifier)
     (bwd : Std.HashMap TyIdentifier TyIdentifier) :
     Option (Std.HashMap TyIdentifier TyIdentifier × Std.HashMap TyIdentifier TyIdentifier) :=
    match ts1, ts2 with
    | [], [] => some (fwd, bwd)
    | t1 :: rest1, t2 :: rest2 =>
      match go t1 t2 fwd bwd with
      | some (fwd', bwd') => goList rest1 rest2 fwd' bwd'
      | none => none
    | _, _ => none

def typeCheck (C: Core.Expression.TyContext) (Env : Core.Expression.TyEnv) (func : Function) :
    Except Format (Function × Core.Expression.TyEnv) := do
  -- (FIXME) Very similar to `Lambda.inferOp`, except that the body is annotated
  -- using `LExprT.resolve`. Can we share code here?
  --
  -- `LFunc.type` below will also catch any ill-formed functions (e.g.,
  -- where there are duplicates in the formals, etc.).
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
    -- Temporarily add formals in the context with monomorphic types.
    -- Type parameters are fixed within the body (Boogie/Java style).
    let Env := Env.pushEmptyContext
    let monoInputs : @LTySignature Unit :=
      func.inputs.map (fun (id, mty) => (id, .forAll [] mty))
    let Env := Env.addInNewestContext monoInputs
    -- Type check and annotate the body, and ensure that it unifies with the
    -- return type (used directly as a monotype, not re-instantiated).
    let (bodya, Env) ← LExpr.resolve C Env body
    let bodyty := bodya.toLMonoTy
    let retty := func.output
    let S ← Constraints.unify [(retty, bodyty)] (TEnv.stateSubstInfo Env) |>.mapError format
    -- Verify that the inferred type is alpha-equivalent to the declared signature.
    -- This rejects bodies that constrain a declared type parameter to a concrete
    -- type (e.g., `foo<a>(x:a):a { x+1 }` infers `int→int` ≠α `a→a`).
    let inferredTy := LMonoTy.subst S.subst monoty
    let bwdMap ← match LMonoTy.alphaEquiv monoty inferredTy with
      | some m => pure m
      | none =>
        .error f!"Function '{func.name}': body constrains the type to '{inferredTy}', \
                  incompatible with declared polymorphic signature '{monoty}'"
    let Env := TEnv.updateSubst Env S
    -- Apply the unification substitution to the body, then rename any type
    -- variables back to the declared type parameter names using the backward
    -- mapping from alpha-equivalence. This ensures annotations are consistent
    -- with the function's typeArgs (required by denotational semantics).
    let bodya := LExpr.applySubstT bodya S.subst
    let renameSubst : Subst := [bwdMap.toList.map (fun (k, v) => (k, .ftvar v))]
    let bodya := LExpr.applySubstT bodya renameSubst
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
