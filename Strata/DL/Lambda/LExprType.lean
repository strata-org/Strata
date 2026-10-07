/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.DL.Lambda.Factory
import all Strata.DL.Lambda.Factory

/-! ## Lambda Expression Typing -/

namespace Lambda

open Strata

public section

/--
Apply type substitution `S` to all type annotations in an `LExpr`.
This is only for user-defined types, not metadata-stored resolved types.
If e is an LExprT whose metadata contains type information, use applySubstT.
-/
def LExpr.applyTypeSubst {T : LExprParams} (e : LExpr T.mono) (S : Subst) : LExpr T.mono :=
  if S.hasEmptyScopes then e else replaceUserProvidedType e (LMonoTy.subst S)

/-- Typecheck an annotated `LExpr`, returning `some τ` if well-typed, `none`
otherwise. `ctx` maps de Bruijn indices to their types from enclosing
binders. -/
@[expose]
def LExpr.typeCheck {T : LExprParams} (ctx : List LMonoTy) : LExpr T.mono → Option LMonoTy
  | .const _ c => some c.ty
  | .op _ _ (some ty) => some ty
  | .op _ _ none => none
  | .fvar _ _ (some ty) => some ty
  | .fvar _ _ none => none
  | .bvar _ i => ctx[i]?
  | .abs _ _ (some aty) body => do
    let rty ← typeCheck (aty :: ctx) body
    some (.arrow aty rty)
  | .abs _ _ none _ => none
  | .quant _ _ _ (some qty) tr body => do
    let _ ← typeCheck (qty :: ctx) tr
    let bty ← typeCheck (qty :: ctx) body
    guard (bty == .bool)
    some .bool
  | .quant _ _ _ none _ _ => none
  | .app _ fn arg => do
    let fty ← typeCheck ctx fn
    let aty ← typeCheck ctx arg
    let (dom, cod) ← fty.isArrow
    guard (dom == aty)
    some cod
  | .ite _ c t e => do
    let cty ← typeCheck ctx c
    let tty ← typeCheck ctx t
    let ety ← typeCheck ctx e
    guard (cty == .bool)
    guard (tty == ety)
    some tty
  | .eq _ e1 e2 => do
    let ty1 ← typeCheck ctx e1
    let ty2 ← typeCheck ctx e2
    guard (ty1 == ty2)
    some .bool

/--
Derive a type substitution from the `.op` type annotation alone, by unifying it
against the function's generic type. On annotated terms (i.e., terms that have
undergone type inference), the `.op` node always carries a type annotation, so
this suffices.

Returns `some Subst.empty` when `fn.typeArgs` is empty (monomorphic — no-op).
Returns `none` if the callee is not annotated or unification fails.
-/
@[expose] def LFunc.opTypeSubst {T : LExprParams} (fn : LFunc T) (callee : LExpr T.mono)
    : Option Subst :=
  if fn.typeArgs.isEmpty then some Subst.empty
  else match callee with
    | .op _ _ (some instTy) =>
      let genericTy := LMonoTy.mkArrow' fn.output fn.inputs.values
      match Constraints.unify [(instTy, genericTy)] SubstInfo.empty with
      | .ok substInfo => some substInfo.subst
      | .error _ => none
    | _ => none

/--
Derive a type substitution by unifying the instantiated operator type against the
function's generic type. Used when inlining a polymorphic function body to
instantiate type variables.

Prefers the `.op` annotation (via `opTypeSubst`). Falls back to a best-effort
approach using argument types when the `.op` is not annotated. On annotated terms
(after type inference), the `.op` always carries a type annotation, so the fallback
is never needed.

Returns `some Subst.empty` when `fn.typeArgs` is empty (monomorphic — no-op).
Returns `none` if the type substitution cannot be derived.
-/
@[expose] def LFunc.computeTypeSubst {T : LExprParams} (fn : LFunc T) (callee : LExpr T.mono)
    (args : List (LExpr T.mono)) : Option Subst :=
  match fn.opTypeSubst callee with
  | some s => some s
  | none =>
    -- Fallback: use argument types (best-effort, only when .op is unannotated)
    if fn.typeArgs.isEmpty then some Subst.empty
    else
      let argConstraints := (args.zip fn.inputs.values).filterMap
        (fun (arg, formal) => (LExpr.typeCheck [] arg).map (·, formal))
      if argConstraints.isEmpty then none
      else match Constraints.unify argConstraints SubstInfo.empty with
        | .ok substInfo => some substInfo.subst
        | .error _ => none

end -- public section
end Lambda
