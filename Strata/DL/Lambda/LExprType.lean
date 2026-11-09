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

/-! ### `LExpr.typeCheck`'s rules for one node

The `app`, `ite` and `eq` rules of `LExpr.typeCheck`, as functions of the
children's types, for callers that compute those types another way (such as the
memoized check of common subexpression elimination). `LExpr.typeCheck` keeps
its rules inline, because the proofs about it unfold its body; the
`typeCheck_app`, `typeCheck_ite` and `typeCheck_eq` lemmas below state that
each of its cases is the corresponding rule, so the two cannot drift apart. -/

/-- The type of an application whose function has type `fty` and whose argument
has type `aty`: the codomain of `fty`, if `fty` is an arrow from `aty`. -/
@[expose]
def LMonoTy.appTy? (fty aty : LMonoTy) : Option LMonoTy := do
  let (dom, cod) ← fty.isArrow
  guard (dom == aty)
  some cod

/-- The type of `if c then t else e` with `c : cty`, `t : tty` and `e : ety`:
`tty`, if `cty` is `bool` and the branches agree. -/
@[expose]
def LMonoTy.iteTy? (cty tty ety : LMonoTy) : Option LMonoTy := do
  guard (cty == .bool)
  guard (tty == ety)
  some tty

/-- The type of `e1 == e2` with `e1 : ty1` and `e2 : ty2`: `bool`, if the sides
agree. -/
@[expose]
def LMonoTy.eqTy? (ty1 ty2 : LMonoTy) : Option LMonoTy := do
  guard (ty1 == ty2)
  some .bool

/-- `LExpr.typeCheck` types an application by typing its function and its
argument, then applying `LMonoTy.appTy?` to the two types. -/
theorem LExpr.typeCheck_app {T : LExprParams} (ctx : List LMonoTy) (m : T.mono.base.Metadata)
    (fn arg : LExpr T.mono) :
    LExpr.typeCheck ctx (.app m fn arg) = (do
      let fty ← LExpr.typeCheck ctx fn
      let aty ← LExpr.typeCheck ctx arg
      LMonoTy.appTy? fty aty) := rfl

/-- `LExpr.typeCheck` types `if c then t else e` by typing the condition and
both branches, then applying `LMonoTy.iteTy?` to the three types. -/
theorem LExpr.typeCheck_ite {T : LExprParams} (ctx : List LMonoTy) (m : T.mono.base.Metadata)
    (c t e : LExpr T.mono) :
    LExpr.typeCheck ctx (.ite m c t e) = (do
      let cty ← LExpr.typeCheck ctx c
      let tty ← LExpr.typeCheck ctx t
      let ety ← LExpr.typeCheck ctx e
      LMonoTy.iteTy? cty tty ety) := rfl

/-- `LExpr.typeCheck` types `e1 == e2` by typing both sides, then applying
`LMonoTy.eqTy?` to the two types. -/
theorem LExpr.typeCheck_eq {T : LExprParams} (ctx : List LMonoTy) (m : T.mono.base.Metadata)
    (e1 e2 : LExpr T.mono) :
    LExpr.typeCheck ctx (.eq m e1 e2) = (do
      let ty1 ← LExpr.typeCheck ctx e1
      let ty2 ← LExpr.typeCheck ctx e2
      LMonoTy.eqTy? ty1 ty2) := rfl

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

/--
Check every operator annotation of `e` against the factory `F`: an `.op` naming
a function `fn` of `F` must be annotated, and its annotation must be an instance of
`fn`'s type `inputs → output`, that is, `LMonoTy.matchSubst` finds a substitution of the
type variables of `fn`'s type that turns it into the annotation. The annotation's own type
variables are not substituted. Operators that `F` does not define are not constrained.

The check implies the declarative `OpsConsistentR` (`opsConsistent_sound`), but not
`OpsConsistent`, which requires the annotation to equal the function's type under the
substitution `LFunc.opTypeSubst` computes by two-way unification. That substitution can
differ from the one-way match in two ways. When the annotation has type variables of its
own, unification may bind those instead of the function's: `id : a → a` annotated `b → b`
matches, but unification maps `b` to `a`, and `a → a` is not the annotation. And a
function with no `typeArgs` gets the empty substitution, even when its type mentions a
type variable that matching binds.
-/
@[expose]
def LExpr.opsConsistent {T : LExprParams} (F : Factory T) : LExpr T.mono → Bool
  | .op _ name ty =>
    match F[name.name]?, ty with
    | none, _ => true
    | some fn, some tyOp =>
      ((LMonoTy.mkArrow' fn.output (fn.inputs.map Prod.snd)).matchSubst tyOp).isSome
    | some _, none => false
  | .app _ fn arg => opsConsistent F fn && opsConsistent F arg
  | .abs _ _ _ body => opsConsistent F body
  | .ite _ c t f => opsConsistent F c && opsConsistent F t && opsConsistent F f
  | .eq _ e1 e2 => opsConsistent F e1 && opsConsistent F e2
  | .quant _ _ _ _ tr body => opsConsistent F tr && opsConsistent F body
  | _ => true

/-- Type check `e` (as `LExpr.typeCheck`) against the factory `F`: `none` unless
every operator annotation of `e` agrees with its signature in `F`. -/
@[expose]
def LExpr.typeCheckWith {T : LExprParams} (F : Factory T) (ctx : List LMonoTy)
    (e : LExpr T.mono) : Option LMonoTy :=
  if e.opsConsistent F then e.typeCheck ctx else none

end -- public section
end Lambda
