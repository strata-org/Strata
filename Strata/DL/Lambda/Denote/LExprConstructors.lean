/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

import all Strata.DL.Lambda.Denote.CallOfLFuncDenote
import all Strata.DL.Lambda.LTyUnify
import all Strata.DL.Lambda.FactoryWF

namespace Lambda

/-! ## Type substitution agreement lemmas

These lemmas establish that if two substitutions produce the same result on a
type, they must agree on all free variables of that type — and conversely, if
they agree on all free variables, they produce the same result. -/

/-- If two substitutions produce the same result on a type `ty`, then they
agree on every free variable of `ty`. -/
theorem subst_eq_implies_agree_on_freeVars
    {S₁ S₂ : Subst}
    {ty : LMonoTy}
    (h : LMonoTy.subst S₁ ty = LMonoTy.subst S₂ ty)
    (v : TyIdentifier)
    (hv : v ∈ LMonoTy.freeVars ty)
    : S₁.find? v = S₂.find? v := by
  sorry

/-- If two substitutions agree on all free variables of `ty`, then they
produce the same result on `ty`. -/
theorem agree_on_freeVars_implies_subst_eq
    {S₁ S₂ : Subst}
    {ty : LMonoTy}
    (h : ∀ v, v ∈ LMonoTy.freeVars ty → S₁.find? v = S₂.find? v)
    : LMonoTy.subst S₁ ty = LMonoTy.subst S₂ ty := by
  sorry

/-- List version: if two substitutions agree on all free variables of every
type in a list, then mapping `subst` over the list produces the same result. -/
theorem agree_on_freeVars_implies_subst_eq_list
    {S₁ S₂ : Subst}
    {tys : List LMonoTy}
    (h : ∀ v, v ∈ LMonoTys.freeVars tys → S₁.find? v = S₂.find? v)
    : tys.map (LMonoTy.subst S₁) = tys.map (LMonoTy.subst S₂) := by
  sorry

/-! ## Constructor output type determines argument types

For ADT constructors, the output type is `tcons d.name (d.typeArgs.map .ftvar)`,
so all type parameters appear directly in the output type. This means the
output type uniquely determines the type substitution, and hence the argument
types. -/

/-- For a constructor whose output type contains all of its type arguments as
free variables: if two type substitutions produce the same output type, they
produce the same argument types.

The hypothesis `h_output_covers` holds for all ADT constructors, since
`constrFunc` sets `output := dataDefault d = .tcons d.name (d.typeArgs.map .ftvar)`
and `typeArgs := d.typeArgs`. -/
theorem constr_same_output_implies_same_argTys
    {T : LExprParams}
    {f : LFunc T}
    {S₁ S₂ : Subst}
    (h_wf : LFuncWF f)
    (h_output_eq : LMonoTy.subst S₁ f.output = LMonoTy.subst S₂ f.output)
    (h_output_covers : ∀ v, v ∈ f.typeArgs → v ∈ LMonoTy.freeVars f.output)
    : (f.inputs.map Prod.snd).map (LMonoTy.subst S₁) =
      (f.inputs.map Prod.snd).map (LMonoTy.subst S₂) := by
  sorry

/-! ## Constructor output type determines argument types (combined lemma)

For ADT constructor applications: if two expressions `e₁, e₂` call the same
constructor `fn` and both have result type `τ`, then the argument type lists
`argTys₁` and `argTys₂` must be equal.

This is because:
1. `OpsConsistent` gives type substitutions `S₁, S₂` with
   `ty_opᵢ = (mkArrow' fn.output inputTys).subst Sᵢ`
2. Combined with `hty_opᵢ : ty_opᵢ = mkArrow' τ argTysᵢ`, by `mkArrow'_injective`:
   `τ = fn.output.subst S₁ = fn.output.subst S₂`
3. For constructors, the output type contains all type parameters as free vars,
   so equal output substitutions force equal input substitutions
4. Hence `argTys₁ = argTys₂`
-/
theorem constr_callOfLFunc_argTys_eq
    {T : LExprParams} [DecidableEq T.IDMeta] [Inhabited T.mono.base.IDMeta]
    {F : @Factory T}
    {e₁ e₂ : LExpr T.mono} {τ : LMonoTy}
    {callee₁ callee₂ : LExpr T.mono}
    {args₁ args₂ : List (LExpr T.mono)} {fn : LFunc T}
    {argTys₁ argTys₂ : List LMonoTy}
    (hcall₁ : Factory.callOfLFunc F e₁ = some (callee₁, args₁, fn))
    (hcall₂ : Factory.callOfLFunc F e₂ = some (callee₂, args₂, fn))
    (h₁ : LExpr.HasTypeA [] e₁ τ) (h₂ : LExpr.HasTypeA [] e₂ τ)
    (h_args₁ : List.Forall₂ (LExpr.HasTypeA []) args₁ argTys₁)
    (h_args₂ : List.Forall₂ (LExpr.HasTypeA []) args₂ argTys₂)
    (hoc₁ : OpsConsistent F e₁) (hoc₂ : OpsConsistent F e₂)
    (hfwf : FactoryWF F)
    (hconstr : fn.isConstr = true)
    (hcallee₁ : ∃ m n, callee₁ = .op m n (some (LMonoTy.mkArrow' τ argTys₁)))
    (hcallee₂ : ∃ m n, callee₂ = .op m n (some (LMonoTy.mkArrow' τ argTys₂)))
    : argTys₁ = argTys₂ := by
  sorry

end Lambda
