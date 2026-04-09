/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

import all Strata.DL.Lambda.Denote.CallOfLFuncDenote
import all Strata.DL.Lambda.LTyUnify
import all Strata.DL.Lambda.FactoryWF

namespace Lambda

/-- If `v ∈ LMonoTys.freeVars tys` and every element's free vars are in `S`,
then `v ∈ S`. -/
theorem LMonoTys.freeVars_subset
    {tys : List LMonoTy} {S : List TyIdentifier}
    (h : ∀ ty, ty ∈ tys → LMonoTy.freeVars ty ⊆ S)
    {v : TyIdentifier}
    (hv : v ∈ LMonoTys.freeVars tys)
    : v ∈ S := by
  induction tys with
  | nil => simp [LMonoTys.freeVars] at hv
  | cons ty rest ih =>
    simp only [LMonoTys.freeVars_of_cons, List.mem_append] at hv
    cases hv with
    | inl hmem => exact h ty (.head _) hmem
    | inr hmem => exact ih (fun t ht => h t (.tail _ ht)) hmem

/-- Each element's free vars are a subset of the whole list's free vars. -/
theorem LMonoTys.freeVars_mem_subset
    {ty : LMonoTy} {tys : List LMonoTy}
    (ht : ty ∈ tys)
    : LMonoTy.freeVars ty ⊆ LMonoTys.freeVars tys := by
  induction tys with
  | nil => contradiction
  | cons x rest ih =>
    simp only [LMonoTys.freeVars_of_cons]
    grind

/-- If `v ∈ LMonoTys.freeVars tys`, then some element of `tys` contains `v`. -/
theorem LMonoTys.freeVars_exists
    {v : TyIdentifier} {tys : List LMonoTy}
    (hv : v ∈ LMonoTys.freeVars tys)
    : ∃ ty, ty ∈ tys ∧ v ∈ LMonoTy.freeVars ty := by
  induction tys with
  | nil => simp [LMonoTys.freeVars] at hv
  | cons ty rest ih =>
    simp only [LMonoTys.freeVars_of_cons, List.mem_append] at hv
    cases hv with
    | inl h => exact ⟨ty, .head _, h⟩
    | inr h => obtain ⟨t, ht, htv⟩ := ih h; exact ⟨t, .tail _ ht, htv⟩

/-! ## Type substitution agreement lemmas

These lemmas establish that if two substitutions produce the same result on a
type, they must agree on all free variables of that type — and conversely, if
they agree on all free variables, they produce the same result. -/

/-- If two substitutions produce the same result on a type `ty`, then they
agree on every free variable of `ty` (in the sense of producing the same
substitution result on that variable). -/
theorem subst_eq_implies_agree_on_freeVars
    {S₁ S₂ : Subst}
    {ty : LMonoTy}
    (h : LMonoTy.subst S₁ ty = LMonoTy.subst S₂ ty)
    (v : TyIdentifier)
    (hv : v ∈ LMonoTy.freeVars ty)
    : LMonoTy.subst S₁ (.ftvar v) = LMonoTy.subst S₂ (.ftvar v) := by
  induction ty with
  | ftvar x =>
    simp only [LMonoTy.freeVars, List.mem_singleton] at hv
    subst hv; exact h
  | bitvec n =>
    simp [LMonoTy.freeVars] at hv
  | tcons name args ih =>
    simp only [LMonoTy.subst_unfold] at h
    simp only [LMonoTy.freeVars] at hv
    have h_args := LMonoTy.tcons.inj h |>.2
    -- v ∈ freeVars of some ty ∈ args; find it and apply IH
    have h_map_eq := List.map_eq_map_iff.mp h_args
    have ⟨ty, ht, hv_ty⟩ := LMonoTys.freeVars_exists hv
    exact ih ty ht (h_map_eq ty ht) hv_ty

/-- If two substitutions agree on all free variables of `ty` (in the sense of
producing the same substitution result), then they produce the same result
on `ty`. -/
theorem agree_on_freeVars_implies_subst_eq
    {S₁ S₂ : Subst}
    {ty : LMonoTy}
    (h : ∀ v, v ∈ LMonoTy.freeVars ty →
      LMonoTy.subst S₁ (.ftvar v) = LMonoTy.subst S₂ (.ftvar v))
    : LMonoTy.subst S₁ ty = LMonoTy.subst S₂ ty := by
  induction ty with
  | ftvar v =>
    exact h v (by simp [LMonoTy.freeVars])
  | bitvec n =>
    simp only [LMonoTy.subst_unfold]
  | tcons name args ih =>
    simp only [LMonoTy.subst_unfold]
    congr 1
    simp only [LMonoTy.freeVars] at h
    exact List.map_eq_map_iff.mpr fun ty ht =>
      ih ty ht fun v hv => h v (LMonoTys.freeVars_mem_subset ht hv)

/-- List version: if two substitutions agree on all free variables of every
type in a list, then mapping `subst` over the list produces the same result. -/
theorem agree_on_freeVars_implies_subst_eq_list
    {S₁ S₂ : Subst}
    {tys : List LMonoTy}
    (h : ∀ v, v ∈ LMonoTys.freeVars tys →
      LMonoTy.subst S₁ (.ftvar v) = LMonoTy.subst S₂ (.ftvar v))
    : tys.map (LMonoTy.subst S₁) = tys.map (LMonoTy.subst S₂) :=
  List.map_eq_map_iff.mpr fun _ ht =>
    agree_on_freeVars_implies_subst_eq fun v hv =>
      h v (LMonoTys.freeVars_mem_subset ht hv)

/-- Free vars of `f.inputs.map Prod.snd` are contained in `f.typeArgs`
for a well-formed function. -/
theorem freeVars_map_snd_subset_typeArgs
    {T : LExprParams} {f : LFunc T}
    (h_wf : LFuncWF f)
    {v : TyIdentifier}
    (hv : v ∈ LMonoTys.freeVars (f.inputs.map Prod.snd))
    : v ∈ f.typeArgs := by
  rw [← ListMap.values_eq_map_snd] at hv
  exact LMonoTys.freeVars_subset (fun ty ht => h_wf.inputs_typevars_in_typeArgs ty ht) hv

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
  -- Step 1: S₁ and S₂ agree on all v ∈ freeVars f.output
  have h_agree_output := subst_eq_implies_agree_on_freeVars h_output_eq
  -- Step 2: S₁ and S₂ agree on all v ∈ f.typeArgs
  have h_agree_typeArgs : ∀ v, v ∈ f.typeArgs →
      LMonoTy.subst S₁ (.ftvar v) = LMonoTy.subst S₂ (.ftvar v) :=
    fun v hv => h_agree_output v (h_output_covers v hv)
  -- Step 3+4: Apply agree_on_freeVars_implies_subst_eq_list
  apply agree_on_freeVars_implies_subst_eq_list
  intro v hv
  apply h_agree_typeArgs
  exact freeVars_map_snd_subset_typeArgs h_wf hv

/-- `callOfLFunc` only returns functions that are members of the factory's array. -/
theorem Factory.callOfLFunc_mem' {F : @Factory T} {e : LExpr T.mono} {callee args fn} :
    F.callOfLFunc e = some (callee, args, fn) → fn ∈ F.toArray := by
  intro hcall
  obtain ⟨_, _, _, _, h_get⟩ := Factory.callOfLFunc_getElem? hcall
  exact Factory.getElem?_is_some_implies_mem h_get

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
    (h_args₁ : List.Forall₂ (LExpr.HasTypeA []) args₁ argTys₁)
    (h_args₂ : List.Forall₂ (LExpr.HasTypeA []) args₂ argTys₂)
    (hoc₁ : OpsConsistent F e₁) (hoc₂ : OpsConsistent F e₂)
    (hfwf : FactoryWF F)
    (h_output_covers : ∀ v, v ∈ fn.typeArgs → v ∈ LMonoTy.freeVars fn.output)
    (hcallee₁ : ∃ m n, callee₁ = .op m n (some (LMonoTy.mkArrow' τ argTys₁)))
    (hcallee₂ : ∃ m n, callee₂ = .op m n (some (LMonoTy.mkArrow' τ argTys₂)))
    : argTys₁ = argTys₂ := by
  -- Step 1: Extract type substitutions from OpsConsistent
  have ⟨tySubst₁, _, hty_op₁⟩ := OpsConsistent_callOfLFunc hoc₁ hcall₁
  have ⟨tySubst₂, _, hty_op₂⟩ := OpsConsistent_callOfLFunc hoc₂ hcall₂
  -- Step 2: Connect callee shape to ty_op
  obtain ⟨m₁, n₁, hcallee₁_eq⟩ := hcallee₁
  obtain ⟨m₂, n₂, hcallee₂_eq⟩ := hcallee₂
  have htyop₁ := hty_op₁ m₁ n₁ (LMonoTy.mkArrow' τ argTys₁) hcallee₁_eq
  have htyop₂ := hty_op₂ m₂ n₂ (LMonoTy.mkArrow' τ argTys₂) hcallee₂_eq
  -- Step 3: Rewrite using subst_mkArrow'
  rw [subst_mkArrow'] at htyop₁ htyop₂
  -- Step 4: Apply mkArrow'_injective to get τ = fn.output.subst Sᵢ and argTysᵢ = ...
  have hlen₁ : argTys₁.length = ((fn.inputs.map Prod.snd).map (LMonoTy.subst tySubst₁)).length := by
    simp only [List.length_map]
    have := h_args₁.length_eq.symm.trans (Factory.callOfLFunc_arity hcall₁)
    omega
  have hlen₂ : argTys₂.length = ((fn.inputs.map Prod.snd).map (LMonoTy.subst tySubst₂)).length := by
    simp only [List.length_map]
    have := h_args₂.length_eq.symm.trans (Factory.callOfLFunc_arity hcall₂)
    omega
  have ⟨hτ₁, hargs₁_eq⟩ := LMonoTy.mkArrow'_injective hlen₁ htyop₁
  have ⟨hτ₂, hargs₂_eq⟩ := LMonoTy.mkArrow'_injective hlen₂ htyop₂
  -- Step 5: fn.output.subst tySubst₁ = fn.output.subst tySubst₂ (both = τ)
  have h_output_eq : LMonoTy.subst tySubst₁ fn.output = LMonoTy.subst tySubst₂ fn.output :=
    hτ₁.symm.trans hτ₂
  -- Step 6: Apply constr_same_output_implies_same_argTys
  have hfn_mem := Factory.callOfLFunc_mem' hcall₁
  have h_wf := hfwf.lfuncs_wf fn hfn_mem
  have h_same := constr_same_output_implies_same_argTys h_wf h_output_eq h_output_covers
  -- Step 7: Conclude
  rw [hargs₁_eq, hargs₂_eq, h_same]

/-- For ADT constructors (as witnessed by `ConstrWellFormed`), all type
arguments appear as free variables in the output type. This derives the
`h_output_covers` hypothesis needed by `constr_callOfLFunc_argTys_eq`
from `ConstrWellFormed`. -/
theorem constrFunc_output_covers_typeArgs
    {T : LExprParams}
    {tf : @TypeFactory T.IDMeta}
    {F : @Factory T}
    {fn : LFunc T}
    (hcwf : Factory.ConstrWellFormed F tf)
    (hfn_mem : fn ∈ F.toArray)
    (hconstr : fn.isConstr = true)
    : ∀ v, v ∈ fn.typeArgs → v ∈ LMonoTy.freeVars fn.output := by
  have ⟨d, _, c, _, hfn_eq⟩ := hcwf fn hfn_mem hconstr
  subst hfn_eq
  intro v hv
  unfold constrFunc at hv ⊢
  simp only at hv ⊢
  -- hv : v ∈ d.typeArgs, goal: v ∈ (dataDefault d).freeVars
  unfold dataDefault data at *
  simp only [LMonoTy.freeVars]
  -- Goal: v ∈ LMonoTys.freeVars (d.typeArgs.map .ftvar), with hv : v ∈ d.typeArgs
  have : ∀ (l : List TyIdentifier), v ∈ l → v ∈ LMonoTys.freeVars (l.map .ftvar) := by
    intro l hl
    induction l with
    | nil => contradiction
    | cons x xs ih =>
      simp only [List.map, LMonoTys.freeVars_of_cons, LMonoTy.freeVars, List.mem_append,
                 List.mem_cons] at hl ⊢
      cases hl with
      | inl h => left; exact Or.inl h
      | inr h => right; exact ih h
  exact this d.typeArgs hv

/-- Corollary: `constr_callOfLFunc_argTys_eq` with `ConstrWellFormed` instead
of the explicit `h_output_covers` hypothesis. -/
theorem constr_callOfLFunc_argTys_eq'
    {T : LExprParams} [DecidableEq T.IDMeta] [Inhabited T.mono.base.IDMeta]
    {F : @Factory T} {tf : @TypeFactory T.IDMeta}
    {e₁ e₂ : LExpr T.mono} {τ : LMonoTy}
    {callee₁ callee₂ : LExpr T.mono}
    {args₁ args₂ : List (LExpr T.mono)} {fn : LFunc T}
    {argTys₁ argTys₂ : List LMonoTy}
    (hcall₁ : Factory.callOfLFunc F e₁ = some (callee₁, args₁, fn))
    (hcall₂ : Factory.callOfLFunc F e₂ = some (callee₂, args₂, fn))
    (h_args₁ : List.Forall₂ (LExpr.HasTypeA []) args₁ argTys₁)
    (h_args₂ : List.Forall₂ (LExpr.HasTypeA []) args₂ argTys₂)
    (hoc₁ : OpsConsistent F e₁) (hoc₂ : OpsConsistent F e₂)
    (hfwf : FactoryWF F)
    (hcwf : Factory.ConstrWellFormed F tf)
    (hconstr : fn.isConstr = true)
    (hcallee₁ : ∃ m n, callee₁ = .op m n (some (LMonoTy.mkArrow' τ argTys₁)))
    (hcallee₂ : ∃ m n, callee₂ = .op m n (some (LMonoTy.mkArrow' τ argTys₂)))
    : argTys₁ = argTys₂ :=
  constr_callOfLFunc_argTys_eq hcall₁ hcall₂ h_args₁ h_args₂ hoc₁ hoc₂ hfwf
    (constrFunc_output_covers_typeArgs hcwf (Factory.callOfLFunc_mem' hcall₁) hconstr)
    hcallee₁ hcallee₂

end Lambda
