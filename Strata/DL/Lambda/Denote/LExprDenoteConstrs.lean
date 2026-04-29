/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

import all Strata.DL.Lambda.Denote.CallOfLFuncDenote
import all Strata.DL.Lambda.Denote.LExprDenoteProps
import all Strata.DL.Lambda.LTyUnify
import all Strata.DL.Lambda.FactoryWF
import all Strata.DL.Lambda.TypeFactoryWF

/-!
## Datatype Constructor Properties

Typing and denotation results for ADT constructor applications.

- `constr_same_output_implies_same_argTys` — same output type implies same argument types
- `constr_callOfLFunc_argTys_eq` — constructor calls at the same result type have equal arg type lists
- `callOfLFunc_constr_disjoint_denote` — different constructors at the same type denote to different values
- `callOfLFunc_constr_injective_denote` — same constructor, equal denotation implies pointwise equal arguments
-/

namespace Lambda

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
  have hfn_mem := callOfLFunc_func_mem _ _ _ _ _ false hcall₁
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
  have h_ftvar_freeVars : ∀ (l : List TyIdentifier), v ∈ l → v ∈ LMonoTys.freeVars (l.map .ftvar) := by
    intro l hl
    induction l with
    | nil => contradiction
    | cons x xs ih =>
      simp only [List.map, LMonoTys.freeVars_of_cons, LMonoTy.freeVars, List.mem_append,
                 List.mem_cons] at hl ⊢
      cases hl with
      | inl h => left; exact Or.inl h
      | inr h => right; exact ih h
  exact h_ftvar_freeVars d.typeArgs hv

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
    (constrFunc_output_covers_typeArgs hcwf (callOfLFunc_func_mem _ _ _ _ _ false hcall₁) hconstr)
    hcallee₁ hcallee₂

/-- If two constructor applications with different constructor names are well-typed
at the same type, their denotations differ. -/
theorem callOfLFunc_constr_disjoint_denote
    {T : LExprParams} [DecidableEq T.IDMeta] [Inhabited T.mono.base.IDMeta]
    (tcInterp : TyConstrInterp) (opInterp : OpInterp tcInterp)
    (fvarVal : FreeVarVal T tcInterp) (vt : TyVarVal)
    {F : @Factory T} {tf : @TypeFactory T.IDMeta}
    {e₁ e₂ : LExpr T.mono} {τ : LMonoTy}
    {callee₁ callee₂ : LExpr T.mono}
    {args₁ args₂ : List (LExpr T.mono)}
    {f₁ f₂ : LFunc T.mono.base}
    (h₁ : LExpr.HasTypeA [] e₁ τ)
    (h₂ : LExpr.HasTypeA [] e₂ τ)
    (hcall₁ : Factory.callOfLFunc F e₁ = some (callee₁, args₁, f₁))
    (hcall₂ : Factory.callOfLFunc F e₂ = some (callee₂, args₂, f₂))
    (hconstr₁ : f₁.isConstr = true) (hconstr₂ : f₂.isConstr = true)
    (hdiffname : f₁.name.name ≠ f₂.name.name)
    (hoc₁ : OpsConsistent F e₁) (hoc₂ : OpsConsistent F e₂)
    (hfwf : FactoryWF F) (hcwf : Factory.ConstrWellFormed F tf)
    (htfwf : TypeFactoryWF tf)
    (hConstrIC : ConstrInterpConsistent tcInterp opInterp F)
    : LExpr.denote tcInterp opInterp fvarVal vt .nil e₁ τ h₁ ≠
      LExpr.denote tcInterp opInterp fvarVal vt .nil e₂ τ h₂ := by
  -- Decompose both denotations via callOfLFunc_denote
  obtain ⟨argTys₁, ty_op₁, m₁, name₁, h_args₁, hty_op₁, hcallee₁, hdenote₁⟩ :=
    callOfLFunc_denote tcInterp opInterp fvarVal vt hcall₁ h₁
  obtain ⟨argTys₂, ty_op₂, m₂, name₂, h_args₂, hty_op₂, hcallee₂, hdenote₂⟩ :=
    callOfLFunc_denote tcInterp opInterp fvarVal vt hcall₂ h₂
  subst hty_op₁; subst hty_op₂
  -- Connect names: name₁.name = f₁.name.name, name₂.name = f₂.name.name
  obtain ⟨_, fname₁, _, hcallee₁', hget₁⟩ := Factory.callOfLFunc_getElem? hcall₁
  obtain ⟨_, fname₂, _, hcallee₂', hget₂⟩ := Factory.callOfLFunc_getElem? hcall₂
  rw [hcallee₁] at hcallee₁'; cases hcallee₁'
  rw [hcallee₂] at hcallee₂'; cases hcallee₂'
  have hname₁ := Factory.getElem?_name hget₁
  have hname₂ := Factory.getElem?_name hget₂
  -- Rewrite denotations
  rw [hdenote₁, hdenote₂]
  rw [← hname₁, ← hname₂]
  -- Sort alignment for f₁
  obtain ⟨tySubst₁, _, htySubst₁⟩ := OpsConsistent_callOfLFunc hoc₁ hcall₁
  have hty_op_subst₁ := htySubst₁ m₁ name₁ (LMonoTy.mkArrow' τ argTys₁) hcallee₁
  rw [subst_mkArrow'] at hty_op_subst₁
  have hlen₁ : argTys₁.length = ((f₁.inputs.map Prod.snd).map (LMonoTy.subst tySubst₁)).length := by
    simp only [List.length_map]
    exact h_args₁.length_eq.symm.trans (Factory.callOfLFunc_arity hcall₁)
  have ⟨hτ_eq₁, hargTys_eq₁⟩ := LMonoTy.mkArrow'_injective hlen₁ hty_op_subst₁
  let vt'₁ : TyVarVal := fun x => match tySubst₁.find? x with
    | some t => LMonoTy.substTyVars vt t | none => vt x
  have h_outputSort_eq₁ : LMonoTy.substTyVars vt τ = LMonoTy.substTyVars vt'₁ f₁.output := by
    rw [hτ_eq₁]; exact substTyVars_subst vt tySubst₁ f₁.output
  have h_inputSorts_eq₁ : argTys₁.map (LMonoTy.substTyVars vt) =
      (f₁.inputs.map Prod.snd).map (LMonoTy.substTyVars vt'₁) := by
    rw [hargTys_eq₁]; simp only [List.map_map]
    congr 1; funext ⟨_, ty⟩
    exact substTyVars_subst vt tySubst₁ ty
  -- Sort alignment for f₂
  obtain ⟨tySubst₂, _, htySubst₂⟩ := OpsConsistent_callOfLFunc hoc₂ hcall₂
  have hty_op_subst₂ := htySubst₂ m₂ name₂ (LMonoTy.mkArrow' τ argTys₂) hcallee₂
  rw [subst_mkArrow'] at hty_op_subst₂
  have hlen₂ : argTys₂.length = ((f₂.inputs.map Prod.snd).map (LMonoTy.subst tySubst₂)).length := by
    simp only [List.length_map]
    exact h_args₂.length_eq.symm.trans (Factory.callOfLFunc_arity hcall₂)
  have ⟨hτ_eq₂, hargTys_eq₂⟩ := LMonoTy.mkArrow'_injective hlen₂ hty_op_subst₂
  let vt'₂ : TyVarVal := fun x => match tySubst₂.find? x with
    | some t => LMonoTy.substTyVars vt t | none => vt x
  have h_outputSort_eq₂ : LMonoTy.substTyVars vt τ = LMonoTy.substTyVars vt'₂ f₂.output := by
    rw [hτ_eq₂]; exact substTyVars_subst vt tySubst₂ f₂.output
  have h_inputSorts_eq₂ : argTys₂.map (LMonoTy.substTyVars vt) =
      (f₂.inputs.map Prod.snd).map (LMonoTy.substTyVars vt'₂) := by
    rw [hargTys_eq₂]; simp only [List.map_map]
    congr 1; funext ⟨_, ty⟩
    exact substTyVars_subst vt tySubst₂ ty
  -- Both constructors belong to the same datatype (outputs match after substitution)
  have hmem₁ := callOfLFunc_func_mem _ _ _ _ _ false hcall₁
  have hmem₂ := callOfLFunc_func_mem _ _ _ _ _ false hcall₂
  obtain ⟨d₁, hd₁_mem, c₁, _, hf₁_eq⟩ := hcwf f₁ hmem₁ hconstr₁
  obtain ⟨d₂, hd₂_mem, c₂, _, hf₂_eq⟩ := hcwf f₂ hmem₂ hconstr₂
  have ho₁ : f₁.output = dataDefault d₁ := by subst hf₁_eq; rfl
  have ho₂ : f₂.output = dataDefault d₂ := by subst hf₂_eq; rfl
  have hτ_tcons₁ : τ = .tcons d₁.name (LMonoTys.subst tySubst₁ (d₁.typeArgs.map .ftvar)) := by
    rw [hτ_eq₁, ho₁]; unfold dataDefault data; rw [LMonoTy.subst_tcons]
  have hτ_tcons₂ : τ = .tcons d₂.name (LMonoTys.subst tySubst₂ (d₂.typeArgs.map .ftvar)) := by
    rw [hτ_eq₂, ho₂]; unfold dataDefault data; rw [LMonoTy.subst_tcons]
  have hd_name : d₁.name = d₂.name := by
    have h_tcons_eq := hτ_tcons₁.symm.trans hτ_tcons₂
    exact LMonoTy.tcons.inj h_tcons_eq |>.1
  have hd_eq : d₁ = d₂ := htfwf.eq_of_name_eq hd₁_mem hd₂_mem hd_name
  subst hd_eq
  have h_same_output : f₁.output = f₂.output := by rw [ho₁, ho₂]
  -- Since outputs agree, tySubst₁ and tySubst₂ agree on f₂'s types
  have h_subst_output_eq : LMonoTy.subst tySubst₁ f₂.output = LMonoTy.subst tySubst₂ f₂.output := by grind
  have h_subst_inputs_eq := constr_same_output_implies_same_argTys
    (hfwf.lfuncs_wf f₂ hmem₂) h_subst_output_eq
    (constrFunc_output_covers_typeArgs hcwf hmem₂ hconstr₂)
  -- Apply constr_disjoint with vt'₁
  have hdisj := hConstrIC.constr_disjoint f₁ f₂ hmem₁ hmem₂ hconstr₁ hconstr₂ hdiffname vt'₁
  -- Rewrite f₂'s sort equalities in terms of vt'₁ (using h_subst_inputs_eq)
  have hargTys_eq₂' : argTys₂ = (f₂.inputs.map Prod.snd).map (LMonoTy.subst tySubst₁) := by
    rw [hargTys_eq₂, h_subst_inputs_eq]
  have h_inputSorts_eq₂_vt1 : argTys₂.map (LMonoTy.substTyVars vt) =
      (f₂.inputs.map Prod.snd).map (LMonoTy.substTyVars vt'₁) := by
    rw [hargTys_eq₂']; simp only [List.map_map]
    congr 1; funext ⟨_, ty⟩
    exact substTyVars_subst vt tySubst₁ ty
  have h_outputSort_eq₂_vt1 : LMonoTy.substTyVars vt τ = LMonoTy.substTyVars vt'₁ f₂.output := by
    rw [h_outputSort_eq₁, h_same_output]
  -- Convert goal sorts to fullSort form via applyArgs_cast_eq
  have hvals₁ : f₁.inputs.values = f₁.inputs.map Prod.snd := ListMap.values_eq_map_snd f₁.inputs
  have hvals₂ : f₂.inputs.values = f₂.inputs.map Prod.snd := ListMap.values_eq_map_snd f₂.inputs
  have h₁_sort : LMonoTy.substTyVars vt (LMonoTy.mkArrow' τ argTys₁) =
      LSort.mkArrow (LMonoTy.substTyVars vt'₁ f₁.output)
        (f₁.inputs.values.map (LMonoTy.substTyVars vt'₁)) := by
    rw [substTyVars_mkArrow', h_outputSort_eq₁, h_inputSorts_eq₁, hvals₁]
  have h₂_sort : LMonoTy.substTyVars vt (LMonoTy.mkArrow' τ argTys₂) =
      LSort.mkArrow (LMonoTy.substTyVars vt'₁ f₂.output)
        (f₂.inputs.values.map (LMonoTy.substTyVars vt'₁)) := by
    rw [substTyVars_mkArrow', h_outputSort_eq₂_vt1, h_inputSorts_eq₂_vt1, hvals₂]
  have h_output_sorts_eq : LMonoTy.substTyVars vt'₁ f₁.output = LMonoTy.substTyVars vt'₁ f₂.output := by
    rw [h_same_output]
  let dArgs₁ := denoteArgs tcInterp opInterp fvarVal vt .nil args₁ argTys₁ h_args₁
  let dArgs₂ := denoteArgs tcInterp opInterp fvarVal vt .nil args₂ argTys₂ h_args₂
  have h_convert₁ := applyArgs_cast_eq
    (substTyVars_mkArrow' vt τ argTys₁) h₁_sort
    (hvals₁ ▸ h_inputSorts_eq₁) h_outputSort_eq₁
    (opInterp f₁.name.name (LMonoTy.substTyVars vt (LMonoTy.mkArrow' τ argTys₁)))
    dArgs₁
  have h_convert₂ := applyArgs_cast_eq
    (substTyVars_mkArrow' vt τ argTys₂) h₂_sort
    (hvals₂ ▸ h_inputSorts_eq₂_vt1) h_outputSort_eq₂_vt1
    (opInterp f₂.name.name (LMonoTy.substTyVars vt (LMonoTy.mkArrow' τ argTys₂)))
    dArgs₂
  grind

/-- If two applications of the same constructor are well-typed at the same type
and denote to equal values, then their arguments denote pairwise equal. -/
theorem callOfLFunc_constr_injective_denote
    {T : LExprParams} [DecidableEq T.IDMeta] [Inhabited T.mono.base.IDMeta]
    (tcInterp : TyConstrInterp) (opInterp : OpInterp tcInterp)
    (fvarVal : FreeVarVal T tcInterp) (vt : TyVarVal)
    {F : @Factory T} {tf : @TypeFactory T.IDMeta}
    {e₁ e₂ : LExpr T.mono} {τ : LMonoTy}
    {callee₁ callee₂ : LExpr T.mono}
    {args₁ args₂ : List (LExpr T.mono)}
    {f : LFunc T.mono.base}
    (h₁ : LExpr.HasTypeA [] e₁ τ)
    (h₂ : LExpr.HasTypeA [] e₂ τ)
    (hcall₁ : Factory.callOfLFunc F e₁ = some (callee₁, args₁, f))
    (hcall₂ : Factory.callOfLFunc F e₂ = some (callee₂, args₂, f))
    (hconstr : f.isConstr = true)
    (hoc₁ : OpsConsistent F e₁) (hoc₂ : OpsConsistent F e₂)
    (hfwf : FactoryWF F) (hcwf : Factory.ConstrWellFormed F tf)
    (hConstrIC : ConstrInterpConsistent tcInterp opInterp F)
    (heq : LExpr.denote tcInterp opInterp fvarVal vt .nil e₁ τ h₁ =
           LExpr.denote tcInterp opInterp fvarVal vt .nil e₂ τ h₂)
    : ∀ (i : Nat) (a₁ a₂ : LExpr T.mono) (σ : LMonoTy),
        args₁[i]? = some a₁ → args₂[i]? = some a₂ →
        (ha₁ : LExpr.HasTypeA [] a₁ σ) → (ha₂ : LExpr.HasTypeA [] a₂ σ) →
        LExpr.denote tcInterp opInterp fvarVal vt .nil a₁ σ ha₁ =
        LExpr.denote tcInterp opInterp fvarVal vt .nil a₂ σ ha₂ := by
  -- Decompose both denotations via callOfLFunc_denote
  obtain ⟨argTys₁, ty_op₁, m₁, name₁, h_args₁, hty_op₁, hcallee₁, hdenote₁⟩ :=
    callOfLFunc_denote tcInterp opInterp fvarVal vt hcall₁ h₁
  obtain ⟨argTys₂, ty_op₂, m₂, name₂, h_args₂, hty_op₂, hcallee₂, hdenote₂⟩ :=
    callOfLFunc_denote tcInterp opInterp fvarVal vt hcall₂ h₂
  -- Get argTys₁ = argTys₂
  have hargTys : argTys₁ = argTys₂ :=
    constr_callOfLFunc_argTys_eq' hcall₁ hcall₂ h_args₁ h_args₂ hoc₁ hoc₂ hfwf hcwf hconstr
      ⟨m₁, name₁, hty_op₁ ▸ hcallee₁⟩
      ⟨m₂, name₂, hty_op₂ ▸ hcallee₂⟩
  subst hargTys
  subst hty_op₁; subst hty_op₂
  -- Connect names: name₁.name = name₂.name = f.name.name
  obtain ⟨_, fname₁, _, hcallee₁', hget₁⟩ := Factory.callOfLFunc_getElem? hcall₁
  obtain ⟨_, fname₂, _, hcallee₂', hget₂⟩ := Factory.callOfLFunc_getElem? hcall₂
  rw [hcallee₁] at hcallee₁'; cases hcallee₁'
  rw [hcallee₂] at hcallee₂'; cases hcallee₂'
  have hname₁ := Factory.getElem?_name hget₁  -- f.name.name = name₁.name
  have hname₂ := Factory.getElem?_name hget₂  -- f.name.name = name₂.name
  -- Rewrite heq using hdenote₁ and hdenote₂
  rw [hdenote₁, hdenote₂] at heq
  rw [← hname₁, ← hname₂] at heq
  -- Get OpsConsistent type substitution to connect argTys and f.inputs
  obtain ⟨tySubst₁, _, htySubst₁⟩ := OpsConsistent_callOfLFunc hoc₁ hcall₁
  have hty_op_subst := htySubst₁ m₁ name₁ (LMonoTy.mkArrow' τ argTys₁) hcallee₁
  rw [subst_mkArrow'] at hty_op_subst
  have hlen : argTys₁.length = ((f.inputs.map Prod.snd).map (LMonoTy.subst tySubst₁)).length := by
    simp only [List.length_map]
    exact h_args₁.length_eq.symm.trans (Factory.callOfLFunc_arity hcall₁)
  have ⟨hτ_eq, hargTys_eq⟩ := LMonoTy.mkArrow'_injective hlen hty_op_subst
  -- Define vt' incorporating tySubst₁, prove sort equalities
  let vt' : TyVarVal := fun x => match tySubst₁.find? x with
    | some t => LMonoTy.substTyVars vt t | none => vt x
  have h_inputSorts_eq : argTys₁.map (LMonoTy.substTyVars vt) =
      (f.inputs.map Prod.snd).map (LMonoTy.substTyVars vt') := by
    rw [hargTys_eq]; simp only [List.map_map]
    congr 1; funext ⟨_, ty⟩
    exact substTyVars_subst vt tySubst₁ ty
  have h_outputSort_eq : LMonoTy.substTyVars vt τ = LMonoTy.substTyVars vt' f.output := by
    rw [hτ_eq]; exact substTyVars_subst vt tySubst₁ f.output
  -- Apply constr_injective
  have hmem := callOfLFunc_func_mem _ _ _ _ _ false hcall₁
  have hinj := hConstrIC.constr_injective f hmem hconstr vt'
  have hvals : f.inputs.values = f.inputs.map Prod.snd := ListMap.values_eq_map_snd f.inputs
  let dArgs₁ := denoteArgs tcInterp opInterp fvarVal vt .nil args₁ argTys₁ h_args₁
  let dArgs₂ := denoteArgs tcInterp opInterp fvarVal vt .nil args₂ argTys₁ h_args₂
  -- Convert heq to fullSort form via applyArgs_cast_eq
  have h₂ : LMonoTy.substTyVars vt (LMonoTy.mkArrow' τ argTys₁) =
      LSort.mkArrow (LMonoTy.substTyVars vt' f.output)
        (f.inputs.values.map (LMonoTy.substTyVars vt')) := by
    rw [substTyVars_mkArrow', h_outputSort_eq, h_inputSorts_eq, hvals]
  have h_convert₁ := applyArgs_cast_eq
    (substTyVars_mkArrow' vt τ argTys₁) h₂
    (hvals ▸ h_inputSorts_eq) h_outputSort_eq
    (opInterp f.name.name (LMonoTy.substTyVars vt (LMonoTy.mkArrow' τ argTys₁)))
    dArgs₁
  have h_convert₂ := applyArgs_cast_eq
    (substTyVars_mkArrow' vt τ argTys₁) h₂
    (hvals ▸ h_inputSorts_eq) h_outputSort_eq
    (opInterp f.name.name (LMonoTy.substTyVars vt (LMonoTy.mkArrow' τ argTys₁)))
    dArgs₂
  -- Prove denoteArgs are equal via constr_injective + cast manipulation
  have hdArgs_cast_eq : HList.cast (hvals ▸ h_inputSorts_eq) dArgs₁ =
      HList.cast (hvals ▸ h_inputSorts_eq) dArgs₂ := by
    apply hinj
    have hlhs : SortDenote.applyArgs tcInterp
        (cast (congrArg (SortDenote tcInterp) (substTyVars_mkArrow' vt τ argTys₁))
          (opInterp f.name.name (LMonoTy.substTyVars vt (LMonoTy.mkArrow' τ argTys₁))))
        dArgs₁ =
      cast (congrArg (SortDenote tcInterp) h_outputSort_eq.symm)
        (SortDenote.applyArgs tcInterp
          (cast (congrArg (SortDenote tcInterp) h₂)
            (opInterp f.name.name (LMonoTy.substTyVars vt (LMonoTy.mkArrow' τ argTys₁))))
          (HList.cast (hvals ▸ h_inputSorts_eq) dArgs₁)) := h_convert₁
    have hrhs : SortDenote.applyArgs tcInterp
        (cast (congrArg (SortDenote tcInterp) (substTyVars_mkArrow' vt τ argTys₁))
          (opInterp f.name.name (LMonoTy.substTyVars vt (LMonoTy.mkArrow' τ argTys₁))))
        dArgs₂ =
      cast (congrArg (SortDenote tcInterp) h_outputSort_eq.symm)
        (SortDenote.applyArgs tcInterp
          (cast (congrArg (SortDenote tcInterp) h₂)
            (opInterp f.name.name (LMonoTy.substTyVars vt (LMonoTy.mkArrow' τ argTys₁))))
          (HList.cast (hvals ▸ h_inputSorts_eq) dArgs₂)) := h_convert₂
    grind
  -- HList.cast is injective, so dArgs₁ = dArgs₂
  have hdArgs_eq : dArgs₁ = dArgs₂ := by
    have h_cast_def₁ : HList.cast (hvals ▸ h_inputSorts_eq) dArgs₁ = (hvals ▸ h_inputSorts_eq) ▸ dArgs₁ := rfl
    have h_cast_def₂ : HList.cast (hvals ▸ h_inputSorts_eq) dArgs₂ = (hvals ▸ h_inputSorts_eq) ▸ dArgs₂ := rfl
    rw [h_cast_def₁, h_cast_def₂] at hdArgs_cast_eq
    exact cast_injective (congrArg (HList (SortDenote tcInterp)) (hvals ▸ h_inputSorts_eq)) (by grind)
  -- Extract pointwise denote equality from denoteArgs equality
  intro i a₁ a₂ σ ha₁ ha₂ hta₁ hta₂
  obtain ⟨σ₁, hσ₁, hta₁'⟩ := List.Forall₂.getElem?_some h_args₁ ha₁
  have hσ_eq : σ₁ = σ := HasTypeA_unique hta₁' hta₁
  subst hσ_eq
  exact denoteArgs_eq_implies_denote_eq tcInterp opInterp fvarVal vt .nil
    h_args₁ h_args₂ hdArgs_eq i a₁ a₂ σ₁ ha₁ ha₂ hσ₁ hta₁ hta₂

end Lambda
