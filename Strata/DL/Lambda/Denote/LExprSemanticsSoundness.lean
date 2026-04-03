/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

import Strata.DL.Lambda.Denote.LExprAnnotated
import all Strata.DL.Lambda.Denote.LExprDenote
import all Strata.DL.Lambda.Semantics
import Strata.DL.Lambda.Denote.HList
import all Strata.DL.Lambda.Denote.LExprDenoteProps
import all Strata.DL.Lambda.Denote.LExprDenoteSubst
import all Strata.DL.Lambda.Denote.CallOfLFuncDenote

namespace Lambda

variable {T : LExprParams}
variable (tcInterp : TyConstrInterp)
variable (opInterp : OpInterp tcInterp)
variable (fvarVal : FreeVarVal T tcInterp)
variable (vt : TyVarVal)

/-! ### Helper lemmas -/

/-- `callOfLFunc` only returns functions that are members of the factory. -/
theorem Factory.callOfLFunc_mem {F : @Factory T} {e : LExpr T.mono} {callee args fn} :
    F.callOfLFunc e = some (callee, args, fn) → fn ∈ F := by
  simp [Factory.callOfLFunc]
  cases getLFuncCall e with | mk op args' =>
  simp; cases op <;> simp
  rename_i m name ty
  cases h : F.getFactoryLFunc name.name <;> simp
  rename_i func
  cases args'.length == func.inputs.length <;> simp
  intro _ _ h_fn; subst h_fn
  exact Array.mem_of_find?_eq_some h

/-! ### Weakening and context-irrelevance for lcAt 0 expressions -/

-- omit [DecidableEq T.Metadata] [DecidableEq T.Identifier] in
-- theorem eql_rewrite
--   {F : @Factory T}
--   {e₁ e₂ : LExpr T.mono}
--   (hv₁ : LExpr.isCanonicalValue F e₁)
--   (hv₂ : LExpr.isCanonicalValue F e₂):
--   LExpr.eql F e₁ e₂ hv₁ hv₂ = LExpr.eqModuloTypes e₁ e₂ := by
--   unfold LExpr.eql; split <;> grind
section -- [DecidableEq T.IDMeta] [Inhabited T.mono.base.IDMeta]
variable [DecidableEq T.IDMeta] [Inhabited T.mono.base.IDMeta]

theorem eqModuloMeta_true_implies_denote_eq
    {e₁ e₂ : LExpr T.mono} {τ : LMonoTy}
    (h₁ : LExpr.HasTypeA [] e₁ τ)
    (h₂ : LExpr.HasTypeA [] e₂ τ)
    (heql : LExpr.eqModuloMeta e₁ e₂ = true)
    : LExpr.denote tcInterp opInterp fvarVal vt .nil e₁ τ h₁ =
      LExpr.denote tcInterp opInterp fvarVal vt .nil e₂ τ h₂ := by
    unfold LExpr.eqModuloMeta at heql
    -- Lean is confused by BEq and DecidableEq
    have heq: (e₁.eraseMetadata = e₂.eraseMetadata) := by
      unfold BEq.beq instBEqLExprOfIdentifier at heql
      simp at heql
      rw[LExpr.beq_eq] at heql
      exact heql
    rw[denote_replaceMetadata _ _ _ _ .nil (fun _ => ()) h₁]
    rw[denote_replaceMetadata _ _ _ _ .nil (fun _ => ()) h₂]
    unfold LExpr.eraseMetadata at heq
    generalize replaceMetadata_HasTypeA (fun _ => ()) h₁ = ht₁
    generalize e₁.replaceMetadata (fun _ => ()) = e₁' at *
    subst heq
    rfl


/-- For canonical values, if syntactic equality (`eql`) returns true, then the
denotations are equal. -/
theorem eql_true_implies_denote_eq
    {F : @Factory T}
    {e₁ e₂ : LExpr T.mono} {τ : LMonoTy}
    (h₁ : LExpr.HasTypeA [] e₁ τ)
    (h₂ : LExpr.HasTypeA [] e₂ τ)
    (heql : LExpr.eql F e₁ e₂ = some true)
    : LExpr.denote tcInterp opInterp fvarVal vt .nil e₁ τ h₁ =
      LExpr.denote tcInterp opInterp fvarVal vt .nil e₂ τ h₂ := by
    sorry

/-- For binder-free canonical values, if syntactic equality (`eql`) returns
false, then the denotations are not equal. The `containsBinder = false`
precondition is essential: for expressions with binders, structural inequality
does not imply semantic inequality (e.g., `λ (if #true then %0 else %0)` vs
`λ %0`). -/
theorem eql_false_implies_denote_ne
    {F : @Factory T}
    {e₁ e₂ : LExpr T.mono} {τ : LMonoTy}
    (h₁ : LExpr.HasTypeA [] e₁ τ)
    (h₂ : LExpr.HasTypeA [] e₂ τ)
    (heql : LExpr.eql F e₁ e₂ = some false)
    : LExpr.denote tcInterp opInterp fvarVal vt .nil e₁ τ h₁ ≠
      LExpr.denote tcInterp opInterp fvarVal vt .nil e₂ τ h₂ := by
  sorry

theorem zip_map_fst_eq {α β: Type} (l1: List α) (l2: List β) :
  List.length l1 = List.length l2 →
  (l1.zip l2).map Prod.fst = l1 := by
  induction l1 generalizing l2 <;> cases l2 <;> simp_all

theorem zip_map_snd_eq{α β: Type} (l1: List α) (l2: List β) :
  List.length l1 = List.length l2 →
  (l1.zip l2).map Prod.snd = l2 := by
  induction l1 generalizing l2 <;> cases l2 <;> simp_all

theorem zip_map_fst_snd_eq {α β : Type} (l : List (α × β)) :
    (l.map Prod.fst).zip (l.map Prod.snd) = l := by
  induction l <;> simp_all

/-! ### Main theorem -/

/-- If `e₁` steps to `e₂` under a factory `F` and environment `env`, and both
are well-typed at the same type `τ`, then (given consistency of the factory and
environment with the semantic interpretations) they have the same denotation. -/
theorem Step.denote_preserved
    {F : @Factory T} {env : Env T}
    {e₁ e₂ : LExpr T.mono} {τ : LMonoTy}
    (hstep : Step F env e₁ e₂)
    (h₁ : LExpr.HasTypeA [] e₁ τ)
    (h₂ : LExpr.HasTypeA [] e₂ τ)
    (hF : Factory.InterpConsistent tcInterp opInterp F)
    (hFwt : Factory.WellTyped F)
    (hEnv : Env.InterpConsistent tcInterp opInterp env fvarVal)
    (hOps : OpsConsistent F e₁)
    : LExpr.denote tcInterp opInterp fvarVal vt .nil e₁ τ h₁ =
      LExpr.denote tcInterp opInterp fvarVal vt .nil e₂ τ h₂ := by
  induction hstep generalizing τ with
  | expand_fvar x e henv =>
    cases h₁ with
    | fvar => simp [LExpr.denote]; exact (hEnv vt x _ _ henv h₂).symm
  | beta e1 v2 eres hval heq =>
    subst heq
    cases h₁
    rename_i aty htyv2 htyabs
    cases htyabs with
    | abs =>
      rename_i h_body
      rw [denote_app .nil (.abs h_body) htyv2,
          denote_abs .nil h_body]
      exact (subst_denote tcInterp opInterp fvarVal vt h_body htyv2 h₂
              (HasTypeA_nil_lcAt htyv2)).symm
  | reduce_2 v1 e2 e2' hstep' ih =>
    cases h₁ with
    | app h_fn h_arg =>
      cases h₂ with
      | app h_fn' h_arg' =>
        have haty := HasTypeA_unique h_fn h_fn'
        cases haty
        rw [denote_app .nil h_fn h_arg,
            denote_app .nil h_fn' h_arg']
        congr 1
        rw[ih h_arg h_arg' hOps.2.2]
  | reduce_1 e1 e1' e2 hstep' ih =>
    cases h₁ with
    | app h_fn h_arg =>
      cases h₂ with
      | app h_fn' h_arg' =>
        have haty := HasTypeA_unique h_arg h_arg'
        subst haty
        rw [denote_app .nil h_fn h_arg,
            denote_app .nil h_fn' h_arg']
        congr 1
        rw[ih h_fn h_fn' hOps.2.1]
  | ite_reduce_then ethen eelse =>
    cases h₁ with
    | ite h_c h_t h_e =>
      rw [denote_ite .nil h_c h_t h_e]
      have hc: LExpr.denote tcInterp opInterp fvarVal vt .nil
          (.const _ (.boolConst true)) .bool h_c = true := by rfl
      rw [hc]; rfl
  | ite_reduce_else ethen eelse =>
    cases h₁ with
    | ite h_c h_t h_e =>
      rw [denote_ite .nil h_c h_t h_e]
      have hc : LExpr.denote tcInterp opInterp fvarVal vt .nil
          (.const _ (.boolConst false)) .bool h_c = false := by rfl
      rw [hc]; rfl
  | ite_reduce_cond econd econd' ethen eelse hstep' ih =>
    cases h₁ with
    | ite h_c h_t h_e =>
      cases h₂ with
      | ite h_c' h_t' h_e' =>
        rw [denote_ite .nil h_c h_t h_e,
            denote_ite .nil h_c' h_t' h_e']
        rw [ih h_c h_c' hOps.2.1]
  | ite_reduce_then_branch econd ethen ethen' eelse hstep' ih =>
    cases h₁ with
    | ite h_c h_t h_e =>
      cases h₂ with
      | ite h_c' h_t' h_e' =>
        rw [denote_ite .nil h_c h_t h_e,
            denote_ite .nil h_c' h_t' h_e']
        rw [ih h_t h_t' hOps.2.2.1]
  | ite_reduce_else_branch econd ethen eelse eelse' hstep' ih =>
    cases h₁ with
    | ite h_c h_t h_e =>
      cases h₂ with
      | ite h_c' h_t' h_e' =>
        rw [denote_ite .nil h_c h_t h_e,
            denote_ite .nil h_c' h_t' h_e']
        rw [ih h_e h_e' hOps.2.2.2]
  | eq_reduce_true e1 e2 heql =>
    cases h₁ with
    | eq h_1 h_2 =>
      rw [denote_eq_true .nil h_1 h_2 _
          (eql_true_implies_denote_eq tcInterp opInterp fvarVal vt h_1 h_2 heql)]
      rfl
  | eq_reduce_false e1 e2 heql =>
    cases h₁ with
    | eq h_1 h_2 =>
      rw [denote_eq_false .nil h_1 h_2 _
          (eql_false_implies_denote_ne tcInterp opInterp fvarVal vt
            h_1 h_2 heql)]
      rfl
  | eq_reduce_lhs e1 e1' e2 hstep' ih =>
    cases h₁ with
    | eq h_1 h_2 =>
      cases h₂ with
      | eq h_1' h_2' =>
        have hty := HasTypeA_unique h_2 h_2'; subst hty
        have ih_eq := ih h_1 h_1' hOps.2.1
        by_cases heq : LExpr.denote tcInterp opInterp fvarVal vt .nil e1 _ h_1 =
            LExpr.denote tcInterp opInterp fvarVal vt .nil e2 _ h_2
        · rw [denote_eq_true .nil h_1 h_2 _ heq,
              denote_eq_true .nil h_1' h_2' _
                (by rw [← ih_eq]; exact heq)]
        · rw [denote_eq_false .nil h_1 h_2 _ heq,
              denote_eq_false .nil h_1' h_2' _
                (by rw [← ih_eq]; exact heq)]
  | eq_reduce_rhs v1 e2 e2' hstep' ih =>
    cases h₁ with
    | eq h_1 h_2 =>
      cases h₂ with
      | eq h_1' h_2' =>
        have hty := HasTypeA_unique h_1 h_1'; subst hty
        have ih_eq := ih h_2 h_2' hOps.2.2
        by_cases heq : LExpr.denote tcInterp opInterp fvarVal vt .nil v1 _ h_1 =
            LExpr.denote tcInterp opInterp fvarVal vt .nil e2 _ h_2
        · rw [denote_eq_true .nil h_1 h_2 _ heq,
              denote_eq_true .nil h_1' h_2' _
                (by rw [← ih_eq]; exact heq)]
        · rw [denote_eq_false .nil h_1 h_2 _ heq,
              denote_eq_false .nil h_1' h_2' _
                (by rw [← ih_eq]; exact heq)]
  | expand_fn e callee fnbody new_body args fn tySubst hcall hbody htySubst heq =>
    -- Step 1: Decompose the call
    obtain ⟨argTys, ty_op, m, name, h_args, hty_op, h_callee_eq, h_denote_e⟩ :=
      callOfLFunc_denote tcInterp opInterp fvarVal vt hcall h₁
    -- Step 2: Extract from OpsConsistent
    obtain ⟨tySubst', htySubst', h_ty_op_eq⟩ := OpsConsistent_callOfLFunc hOps hcall
    rw [h_callee_eq] at htySubst htySubst'
    have : tySubst' = tySubst := Option.some.inj (htySubst'.symm.trans htySubst)
    subst this
    have h_ty_op_val := h_ty_op_eq m name ty_op h_callee_eq
    -- Step 3: Decompose into τ and argTys
    have h_subst_arrow := subst_mkArrow' tySubst' fn.output (fn.inputs.map Prod.snd)
    rw [h_subst_arrow] at h_ty_op_val
    rw [hty_op] at h_ty_op_val
    have h_len : argTys.length = ((fn.inputs.map Prod.snd).map (LMonoTy.subst tySubst')).length := by
      simp; exact h_args.length_eq.symm.trans (callOfLFunc_arity hcall)
    have ⟨h_τ_eq, h_argTys_eq⟩ := mkArrow'_injective h_len h_ty_op_val
    -- Step 4: Define vt'
    let vt' : TyVarVal := fun x => match tySubst'.find? x with
      | some t => LMonoTy.substTyVars vt t | none => vt x
    -- Step 5-6: Sort equalities
    have h_sorts_eq : argTys.map (LMonoTy.substTyVars vt) =
        (fn.inputs.map (fun (id, ty) => (id, LMonoTy.substTyVars vt' ty))).map Prod.snd := by
      rw [h_argTys_eq]; simp [List.map_map]
      congr 1; funext; intros a ty a_in
      exact substTyVars_subst vt tySubst' ty
    -- Step 7: Factory consistency
    have h_fn_mem : fn ∈ F := callOfLFunc_mem hcall
    have h_body_wt := (hFwt fn h_fn_mem fnbody hbody).1
    have h_annot := (hFwt fn h_fn_mem fnbody hbody).2
    have h_icb := hF.1 fn h_fn_mem fnbody hbody
    let bindings_vt' := fn.inputs.map (fun (id, ty) => (id, LMonoTy.substTyVars vt' ty))
    let da := denoteArgs tcInterp opInterp fvarVal vt .nil args argTys h_args
    have h_icb_inst := h_icb vt' fvarVal h_body_wt (HList.cast h_sorts_eq da)
    -- Step 8: Connect the two applyArgs calls
    have h_fn_name : fn.name.name = name.name := by
      obtain ⟨_, _, _, hc, hg⟩ := callOfLFunc_getFactoryLFunc hcall
      rw [h_callee_eq] at hc; cases hc
      exact getFactoryLFunc_name hg
    let inputSorts_vt' := bindings_vt'.map Prod.snd
    let fullSort_vt' := LSort.mkArrow (LMonoTy.substTyVars vt' fn.output) inputSorts_vt'
    have h_sort_connect : LMonoTy.substTyVars vt ty_op = fullSort_vt' := by
      have h_tv := h_ty_op_eq m name ty_op h_callee_eq
      rw [h_tv, substTyVars_subst vt tySubst' (fn.output.mkArrow' (fn.inputs.map Prod.snd)),
          substTyVars_mkArrow']
      congr 1
      simp [inputSorts_vt', bindings_vt', List.map_map]
      intros; rfl
    have h_ret_eq : LMonoTy.substTyVars vt' fn.output = LMonoTy.substTyVars vt τ := by
      rw [h_τ_eq]; exact (substTyVars_subst vt tySubst' fn.output).symm
    -- Step 8: Use applyArgs_cast_eq to connect h_denote_e with h_icb_inst
    have h_td : TyDenote tcInterp vt' fn.output = TyDenote tcInterp vt τ :=
      congrArg (SortDenote tcInterp) h_ret_eq
    -- Part A: denote e = cast h_td (denote vt' fnbody)
    have h_partA : LExpr.denote tcInterp opInterp fvarVal vt .nil e τ h₁ =
        cast h_td (LExpr.denote tcInterp opInterp
          (fvarVal.withArgs bindings_vt' (HList.cast h_sorts_eq da))
          vt' .nil fnbody fn.output h_body_wt) := by
      rw [h_denote_e]
      rw [← h_icb_inst, h_fn_name]
      subst hty_op
      have h := applyArgs_cast_eq
        (substTyVars_mkArrow' vt τ argTys) h_sort_connect
        h_sorts_eq h_ret_eq.symm
        (opInterp name.name (LMonoTy.substTyVars vt (τ.mkArrow' argTys))) da
      grind
    -- Part B: use denote_applySubst
    have h_applySubst_wt : LExpr.HasTypeA [] (fnbody.applySubst tySubst') (LMonoTy.subst tySubst' fn.output) :=
      applySubst_typeCheck tySubst' h_body_wt
    have h_td2 : TyDenote tcInterp vt (LMonoTy.subst tySubst' fn.output) = TyDenote tcInterp vt' fn.output := by
      rw [h_τ_eq] at h_td; exact h_td.symm
    have h_partB := denote_applySubst (tcInterp := tcInterp) (opInterp := opInterp)
      (fvarVal := fvarVal.withArgs bindings_vt' (HList.cast h_sorts_eq da))
      (rfl : vt' = fun x => match tySubst'.find? x with
        | some t => LMonoTy.substTyVars vt t | none => vt x)
      h_body_wt h_applySubst_wt h_td2
    -- h_partB : denote vt (applySubst tySubst' fnbody) ... = cast h_td2.symm (denote vt' fnbody ...)
    -- Derive: cast h_td2 (denote vt (applySubst ...)) = denote vt' fnbody
    have h_partB' : cast h_td2
        (LExpr.denote tcInterp opInterp
          (fvarVal.withArgs bindings_vt' (HList.cast h_sorts_eq da)) vt .nil
          (fnbody.applySubst tySubst') (LMonoTy.subst tySubst' fn.output) h_applySubst_wt) =
        LExpr.denote tcInterp opInterp
          (fvarVal.withArgs bindings_vt' (HList.cast h_sorts_eq da)) vt' .nil fnbody fn.output h_body_wt := by
      rw [h_partB]; simp [cast_cast, cast_eq]
    rw [h_partA, ← h_partB']
    simp only [cast_cast]
    -- Goal: cast _ (denote (withArgs ...) vt (applySubst tySubst' fnbody) (subst tySubst' fn.output)) = denote vt new_body τ h₂
    subst h_τ_eq heq
    simp only [cast_eq]
    -- Part C: use substFvarsLifting_denote
    have h_arity := callOfLFunc_arity hcall
    have h_keys_len : fn.inputs.keys.length = args.length := by
      rw [ListMap.keys_eq_map_fst]; simp [h_arity]
    have h_zip_fst : (fn.inputs.keys.zip args).map Prod.fst = fn.inputs.keys :=
      zip_map_fst_eq _ _ h_keys_len
    have h_zip_snd : (fn.inputs.keys.zip args).map Prod.snd = args :=
      zip_map_snd_eq _ _ h_keys_len
    have h_keys : (fn.inputs.keys.zip args).map Prod.fst = bindings_vt'.map Prod.fst := by
      rw [h_zip_fst]; simp [bindings_vt', List.map_map, ListMap.keys_eq_map_fst]
    have h_len : (fn.inputs.keys.zip args).length = bindings_vt'.length := by
      simp [List.length_zip, h_keys_len, bindings_vt']; grind
    have h_tys_len : argTys.length = (fn.inputs.keys.zip args).length := by
      rw [List.length_zip, h_keys_len, Nat.min_self]; grind
    have h_wt : List.Forall₂ (LExpr.HasTypeA []) ((fn.inputs.keys.zip args).map Prod.snd) argTys := by
      rw [h_zip_snd]; exact h_args
    have h_denotes : HList.cast h_sorts_eq da = HList.cast h_sorts_eq.symm.symm
        (denoteArgs tcInterp opInterp fvarVal vt .nil ((fn.inputs.keys.zip args).map Prod.snd) argTys h_wt) := by
      simp [h_zip_snd]; grind
    have h_annot_subst : fvars_annotated_by
        ((fn.inputs.keys.zip args).map Prod.fst |>.zip argTys) (fnbody.applySubst tySubst') := by
      rw [h_zip_fst, ListMap.keys_eq_map_fst, h_argTys_eq]
      have h_map_eq : (fn.inputs.map Prod.fst).zip (List.map (LMonoTy.subst tySubst') (fn.inputs.map Prod.snd)) =
          fn.inputs.map (fun (k, v) => (k, LMonoTy.subst tySubst' v)) := by
          rw[List.map_map]
          induction fn.inputs with
          | nil => rfl
          | cons h t ih => simp [ih]
      rw [h_map_eq]
      exact applySubst_fvars_annotated h_annot
    symm
    exact substFvarsLifting_denote tcInterp opInterp fvarVal vt
      .nil h_applySubst_wt h₂
      (HList.cast h_sorts_eq da)
      h_keys h_len h_tys_len h_sorts_eq.symm h_wt h_denotes h_annot_subst
  | eval_fn e callee e' args fn denotefn hcall heval hresult =>
    sorry

/-- A single step preserves well-typedness. -/
theorem Step.type_preserved
    {F : @Factory T} {env : Env T}
    {e₁ e₂ : LExpr T.mono} {τ : LMonoTy}
    (hstep : Step F env e₁ e₂)
    (h₁ : LExpr.HasTypeA [] e₁ τ)
    : LExpr.HasTypeA [] e₂ τ := by
  sorry

/-- Multi-step version: if `e₁` reduces to `e₂` in zero or more steps, and
both are well-typed at `τ`, they have the same denotation. -/
theorem StepStar.denote_preserved
    {F : @Factory T} {env : Env T}
    {e₁ e₂ : LExpr T.mono} {τ : LMonoTy}
    (hsteps : StepStar F env e₁ e₂)
    (h₁ : LExpr.HasTypeA [] e₁ τ)
    (h₂ : LExpr.HasTypeA [] e₂ τ)
    (hF : Factory.InterpConsistent tcInterp opInterp F)
    (hEnv : Env.InterpConsistent tcInterp opInterp env fvarVal)
    : LExpr.denote tcInterp opInterp fvarVal vt .nil e₁ τ h₁ =
      LExpr.denote tcInterp opInterp fvarVal vt .nil e₂ τ h₂ := by
  sorry

end -- section [DecidableEq T.IDMeta] [Inhabited T.mono.base.IDMeta]

end Lambda
