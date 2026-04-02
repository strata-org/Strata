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
        rw[ih h_arg h_arg' hOps.2]
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
        rw[ih h_fn h_fn' hOps.1]
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
        rw [ih h_c h_c' hOps.1]
  | ite_reduce_then_branch econd ethen ethen' eelse hstep' ih =>
    cases h₁ with
    | ite h_c h_t h_e =>
      cases h₂ with
      | ite h_c' h_t' h_e' =>
        rw [denote_ite .nil h_c h_t h_e,
            denote_ite .nil h_c' h_t' h_e']
        rw [ih h_t h_t' hOps.2.1]
  | ite_reduce_else_branch econd ethen eelse eelse' hstep' ih =>
    cases h₁ with
    | ite h_c h_t h_e =>
      cases h₂ with
      | ite h_c' h_t' h_e' =>
        rw [denote_ite .nil h_c h_t h_e,
            denote_ite .nil h_c' h_t' h_e']
        rw [ih h_e h_e' hOps.2.2]
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
        have ih_eq := ih h_1 h_1' hOps.1
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
        have ih_eq := ih h_2 h_2' hOps.2
        by_cases heq : LExpr.denote tcInterp opInterp fvarVal vt .nil v1 _ h_1 =
            LExpr.denote tcInterp opInterp fvarVal vt .nil e2 _ h_2
        · rw [denote_eq_true .nil h_1 h_2 _ heq,
              denote_eq_true .nil h_1' h_2' _
                (by rw [← ih_eq]; exact heq)]
        · rw [denote_eq_false .nil h_1 h_2 _ heq,
              denote_eq_false .nil h_1' h_2' _
                (by rw [← ih_eq]; exact heq)]
  | expand_fn e callee fnbody new_body args fn hcall hbody heq =>
    -- Step 1: Decompose the call via callOfLFunc_denote
    obtain ⟨argTys, ty_op, m, name, h_args, hty_op, h_callee_eq, h_denote_e⟩ :=
      callOfLFunc_denote tcInterp opInterp fvarVal vt hcall h₁
    -- Step 2: Get σ from OpsConsistent
    have h_ops_callee := OpsConsistent_callOfLFunc_callee hOps hcall
    rw [h_callee_eq] at h_ops_callee
    simp only [OpsConsistent] at h_ops_callee
    -- Connect getFactoryLFunc to fn
    have h_getF : F.getFactoryLFunc name.name = some fn := by
      obtain ⟨m', name', ty', hcallee', hgetF'⟩ := callOfLFunc_getFactoryLFunc hcall
      rw [h_callee_eq] at hcallee'
      cases hcallee'
      exact hgetF'
    rw [h_getF] at h_ops_callee
    obtain ⟨σ, h_ty_op_eq⟩ := h_ops_callee
    -- Step 3: Decompose ty_op = substMap σ (mkArrow' fn.output inputTys)
    --   into τ = substMap σ fn.output and argTys = inputTys.map (substMap σ)
    have h_inputTys := fn.inputs.map Prod.snd
    have h_substMap_arrow := substMap_mkArrow' σ fn.output (fn.inputs.map Prod.snd)
    rw [h_substMap_arrow] at h_ty_op_eq
    rw [hty_op] at h_ty_op_eq
    -- h_ty_op_eq : τ.mkArrow' argTys = (substMap σ fn.output).mkArrow' (map (substMap σ) inputTys)
    -- mkArrow'_injective needs h_len for the first list
    have h_len : argTys.length = (List.map (LMonoTy.substMap σ) (List.map Prod.snd fn.inputs)).length := by
      simp; exact h_args.length_eq.symm.trans (callOfLFunc_arity hcall)
    have h_inj := mkArrow'_injective h_len h_ty_op_eq
    have h_τ_eq : τ = LMonoTy.substMap σ fn.output := h_inj.1
    have h_argTys_eq : argTys = (fn.inputs.map Prod.snd).map (LMonoTy.substMap σ) := h_inj.2
    -- Step 4: Define vt'
    let vt' : TyVarVal := fun x => match σ.find? x with
      | some t => LMonoTy.substTyVars vt t | none => vt x
    -- Step 7: Get body typing and InterpConsistentBody from factory consistency
    have h_fn_mem : fn ∈ F := callOfLFunc_mem hcall
    have h_body_wt := (hFwt fn h_fn_mem fnbody hbody).1
    have h_annot := (hFwt fn h_fn_mem fnbody hbody).2
    have h_icb := hF.1 fn h_fn_mem fnbody hbody
    -- Instantiate InterpConsistentBody at vt' and fvarVal
    let bindings_vt' := fn.inputs.map (fun (id, ty) => (id, LMonoTy.substTyVars vt' ty))
    let inputSorts_vt' := bindings_vt'.map Prod.snd
    let fullSort_vt' := LSort.mkArrow (LMonoTy.substTyVars vt' fn.output) inputSorts_vt'
    -- Step 5: Connect opInterp calls
    -- We need: fn.name.name = name.name
    have h_fn_name : fn.name.name = name.name :=
      getFactoryLFunc_name h_getF
    -- We need: substTyVars vt ty_op = fullSort_vt'
    have h_sort_connect : LMonoTy.substTyVars vt ty_op = fullSort_vt' := by
      rw [hty_op]
      rw [substTyVars_mkArrow']
      congr 1
      · rw [h_τ_eq]; exact (substTyVars_substMap vt σ fn.output)
      · rw [h_argTys_eq]; simp [List.map_map, inputSorts_vt', bindings_vt']
        congr 1; intro a b _
        show LMonoTy.substTyVars vt (LMonoTy.substMap σ b) = LMonoTy.substTyVars vt' b
        change LMonoTy.substTyVars vt (LMonoTy.substMap σ b) =
          LMonoTy.substTyVars (fun x => match σ.find? x with | some t => LMonoTy.substTyVars vt t | none => vt x) b
        exact substTyVars_substMap vt σ b
    -- Instantiate InterpConsistentBody at vt', fvarVal, h_body_wt
    have h_icb_inst := h_icb vt' fvarVal h_body_wt
    -- Step 6: argTys.map (substTyVars vt) = inputSorts_vt'
    have h_sorts_eq : argTys.map (LMonoTy.substTyVars vt) = inputSorts_vt' := by
      simp [inputSorts_vt', bindings_vt', h_argTys_eq, List.map_map]
      congr 1; intro a b _
      show LMonoTy.substTyVars vt (LMonoTy.substMap σ b) = LMonoTy.substTyVars vt' b
      change LMonoTy.substTyVars vt (LMonoTy.substMap σ b) =
        LMonoTy.substTyVars (fun x => match σ.find? x with | some t => LMonoTy.substTyVars vt t | none => vt x) b
      exact substTyVars_substMap vt σ b
    -- Cast denoteArgs to the right sort list
    let da := denoteArgs tcInterp opInterp fvarVal vt .nil args argTys h_args
    have h_da_cast : HList.cast h_sorts_eq da = (HList.cast h_sorts_eq da) := rfl
    -- Instantiate h_icb_inst with the cast args
    have h_icb_applied := h_icb_inst (HList.cast h_sorts_eq da)
    -- The RHS of h_icb_applied lives in TyDenote tcInterp vt' fn.output
    -- but we need TyDenote tcInterp vt τ. These are equal by substTyVars_substMap + h_τ_eq.
    have h_sort_eq_vt : LMonoTy.substTyVars vt' fn.output = LMonoTy.substTyVars vt τ := by
      rw [h_τ_eq]; exact (substTyVars_substMap vt σ fn.output).symm
    have h_td_eq : TyDenote tcInterp vt' fn.output = TyDenote tcInterp vt τ :=
      congrArg (SortDenote tcInterp) h_sort_eq_vt
    -- Step 8: The whole chain from denote e to denote (withArgs ...) vt' fnbody
    have h_chain : LExpr.denote tcInterp opInterp fvarVal vt .nil e τ h₁ =
        cast h_td_eq (LExpr.denote tcInterp opInterp
          (fvarVal.withArgs bindings_vt' (HList.cast h_sorts_eq da))
          vt' .nil fnbody fn.output h_body_wt) := by
      rw [h_denote_e]
      rw [← h_icb_applied, h_fn_name]
      subst hty_op
      have h := applyArgs_cast_eq
        (substTyVars_mkArrow' vt τ argTys) h_sort_connect
        h_sorts_eq h_sort_eq_vt.symm
        (opInterp name.name (LMonoTy.substTyVars vt (τ.mkArrow' argTys))) da
      grind
    -- Step 9: Use substFvarsLifting_denote_poly to connect
    subst heq
    have h_keys_eq : (fn.inputs.keys.zip args).map Prod.fst = bindings_vt'.map Prod.fst := by
      rw[zip_map_fst_eq]
      . simp[bindings_vt', List.map_map]
        rw[ListMap.keys_eq_map_fst]
        rfl
      · rw[ListMap.keys_eq_map_fst]
        simp [callOfLFunc_arity hcall]
    have h_arity := callOfLFunc_arity hcall
    have h_zip_snd : (fn.inputs.keys.zip args).map Prod.snd = args :=
      zip_map_snd_eq fn.inputs.keys args (by rw [ListMap.keys_eq_map_fst]; simp [h_arity])
    have h_wt_zip : List.Forall₂ (LExpr.HasTypeA []) ((fn.inputs.keys.zip args).map Prod.snd) argTys :=
      h_zip_snd.symm ▸ h_args
    have h_argTys_len : argTys.length = (fn.inputs.keys.zip args).length := by
      simp [List.length_zip, ListMap.keys_eq_map_fst, h_arity]
      exact h_args.length_eq.symm.trans h_arity
    have h_inputTys_len : (fn.inputs.map Prod.snd).length = (fn.inputs.keys.zip args).length := by
      simp [List.length_zip, ListMap.keys_eq_map_fst, h_arity]
    have h_denotes_eq : da = denoteArgs tcInterp opInterp fvarVal vt .nil ((fn.inputs.keys.zip args).map Prod.snd) argTys h_wt_zip := by
      simp [h_zip_snd]; rfl
    have h_denotes_eq' : HList.cast h_sorts_eq da = HList.cast h_sorts_eq
        (denoteArgs tcInterp opInterp fvarVal vt .nil
          ((fn.inputs.keys.zip args).map Prod.snd) argTys h_wt_zip) := by
      congr 1
    have h_annot_zip : fvars_annotated_by
        ((fn.inputs.keys.zip args).map Prod.fst |>.zip (fn.inputs.map Prod.snd)) fnbody := by
      have : (fn.inputs.keys.zip args).map Prod.fst = fn.inputs.keys :=
        zip_map_fst_eq fn.inputs.keys args (by rw [ListMap.keys_eq_map_fst]; simp [h_arity])
      rw [this, ListMap.keys_eq_map_fst, zip_map_fst_snd_eq]
      exact h_annot
    have h_bvar_eq_nil : ∀ i (τ_b : LMonoTy) (hb : ([] : List LMonoTy)[i]? = some τ_b),
        LMonoTy.substTyVars vt' τ_b = LMonoTy.substTyVars vt τ_b ∧
        HEq ((HList.nil : BVarVal tcInterp vt' []).get i hb)
             ((HList.nil : BVarVal tcInterp vt []).get i hb) := by
      intro i τ_b hb; simp at hb
    -- Step 10: Combine h_chain with substFvarsLifting_denote_poly
    rw [h_chain]
    exact (substFvarsLifting_denote_poly
      (σ := σ) (hvt' := rfl)
      (bvarVal_outer_vt := .nil) (bvarVal_outer_vt' := .nil)
      (h_body := h_body_wt) (h_subst := h₂)
      (h_args := HList.cast h_sorts_eq da)
      (h_keys := h_keys_eq)
      (h_argTys_len := h_argTys_len) (h_inputTys_len := h_inputTys_len)
      (h_inst := h_argTys_eq) (h_sorts := h_sorts_eq.symm)
      (h_wt := h_wt_zip)
      (h_denotes := h_denotes_eq')
      (h_annot := h_annot_zip)
      (h_sort_eq := h_sort_eq_vt) (h_td_eq := h_td_eq)
      (h_bvar_eq := h_bvar_eq_nil)).symm
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
