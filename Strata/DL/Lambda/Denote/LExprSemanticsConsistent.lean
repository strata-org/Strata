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
import all Strata.DL.Lambda.Denote.LExprDenoteEq

/-!
## Operational Semantics Consistency

Proves that the Lambda operational and denotational semantics agree:
evaluation steps preserve denotation and type.

- `Step.denote_preserved` — one evaluation step preserves denotation
- `Step.type_preserved` — one evaluation step preserves type (sorry)
- `StepStar.denote_preserved` — multi-step evaluation preserves denotation (sorry)
-/

namespace Lambda

variable {T : LExprParams}
variable (tcInterp : TyConstrInterp)
variable (opInterp : OpInterp tcInterp)
variable (fvarVal : FreeVarVal T tcInterp)
variable (vt : TyVarVal)

/-! ### State substitution and denotation -/

section
variable [DecidableEq T.IDMeta] [Inhabited T.mono.base.IDMeta]

omit [Inhabited T.mono.base.IDMeta] in
/-- Values from a state map are well-typed at the types given by `envTys`,
weakened to any binder context `Δ`. -/
private theorem state_map_forall₂_hasTypeA
    {Δ : List LMonoTy}
    (entries : List (T.Identifier × LExpr T.mono))
    (envTys : Map T.Identifier LMonoTy)
    (env : T.Identifier → Option (LExpr T.mono))
    (h_in_env : ∀ (k : T.Identifier) (v : LExpr T.mono),
      (k, v) ∈ entries → env k = some v)
    (hEnvWT : ∀ (x : T.Identifier) (v : LExpr T.mono) (ty : LMonoTy),
      env x = some v → Map.find? envTys x = some ty → LExpr.HasTypeA [] v ty)
    (hEnvLC : ∀ (x : T.Identifier) (v : LExpr T.mono),
      env x = some v → LExpr.lcAt 0 v = true)
    (hEnvTysCover : ∀ (x : T.Identifier) (v : LExpr T.mono),
      env x = some v → ∃ ty, Map.find? envTys x = some ty)
    : List.Forall₂ (LExpr.HasTypeA Δ) (entries.map Prod.snd)
        (entries.map (fun (k, _) =>
          match Map.find? envTys k with
          | some ty => ty
          | none => .bool)) := by
  induction entries with
  | nil => exact List.Forall₂.nil
  | cons p rest ih =>
    obtain ⟨k, v⟩ := p
    simp only [List.map_cons]
    apply List.Forall₂.cons
    · have h_mem_head : (k, v) ∈ (k, v) :: rest := List.mem_cons_self ..
      have h_env_kv := h_in_env k v h_mem_head
      obtain ⟨ty, h_envTys_k⟩ := hEnvTysCover k v h_env_kv
      simp only [h_envTys_k]
      have h_wt := hEnvWT k v ty h_env_kv h_envTys_k
      have h_lc := hEnvLC k v h_env_kv
      exact HasTypeA_weaken h_wt h_lc
    · exact ih (fun k' v' h_mem => h_in_env k' v' (List.mem_cons_of_mem _ h_mem))

omit [Inhabited T.mono.base.IDMeta] in
/-- Substituting free variables from the state preserves denotation.

Requires that the environment is:
- interpretation-consistent (`hEnv`): env values denote to what `fvarVal` gives,
- locally closed (`hEnvLC`): env values have no dangling bound variables,
- well-typed (`hEnvWT`): env values are well-typed at the types given by `envTys`,
- covered (`hEnvTysCover`): every env key has a type in `envTys`,
- annotated (`hAnnot`): fvar annotations in `e` match `envTys`. -/
private theorem substFvarsFromState_denote_preserved
    {σ : LState T} {e : LExpr T.mono} {τ : LMonoTy}
    {Δ : List LMonoTy} {bvarVal : BVarVal tcInterp vt Δ}
    (h₁ : LExpr.HasTypeA Δ e τ)
    (h₂ : LExpr.HasTypeA Δ (LExpr.substFvarsFromState σ e) τ)
    (hEnv : Env.InterpConsistent tcInterp opInterp (Scopes.toEnv σ.state) fvarVal)
    (hEnvLC : ∀ (x : T.Identifier) (v : LExpr T.mono),
      Scopes.toEnv σ.state x = some v → LExpr.lcAt 0 v = true)
    (envTys : Map T.Identifier LMonoTy)
    (hEnvWT : ∀ (x : T.Identifier) (v : LExpr T.mono) (ty : LMonoTy),
      Scopes.toEnv σ.state x = some v →
      Map.find? envTys x = some ty →
      LExpr.HasTypeA [] v ty)
    (hEnvTysCover : ∀ (x : T.Identifier) (v : LExpr T.mono),
      Scopes.toEnv σ.state x = some v →
      ∃ ty, Map.find? envTys x = some ty)
    (hAnnot : fvars_annotated_by envTys e)
    : LExpr.denote tcInterp opInterp fvarVal vt bvarVal e τ h₁ =
      LExpr.denote tcInterp opInterp fvarVal vt bvarVal
        (LExpr.substFvarsFromState σ e) τ h₂ := by
  simp only [LExpr.substFvarsFromState] at h₂ ⊢
  let sm : Map T.Identifier (LExpr T.mono) :=
    List.map (fun x => (x.fst, x.2.snd)) (Maps.toSingleMap σ.state)
  have h_lc : ∀ (k : T.Identifier) (v : LExpr T.mono),
      Map.find? sm k = some v → LExpr.lcAt 0 v = true := by
    intro k v hfind
    have h_fmap : sm = Map.fmap Prod.snd (Maps.toSingleMap σ.state) := rfl
    rw [h_fmap, Map.find?_fmap] at hfind
    cases htsm : (Maps.toSingleMap σ.state).find? k with
    | none => simp [htsm] at hfind
    | some p =>
      simp [htsm] at hfind; subst hfind
      apply hEnvLC k p.snd
      simp only [Scopes.toEnv]
      rw [Maps.find?_toSingleMap] at htsm
      rw [htsm]
      rfl
  let ks := sm.keySet
  let tys : List LMonoTy := ks.map (fun (k, _) =>
    match Map.find? envTys k with
    | some ty => ty
    | none => .bool)
  let sortBindings : List (Identifier T.IDMeta × LSort) :=
    (ks.map Prod.fst).zip (tys.map (LMonoTy.substTyVars vt))
  have h_in_env : ∀ (k : T.Identifier) (v : LExpr T.mono),
      (k, v) ∈ (show List _ from ks) → Scopes.toEnv σ.state k = some v := by
    intro k v h_mem_ks
    have h_find_sm : Map.find? sm k = some v :=
      (Map.find?_iff_mem_keySet (m := sm) (x := k) (v := v)).mpr h_mem_ks
    have h_fmap : sm = Map.fmap Prod.snd (Maps.toSingleMap σ.state) := rfl
    rw [h_fmap, Map.find?_fmap] at h_find_sm
    cases h_tsm : (Maps.toSingleMap σ.state).find? k with
    | none => simp [h_tsm] at h_find_sm
    | some p =>
      simp [h_tsm] at h_find_sm; subst h_find_sm
      simp only [Scopes.toEnv]
      rw [Maps.find?_toSingleMap] at h_tsm
      rw [h_tsm]; rfl
  have h_wt : List.Forall₂ (LExpr.HasTypeA Δ) (ks.map Prod.snd) tys :=
    state_map_forall₂_hasTypeA ks envTys (Scopes.toEnv σ.state)
      h_in_env hEnvWT hEnvLC hEnvTysCover
  have h_sorts : sortBindings.map Prod.snd = tys.map (LMonoTy.substTyVars vt) := by
    simp only [sortBindings]
    apply zip_map_snd_eq
    simp [tys]
  let h_args : HList (SortDenote tcInterp) (sortBindings.map Prod.snd) :=
    HList.cast h_sorts.symm
      (denoteArgs tcInterp opInterp fvarVal vt bvarVal (ks.map Prod.snd) tys h_wt)
  have h_ks_tys_len : (ks.map Prod.fst).length = (tys.map (LMonoTy.substTyVars vt)).length := by
    simp [tys]
  have h_keys : ks.map Prod.fst = sortBindings.map Prod.fst := by
    simp only [sortBindings]
    exact (zip_map_fst_eq _ _ h_ks_tys_len).symm
  have h_len : ks.length = sortBindings.length := by
    have := congrArg List.length h_keys
    simp at this; exact this
  have h_tys_len : tys.length = ks.length := by simp [tys]
  have h_denotes : h_args = HList.cast h_sorts.symm
      (denoteArgs tcInterp opInterp fvarVal vt bvarVal (ks.map Prod.snd) tys h_wt) := by
    rfl
  -- Prove fvars_annotated_by for the keySet-derived type map
  have h_annot : fvars_annotated_by (ks.map Prod.fst |>.zip tys) e := by
    apply fvars_annotated_by_of_find_sub _ envTys e _ hAnnot
    intro k v h_find_zip
    have h_mem := Map.find?_mem _ _ _ h_find_zip
    have h_k_mem := (List.of_mem_zip h_mem).1
    rw [List.mem_map] at h_k_mem
    obtain ⟨⟨k', w⟩, h_kw_mem, h_k_eq⟩ := h_k_mem
    simp at h_k_eq; subst h_k_eq
    have h_env_kw := h_in_env k' w h_kw_mem
    obtain ⟨ty, h_envTys_k⟩ := hEnvTysCover k' w h_env_kw
    obtain ⟨i, h_key_i, h_val_i, h_first_i⟩ := Map.find?_index h_find_zip
    rw [List.map_fst_zip (by simp [tys] : (ks.map Prod.fst).length ≤ tys.length)] at h_key_i
    rw [List.map_snd_zip (by simp [tys] : tys.length ≤ (ks.map Prod.fst).length)] at h_val_i
    simp only [tys, List.getElem?_map] at h_val_i
    rw [List.getElem?_map] at h_key_i
    cases h_ks_i : ks[i]? with
    | none => simp [h_ks_i] at h_key_i
    | some p =>
      simp [h_ks_i] at h_key_i h_val_i
      rw [h_key_i, h_envTys_k] at h_val_i
      exact h_val_i ▸ h_envTys_k
  have h_lc_ks : ∀ (k : T.Identifier) (v : LExpr T.mono),
      Map.find? ks k = some v → LExpr.lcAt 0 v = true := by
    intro k v hfind
    rw [Map.find?_keySet] at hfind
    exact h_lc k v hfind
  have h_substFvars_eq : LExpr.substFvars e sm = LExpr.substFvars e ks :=
    LExpr.substFvars_congr_find e sm ks (fun k => (Map.find?_keySet (m := sm) (k := k)).symm)
  -- Generalize typing proof, rewrite sm to ks, apply substFvars_denote
  symm
  generalize_lhs_last_arg
  rename_i Hty
  revert Hty
  rw[h_substFvars_eq]
  intros Hty
  rw [substFvars_denote (tcInterp := tcInterp) (opInterp := opInterp)
    (fvarVal := fvarVal) (vt := vt)
    bvarVal h₁ Hty h_args h_keys h_len h_tys_len h_sorts h_wt h_denotes h_annot h_lc_ks]
  -- Reduce to showing fvarVal = fvarVal.withArgs on free vars of e via denote_ext
  symm
  apply denote_ext
  · intros; rfl
  · intro name ty h_fv
    by_cases h_mem : name ∈ sortBindings.map Prod.fst
    · have h_mem_ks : name ∈ ks.map Prod.fst := h_keys ▸ h_mem
      cases h_find_v : Map.find? ks name with
      | none => exact absurd h_mem_ks (Map.findNone_eq_notmem_mapfst.mpr h_find_v)
      | some v =>
      obtain ⟨i, h_key_b, h_val_b, h_first_b⟩ := Map.find?_index h_find_v
      have h_key : (sortBindings.map Prod.fst)[i]? = some name := by
        rw [← h_keys]; exact h_key_b
      have h_first : ∀ j < i, (sortBindings.map Prod.fst)[j]? ≠ some name := by
        intro j hj; rw [← h_keys]; exact h_first_b j hj
      -- Bridge ks.find? → sm.find? → Scopes.toEnv
      have h_find_sm : Map.find? sm name = some v := by
        rw [← Map.find?_keySet]; exact h_find_v
      have h_env_v : Scopes.toEnv σ.state name = some v := by
        have h_fmap : sm = Map.fmap Prod.snd (Maps.toSingleMap σ.state) := rfl
        rw [h_fmap, Map.find?_fmap] at h_find_sm
        cases h_tsm : (Maps.toSingleMap σ.state).find? name with
        | none => simp [h_tsm] at h_find_sm
        | some p =>
          simp [h_tsm] at h_find_sm; subst h_find_sm
          simp only [Scopes.toEnv]
          rw [Maps.find?_toSingleMap] at h_tsm
          rw [h_tsm]; rfl
      have h_envTys_name : Map.find? envTys name = some ty := by
        obtain ⟨ty', h_find_ty'⟩ := hEnvTysCover name v h_env_v
        have h_ty_eq := fvars_annotated_by_freeVars envTys e hAnnot name ty ty' h_fv h_find_ty'
        rw [h_ty_eq]; exact h_find_ty'
      have h_tys_i : tys[i]? = some ty := by
        simp only [tys, List.getElem?_map]
        cases h_ks_i : ks[i]? with
        | none => simp [h_ks_i] at h_key_b
        | some p =>
          simp [h_ks_i] at h_key_b
          simp [h_key_b, h_envTys_name]
      have h_sort : (sortBindings.map Prod.snd)[i]? = some (LMonoTy.substTyVars vt ty) := by
        rw [h_sorts, List.getElem?_map, h_tys_i]; rfl
      -- Rewrite withArgs to index lookup, then match against env interpretation
      rw [IdentInterp.withArgs_get (tcInterp := tcInterp) fvarVal sortBindings h_args
        name _ i h_key h_sort h_first]
      rw [h_denotes, HList.get_cast]
      · have h_sort_mapped : (tys.map (LMonoTy.substTyVars vt))[i]? =
            some (LMonoTy.substTyVars vt ty) := by
          rw [List.getElem?_map, h_tys_i]; rfl
        rw [denoteArgs_get (tcInterp := tcInterp) (opInterp := opInterp)
          (fvarVal := fvarVal) (vt := vt) (bvarVal := bvarVal) h_wt i h_val_b h_tys_i h_sort_mapped]
        have h_v_wt : LExpr.HasTypeA [] v ty := hEnvWT name v ty h_env_v h_envTys_name
        have h_v_lc : LExpr.lcAt 0 v = true := hEnvLC name v h_env_v
        rw [denote_irrel_of_lcAt (tcInterp := tcInterp) (opInterp := opInterp)
          (fvarVal := fvarVal) (vt := vt) h_v_lc _ h_v_wt bvarVal .nil]
        exact (hEnv vt name v ty h_env_v h_v_wt).symm
      · exact h_sorts ▸ h_sort
    · exact (IdentInterp.withArgs_not_mem (tcInterp := tcInterp) (fvarVal := fvarVal)
        h_args h_mem).symm
  · intros; rfl

/-! ### Step relation preserves denotation -/

/-- If `e₁` steps to `e₂` under a factory `F` and environment `env`, and both
are well-typed at the same type `τ`, then they have the same denotation.

Assumptions:
- `hF`: the factory's function bodies denote consistently with `opInterp`.
- `hFwt`: the factory's function bodies are well-typed.
- `hEnv`: environment values denote consistently with `fvarVal`.
- `hOps`: every op referenced in `e₁` has a corresponding factory entry.
- `hFwf`: the factory is well-formed (arities, types match declarations).
- `hcwf`: constructor declarations in `F` are well-formed w.r.t. `tf`.
- `hConstrIC`: constructor interpretations are consistent with `tcInterp`/`opInterp`.
- `htfwf`: the type factory is well-formed.
- `hEnvLC`: environment values are locally closed (no dangling bound variables).
- `envTys`, `hEnvWT`: environment values are well-typed at the types given by `envTys`.
- `hEnvTysCover`: every environment key has a type in `envTys`.
- `hAnnot`: free variable annotations in `e₁` match `envTys`. -/
theorem Step.denote_preserved
    {F : @Factory T} {env : Env T} {tf : @TypeFactory T.IDMeta}
    {e₁ e₂ : LExpr T.mono} {τ : LMonoTy}
    (hstep : Step F env e₁ e₂)
    (h₁ : LExpr.HasTypeA [] e₁ τ)
    (h₂ : LExpr.HasTypeA [] e₂ τ)
    (hF : Factory.InterpConsistent tcInterp opInterp F)
    (hFwt : Factory.WellTyped F)
    (hEnv : Env.InterpConsistent tcInterp opInterp env fvarVal)
    (hOps : OpsConsistent F e₁)
    (hFwf : FactoryWF F)
    (hcwf : Factory.ConstrWellFormed F tf)
    (hConstrIC : ConstrInterpConsistent tcInterp opInterp F)
    (htfwf : TypeFactoryWF tf)
    (hEnvLC : ∀ (x : T.Identifier) (e : LExpr T.mono), env x = some e → LExpr.lcAt 0 e = true)
    (envTys : Map T.Identifier LMonoTy)
    (hEnvWT : ∀ (x : T.Identifier) (e : LExpr T.mono) (ty : LMonoTy),
      env x = some e → Map.find? envTys x = some ty → LExpr.HasTypeA [] e ty)
    (hEnvTysCover : ∀ (x : T.Identifier) (e : LExpr T.mono),
      env x = some e → ∃ ty, Map.find? envTys x = some ty)
    (hAnnot : fvars_annotated_by envTys e₁)
    : LExpr.denote tcInterp opInterp fvarVal vt .nil e₁ τ h₁ =
      LExpr.denote tcInterp opInterp fvarVal vt .nil e₂ τ h₂ := by
  induction hstep generalizing τ with
  | expand_fvar x e henv =>
    cases h₁ with
    | fvar => simp [LExpr.denote]; exact (hEnv vt x _ _ henv h₂).symm
  | beta e1 v2 eres heq =>
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
        rw[ih h_arg h_arg' hOps.2.2 hAnnot.2]
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
        rw[ih h_fn h_fn' hOps.2.1 hAnnot.1]
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
        rw [ih h_c h_c' hOps.2.1 hAnnot.1]
  | ite_reduce_then_branch econd ethen ethen' eelse hstep' ih =>
    cases h₁ with
    | ite h_c h_t h_e =>
      cases h₂ with
      | ite h_c' h_t' h_e' =>
        rw [denote_ite .nil h_c h_t h_e,
            denote_ite .nil h_c' h_t' h_e']
        rw [ih h_t h_t' hOps.2.2.1 hAnnot.2.1]
  | ite_reduce_else_branch econd ethen eelse eelse' hstep' ih =>
    cases h₁ with
    | ite h_c h_t h_e =>
      cases h₂ with
      | ite h_c' h_t' h_e' =>
        rw [denote_ite .nil h_c h_t h_e,
            denote_ite .nil h_c' h_t' h_e']
        rw [ih h_e h_e' hOps.2.2.2 hAnnot.2.2]
  | eq_reduce_true e1 e2 heql =>
    cases h₁ with
    | eq h_1 h_2 =>
      rw [denote_eq_true .nil h_1 h_2 _
          (eql_true_implies_denote_eq tcInterp opInterp fvarVal vt h_1 h_2
            hOps.2.1 hOps.2.2 hFwf hcwf heql)]
      rfl
  | eq_reduce_false e1 e2 heql =>
    cases h₁ with
    | eq h_1 h_2 =>
      rw [denote_eq_false .nil h_1 h_2 _
          (eql_false_implies_denote_ne tcInterp opInterp fvarVal vt h_1 h_2
            hOps.2.1 hOps.2.2 hFwf hcwf htfwf heql hConstrIC)]
      rfl
  | eq_reduce_lhs e1 e1' e2 hstep' ih =>
    cases h₁ with
    | eq h_1 h_2 =>
      cases h₂ with
      | eq h_1' h_2' =>
        have hty := HasTypeA_unique h_2 h_2'; subst hty
        have ih_eq := ih h_1 h_1' hOps.2.1 hAnnot.1
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
        have ih_eq := ih h_2 h_2' hOps.2.2 hAnnot.2
        by_cases heq : LExpr.denote tcInterp opInterp fvarVal vt .nil v1 _ h_1 =
            LExpr.denote tcInterp opInterp fvarVal vt .nil e2 _ h_2
        · rw [denote_eq_true .nil h_1 h_2 _ heq,
              denote_eq_true .nil h_1' h_2' _
                (by rw [← ih_eq]; exact heq)]
        · rw [denote_eq_false .nil h_1 h_2 _ heq,
              denote_eq_false .nil h_1' h_2' _
                (by rw [← ih_eq]; exact heq)]
  | abs_subst_fvars body σ x _ h_env_eq =>
    -- Decompose abs typing
    cases h₁ with
    | abs h_body =>
      cases h₂ with
      | abs h_subst_body =>
        rw [denote_abs .nil h_body, denote_abs .nil h_subst_body]
        funext v
        exact substFvarsFromState_denote_preserved tcInterp opInterp fvarVal vt
          h_body h_subst_body (h_env_eq ▸ hEnv) (h_env_eq ▸ hEnvLC)
          envTys (h_env_eq ▸ hEnvWT) (h_env_eq ▸ hEnvTysCover) hAnnot
  | quant_subst_fvars_body tr body σ x _ h_env_eq =>
    cases h₁ with
    | quant h_tr h_body =>
      cases h₂ with
      | quant h_tr' h_subst_body =>
        have h_body_eq : ∀ v, LExpr.denote tcInterp opInterp fvarVal vt (.cons v .nil)
              body .bool h_body =
            LExpr.denote tcInterp opInterp fvarVal vt (.cons v .nil)
              (LExpr.substFvarsFromState σ body) .bool h_subst_body :=
          fun v => substFvarsFromState_denote_preserved tcInterp opInterp fvarVal vt
            h_body h_subst_body (h_env_eq ▸ hEnv) (h_env_eq ▸ hEnvLC)
            envTys (h_env_eq ▸ hEnvWT) (h_env_eq ▸ hEnvTysCover) hAnnot.2
        rename_i qty _ _ _ _ _ _
        cases qty with
        | all =>
          by_cases hall : ∀ v, (LExpr.denote tcInterp opInterp fvarVal vt (.cons v .nil)
              body .bool h_body : Bool) = true
          · rw [denote_quant_all_true .nil h_body _ hall]
            symm; apply denote_quant_all_true .nil h_subst_body
            intro v; rw [← h_body_eq]; exact hall v
          · have ⟨w, hw⟩ := Classical.not_forall.mp hall
            have hwf : (LExpr.denote tcInterp opInterp fvarVal vt (.cons w .nil)
                body .bool h_body : Bool) = false := Bool.eq_false_iff.mpr hw
            rw [denote_quant_all_false .nil h_body _ w hwf]
            symm; apply denote_quant_all_false .nil h_subst_body _ w
            rw [← h_body_eq]; exact hwf
        | exist =>
          by_cases hexist : ∃ v, (LExpr.denote tcInterp opInterp fvarVal vt (.cons v .nil)
              body .bool h_body : Bool) = true
          · obtain ⟨w, hw⟩ := hexist
            rw [denote_quant_exist_true .nil h_body _ w hw]
            symm; apply denote_quant_exist_true .nil h_subst_body _ w
            rw [← h_body_eq]; exact hw
          · have hexist_f : ∀ v, (LExpr.denote tcInterp opInterp fvarVal vt (.cons v .nil)
                body .bool h_body : Bool) = false :=
              fun v => Bool.eq_false_iff.mpr (fun h => hexist ⟨v, h⟩)
            rw [denote_quant_exist_false .nil h_body _ hexist_f]
            symm; apply denote_quant_exist_false .nil h_subst_body
            intro v; rw [← h_body_eq]; exact hexist_f v
  | quant_subst_fvars_trigger tr body σ x _ h_env_eq =>
    cases h₁ with
    | quant h_tr h_body =>
      cases h₂ with
      | quant h_tr' h_body' =>
        rename_i qk _ _ _ _ _ _
        cases qk with
        | all =>
          by_cases hall : ∀ v, (LExpr.denote tcInterp opInterp fvarVal vt (.cons v .nil)
              body .bool h_body : Bool) = true
          · rw [denote_quant_all_true .nil h_body _ hall]
            symm; apply denote_quant_all_true .nil h_body' _ hall
          · have ⟨w, hw⟩ := Classical.not_forall.mp hall
            have hwf : (LExpr.denote tcInterp opInterp fvarVal vt (.cons w .nil)
                body .bool h_body : Bool) = false := Bool.eq_false_iff.mpr hw
            rw [denote_quant_all_false .nil h_body _ w hwf]
            symm; apply denote_quant_all_false .nil h_body' _ w hwf
        | exist =>
          by_cases hexist : ∃ v, (LExpr.denote tcInterp opInterp fvarVal vt (.cons v .nil)
              body .bool h_body : Bool) = true
          · obtain ⟨w, hw⟩ := hexist
            rw [denote_quant_exist_true .nil h_body _ w hw]
            symm; apply denote_quant_exist_true .nil h_body' _ w hw
          · have hexist_f : ∀ v, (LExpr.denote tcInterp opInterp fvarVal vt (.cons v .nil)
                body .bool h_body : Bool) = false :=
              fun v => Bool.eq_false_iff.mpr (fun h => hexist ⟨v, h⟩)
            rw [denote_quant_exist_false .nil h_body _ hexist_f]
            symm; apply denote_quant_exist_false .nil h_body' _ hexist_f
  | expand_fn e callee fnbody new_body args fn tySubst hcall hbody htySubst heq =>
    -- Step 1: Decompose the call
    obtain ⟨argTys, ty_op, m, name, h_args, hty_op, h_callee_eq, h_denote_e⟩ :=
      callOfLFunc_denote tcInterp opInterp fvarVal vt hcall h₁
    -- Step 2: Extract from OpsConsistent
    obtain ⟨tySubst', htySubst', h_ty_op_eq⟩ := OpsConsistent_callOfLFunc hOps hcall
    rw [h_callee_eq] at htySubst htySubst'
    have htySubst'_ct := LFunc.computeTypeSubst_of_opTypeSubst (args := args) htySubst'
    have : tySubst' = tySubst := Option.some.inj (htySubst'_ct.symm.trans htySubst)
    subst this
    have h_ty_op_val := h_ty_op_eq m name ty_op h_callee_eq
    -- Step 3: Decompose into τ and argTys
    have h_subst_arrow := subst_mkArrow' tySubst' fn.output (fn.inputs.map Prod.snd)
    rw [h_subst_arrow] at h_ty_op_val
    rw [hty_op] at h_ty_op_val
    have h_len : argTys.length = ((fn.inputs.map Prod.snd).map (LMonoTy.subst tySubst')).length := by
      simp; exact h_args.length_eq.symm.trans (Factory.callOfLFunc_arity hcall)
    have ⟨h_τ_eq, h_argTys_eq⟩ := LMonoTy.mkArrow'_injective h_len h_ty_op_val
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
    obtain ⟨_, _, _, h_callee_op, h_get⟩ := Factory.callOfLFunc_getElem? hcall
    rw [h_callee_eq] at h_callee_op; cases h_callee_op
    -- h_get : F[name.name]? = some fn
    have h_fn_mem_str : name.name ∈ F := Factory.getElem?_some_implies_mem h_get
    have h_fn_eq : F[name.name] = fn := Factory.getElem?_some_getElem h_get
    have h_body_wt := h_fn_eq ▸ (hFwt name.name h_fn_mem_str fnbody (h_fn_eq ▸ hbody)).1
    have h_annot := h_fn_eq ▸ (hFwt name.name h_fn_mem_str fnbody (h_fn_eq ▸ hbody)).2
    have h_icb := h_fn_eq ▸ hF.1 name.name h_fn_mem_str fnbody (h_fn_eq ▸ hbody)
    let bindings_vt' := fn.inputs.map (fun (id, ty) => (id, LMonoTy.substTyVars vt' ty))
    let da := denoteArgs tcInterp opInterp fvarVal vt .nil args argTys h_args
    have h_icb_inst := h_icb vt' fvarVal h_body_wt (HList.cast (h_fn_eq ▸ h_sorts_eq) da)
    -- Step 8: Connect the two applyArgs calls
    have h_fn_name : fn.name.name = name.name := Factory.getElem?_name h_get
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
    have h_arity := Factory.callOfLFunc_arity hcall
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
    rename_i step_md
    -- Step 1: Decompose the call
    obtain ⟨argTys, ty_op, md, name, h_args, hty_op, h_callee_eq, h_denote_e⟩ :=
      callOfLFunc_denote tcInterp opInterp fvarVal vt hcall h₁
    -- Step 2: Extract tySubst from OpsConsistent
    obtain ⟨tySubst, htySubst, h_ty_op_eq⟩ := OpsConsistent_callOfLFunc hOps hcall
    -- Step 3: Derive τ = subst tySubst fn.output and argTys = instInputTys
    have h_ty_op_val := h_ty_op_eq md name ty_op h_callee_eq
    have h_subst_arrow := subst_mkArrow' tySubst fn.output (fn.inputs.map Prod.snd)
    rw [h_subst_arrow] at h_ty_op_val
    rw [hty_op] at h_ty_op_val
    have h_len : argTys.length = ((fn.inputs.map Prod.snd).map (LMonoTy.subst tySubst)).length := by
      simp; exact h_args.length_eq.symm.trans (Factory.callOfLFunc_arity hcall)
    have ⟨h_τ_eq, h_argTys_eq⟩ := LMonoTy.mkArrow'_injective h_len h_ty_op_val
    -- Step 4: Get InterpConsistentEval from Factory.InterpConsistent
    obtain ⟨_, _, _, h_callee_op, h_get⟩ := Factory.callOfLFunc_getElem? hcall
    rw [h_callee_eq] at h_callee_op; cases h_callee_op
    have h_fn_mem_str : name.name ∈ F := Factory.getElem?_some_implies_mem h_get
    have h_fn_eq : F[name.name] = fn := Factory.getElem?_some_getElem h_get
    have h_ice := h_fn_eq ▸ hF.2 name.name h_fn_mem_str denotefn (h_fn_eq ▸ heval)
    -- Step 5: Instantiate InterpConsistentEval
    have h_ceval : denotefn step_md args = some e' := hresult.symm
    subst h_τ_eq h_argTys_eq
    have h_ice_inst := h_ice vt fvarVal step_md tySubst args e' h_ceval h_args h₂
    -- Step 6-7: Connect and conclude
    have h_fn_name : fn.name.name = name.name := Factory.getElem?_name h_get
    rw [h_denote_e, h_ice_inst, h_fn_name]
    congr 1
    subst hty_op
    grind

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
