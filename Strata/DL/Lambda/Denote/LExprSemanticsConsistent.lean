/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

import all Strata.DL.Lambda.Semantics
import all Strata.DL.Lambda.Denote.LExprDenoteEq

/-!
## Operational Semantics Consistency

Proves that the Lambda operational and denotational semantics agree:
evaluation steps preserve denotation, type, and structural invariants.

### Single-step preservation
- `Step.denote_preserved` — one evaluation step preserves denotation
- `Step.type_preserved` — one evaluation step preserves `HasTypeA`
- `Step.OpsConsistent_preserved` — one step preserves `OpsConsistent`
- `Step.fvars_annotated_preserved` — one step preserves `fvars_annotated_by`

### Multi-step preservation
- `StepStar.type_preserved` — `HasTypeA` is preserved by `StepStar`
- `StepStar.denote_preserved` — denotation is preserved by `StepStar`
- `StepStar.denote_preserved'` — corollary that derives the `e₂` typing proof automatically

### Evaluator soundness
- `eval_denote_sound` — if `e₂ = eval n σ e` and both are well-typed at `τ`,
  then `denote e = denote e₂` (composes `eval_StepStar` with `StepStar.denote_preserved`)

### Bundled assumption structures
- `Env.InterpConsistent` — environment values denote as the free-variable valuation
- `InterpConsistent` — interpretation consistency (factory, constructors, environment)
-/

namespace Lambda

variable {T : LExprParams}
variable (tcInterp : TyConstrInterp)
variable (opInterp : OpInterp tcInterp)
variable (fvarVal : FreeVarVal T tcInterp)
variable (vt : TyVarVal)

/-- A free-variable valuation `fvarVal` is consistent with an environment `env`
when every binding `env x = some e` that is well-typed at `ty` denotes to the
same value as `fvarVal x (substTyVars vt ty)`. -/
def Env.InterpConsistent (env : T.Identifier → Option (LExpr T.mono)) (fvarVal : FreeVarVal T tcInterp) : Prop :=
  ∀ (vt : TyVarVal) (x : T.Identifier) (e : LExpr T.mono) (ty : LMonoTy),
    env x = some e →
    ∀ (h : LExpr.HasTypeA [] e ty),
      LExpr.denote tcInterp opInterp fvarVal vt .nil e ty h = fvarVal x (ty.substTyVars vt)

/-- Bundled interpretation consistency assumptions.
- `factory` : `Factory.InterpConsistent tcInterp opInterp F` — factory bodies/evals are interp-consistent
- `constr` : `ConstrInterpConsistent tcInterp opInterp F` — constructor interp consistency
- `env` : `Env.InterpConsistent tcInterp opInterp env fvarVal` — env values denote as fvarVal
-/
structure InterpConsistent [DecidableEq T.IDMeta] (F : @Factory T)
    (env : Env T) where
  factory : Factory.InterpConsistent tcInterp opInterp F
  constr : ConstrInterpConsistent tcInterp opInterp F
  env : Env.InterpConsistent tcInterp opInterp env fvarVal

/-! ### State substitution and denotation -/

section
variable [DecidableEq T.IDMeta] [Inhabited T.mono.base.IDMeta]

omit [Inhabited T.mono.base.IDMeta] in
/-- Values from a state map are well-typed at the types given by `envTys`,
weakened to any binder context `Δ`. -/
private theorem state_map_forall₂_hasTypeA
    {Δ : List LMonoTy}
    (entries : List (T.Identifier × LExpr T.mono))
    {env : T.Identifier → Option (LExpr T.mono)}
    (h_in_env : ∀ (k : T.Identifier) (v : LExpr T.mono),
      (k, v) ∈ entries → env k = some v)
    (hEnvTy : Env.Typed env)
    (hEnvLC : ∀ (x : T.Identifier) (v : LExpr T.mono),
      env x = some v → LExpr.lcAt 0 v = true)
    : List.Forall₂ (LExpr.HasTypeA Δ) (entries.map Prod.snd)
        (entries.map (fun (k, _) =>
          match Map.find? hEnvTy.tyMap k with
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
      obtain ⟨ty, h_envTys_k⟩ := hEnvTy.cover k v h_env_kv
      simp only [h_envTys_k]
      have h_wt := hEnvTy.wt k v ty h_env_kv h_envTys_k
      have h_lc := hEnvLC k v h_env_kv
      exact HasTypeA_weaken h_wt h_lc
    · exact ih (fun k' v' h_mem => h_in_env k' v' (List.mem_cons_of_mem _ h_mem))

omit [Inhabited T.mono.base.IDMeta] in
/-- If every key in `ks` is in `env`, and every env value has a type in `envTys`,
then the annotation map derived from `ks` and `envTys` is a sub-annotation of `envTys`. -/
private theorem fvars_annotated_by_keySet
    (ks : List (T.Identifier × LExpr T.mono))
    {env : T.Identifier → Option (LExpr T.mono)}
    (e : LExpr T.mono)
    (h_in_env : ∀ (k : T.Identifier) (v : LExpr T.mono),
      (k, v) ∈ ks → env k = some v)
    (hEnvTy : Env.Typed env)
    (hAnnot : fvars_annotated_by hEnvTy.tyMap e)
    : fvars_annotated_by
        (ks.map Prod.fst |>.zip (ks.map (fun (k, _) =>
          match Map.find? hEnvTy.tyMap k with
          | some ty => ty
          | none => .bool)))
        e := by
  apply fvars_annotated_by_of_find_sub _ hEnvTy.tyMap e _ hAnnot
  intro k v h_find_zip
  have h_mem := Map.find?_mem _ _ _ h_find_zip
  have h_k_mem := (List.of_mem_zip h_mem).1
  rw [List.mem_map] at h_k_mem
  obtain ⟨⟨k', w⟩, h_kw_mem, h_k_eq⟩ := h_k_mem
  simp at h_k_eq; subst h_k_eq
  have h_env_kw := h_in_env k' w h_kw_mem
  obtain ⟨ty, h_envTys_k⟩ := hEnvTy.cover k' w h_env_kw
  obtain ⟨i, h_key_i, h_val_i, h_first_i⟩ := Map.find?_index h_find_zip
  have h_tys_len : (ks.map Prod.fst).length ≤
      (ks.map (fun (k, _) => match Map.find? hEnvTy.tyMap k with | some ty => ty | none => .bool)).length := by
    simp
  have h_tys_len' : (ks.map (fun (k, _) => match Map.find? hEnvTy.tyMap k with | some ty => ty | none => .bool)).length ≤
      (ks.map Prod.fst).length := by
    simp
  rw [List.map_fst_zip h_tys_len] at h_key_i
  rw [List.map_snd_zip h_tys_len'] at h_val_i
  simp only [List.getElem?_map] at h_val_i
  rw [List.getElem?_map] at h_key_i
  cases h_ks_i : ks[i]? with
  | none => simp [h_ks_i] at h_key_i
  | some p =>
    simp [h_ks_i] at h_key_i h_val_i
    rw [h_key_i, h_envTys_k] at h_val_i
    exact h_val_i ▸ h_envTys_k

omit [Inhabited T.mono.base.IDMeta] in
/-- Substituting free variables from an environment preserves typing. -/
private theorem substFvarsFromEnv_type_preserved
    {env : Env T} {e : LExpr T.mono} {τ : LMonoTy} {Δ : List LMonoTy}
    (h : LExpr.HasTypeA Δ e τ)
    (hEnvLC : ∀ (x : T.Identifier) (v : LExpr T.mono), env x = some v → LExpr.lcAt 0 v = true)
    (hEnvTy : Env.Typed env)
    (hAnnot : fvars_annotated_by hEnvTy.tyMap e)
    : LExpr.HasTypeA Δ (LExpr.substFvarsFromEnv env e) τ := by
  induction e generalizing τ Δ with
  | const => exact h
  | op => exact h
  | bvar => exact h
  | fvar m name ty =>
    simp only [LExpr.substFvarsFromEnv]
    cases henv : env name with
    | none => exact h
    | some v =>
      cases h with
      | fvar =>
        obtain ⟨ty', h_ty'⟩ := hEnvTy.cover name v henv
        have h_annot_eq : τ = ty' := hAnnot ty' h_ty'
        rw [h_annot_eq]
        exact HasTypeA_weaken (hEnvTy.wt name v ty' henv h_ty') (hEnvLC name v henv)
  | abs m nm aty body ih =>
    simp only [LExpr.substFvarsFromEnv]
    cases h with
    | abs h_body => exact .abs (ih h_body hAnnot)
  | quant m qk nm qty tr body ih_tr ih_body =>
    simp only [LExpr.substFvarsFromEnv]
    cases h with
    | quant h_tr h_body =>
      exact .quant (ih_tr h_tr hAnnot.1) (ih_body h_body hAnnot.2)
  | app m fn arg ih_fn ih_arg =>
    simp only [LExpr.substFvarsFromEnv]
    cases h with
    | app h_fn h_arg =>
      exact .app (ih_fn h_fn hAnnot.1) (ih_arg h_arg hAnnot.2)
  | ite m c t f ihc iht ihf =>
    simp only [LExpr.substFvarsFromEnv]
    cases h with
    | ite h_c h_t h_f =>
      exact .ite (ihc h_c hAnnot.1) (iht h_t hAnnot.2.1) (ihf h_f hAnnot.2.2)
  | eq m e1 e2 ih1 ih2 =>
    simp only [LExpr.substFvarsFromEnv]
    cases h with
    | eq h1 h2 =>
      exact .eq (ih1 h1 hAnnot.1) (ih2 h2 hAnnot.2)

omit [Inhabited T.mono.base.IDMeta] in
/-- Substituting free variables from an environment preserves denotation.

Requires that the environment is:
- interpretation-consistent (`hEnv`): env values denote to what `fvarVal` gives,
- locally closed (`hEnvLC`): env values have no dangling bound variables,
- well-typed (`hEnvTy`): env values are well-typed at the types given by `hEnvTy.tyMap`,
- annotated (`hAnnot`): fvar annotations in `e` match `hEnvTy.tyMap`. -/
private theorem substFvarsFromEnv_denote_preserved
    {env : Env T} {e : LExpr T.mono} {τ : LMonoTy}
    {Δ : List LMonoTy} {bvarVal : BVarVal tcInterp vt Δ}
    (h₁ : LExpr.HasTypeA Δ e τ)
    (h₂ : LExpr.HasTypeA Δ (LExpr.substFvarsFromEnv env e) τ)
    (hEnv : Env.InterpConsistent tcInterp opInterp env fvarVal)
    (hEnvLC : ∀ (x : T.Identifier) (v : LExpr T.mono),
      env x = some v → LExpr.lcAt 0 v = true)
    (hEnvTy : Env.Typed env)
    (hAnnot : fvars_annotated_by hEnvTy.tyMap e)
    : LExpr.denote tcInterp opInterp fvarVal vt bvarVal e τ h₁ =
      LExpr.denote tcInterp opInterp fvarVal vt bvarVal
        (LExpr.substFvarsFromEnv env e) τ h₂ := by
  induction e generalizing τ Δ bvarVal with
  | const => rfl
  | op => rfl
  | bvar => rfl
  | fvar m name ty =>
    cases h₁ with
    | fvar =>
      simp only [LExpr.substFvarsFromEnv] at h₂
      split at h₂
      · rename_i v henv
        simp only [LExpr.substFvarsFromEnv, henv, LExpr.denote]
        have ⟨ty', h_ty'⟩ := hEnvTy.cover name v henv
        have h_annot_eq : τ = ty' := hAnnot ty' h_ty'
        subst h_annot_eq
        have h_wt := hEnvTy.wt name v τ henv h_ty'
        have h_lc := hEnvLC name v henv
        rw [← hEnv vt name v τ henv h_wt]
        exact denote_irrel_of_lcAt tcInterp opInterp fvarVal vt h_lc h_wt h₂ .nil bvarVal
      · rename_i henv
        simp only [LExpr.substFvarsFromEnv, henv]
  | abs m nm aty body ih =>
    simp only [LExpr.substFvarsFromEnv] at h₂ ⊢
    cases h₁ with
    | abs h_body =>
      cases h₂ with
      | abs h_subst_body =>
        rw [denote_abs bvarVal h_body, denote_abs bvarVal h_subst_body]
        funext v
        exact ih h_body h_subst_body hAnnot
  | quant m qk nm qty tr body ih_tr ih_body =>
    simp only [LExpr.substFvarsFromEnv] at h₂ ⊢
    cases h₁ with
    | quant h_tr h_body =>
      cases h₂ with
      | quant h_tr' h_subst_body =>
        exact denote_quant_congr h_body h_subst_body _ _ fun v =>
          ih_body h_body h_subst_body hAnnot.2
  | app m fn arg ih_fn ih_arg =>
    simp only [LExpr.substFvarsFromEnv] at h₂ ⊢
    cases h₁ with
    | app h_fn h_arg =>
      cases h₂ with
      | app h_fn' h_arg' =>
        rename_i aty₁ aty₂
        have h_fn_tp := substFvarsFromEnv_type_preserved h_fn hEnvLC hEnvTy hAnnot.1
        have h_aty_eq : LMonoTy.arrow aty₁ τ = LMonoTy.arrow aty₂ τ :=
          HasTypeA_unique h_fn_tp h_fn'
        have h_aty : aty₁ = aty₂ := by cases h_aty_eq; rfl
        subst h_aty
        rw [denote_app bvarVal h_fn h_arg,
            denote_app bvarVal h_fn' h_arg']
        rw [ih_fn h_fn h_fn' hAnnot.1, ih_arg h_arg h_arg' hAnnot.2]
  | ite m c t f ihc iht ihf =>
    simp only [LExpr.substFvarsFromEnv] at h₂ ⊢
    cases h₁ with
    | ite h_c h_t h_f =>
      cases h₂ with
      | ite h_c' h_t' h_f' =>
        have ihc_eq := ihc (bvarVal := bvarVal) h_c h_c' hAnnot.1
        have iht_eq := iht (bvarVal := bvarVal) h_t h_t' hAnnot.2.1
        have ihf_eq := ihf (bvarVal := bvarVal) h_f h_f' hAnnot.2.2
        rw [denote_ite bvarVal h_c h_t h_f,
            denote_ite bvarVal h_c' h_t' h_f',
            ihc_eq, iht_eq, ihf_eq]
  | eq m e1 e2 ih1 ih2 =>
    simp only [LExpr.substFvarsFromEnv] at h₂ ⊢
    cases h₁ with
    | eq h_1 h_2 =>
      cases h₂ with
      | eq h_1' h_2' =>
        rename_i ty₁ ty₂
        have h_1_tp := substFvarsFromEnv_type_preserved h_1 hEnvLC hEnvTy hAnnot.1
        have h_ty_eq : ty₁ = ty₂ := HasTypeA_unique h_1_tp h_1'
        subst h_ty_eq
        have ih_eq1 := ih1 (bvarVal := bvarVal) h_1 h_1' hAnnot.1
        have ih_eq2 := ih2 (bvarVal := bvarVal) h_2 h_2' hAnnot.2
        by_cases heq : LExpr.denote tcInterp opInterp fvarVal vt bvarVal e1 _ h_1 =
            LExpr.denote tcInterp opInterp fvarVal vt bvarVal e2 _ h_2
        · rw [denote_eq_true bvarVal h_1 h_2 _ heq,
              denote_eq_true bvarVal h_1' h_2' _
                (by rw [← ih_eq1, ← ih_eq2]; exact heq)]
        · rw [denote_eq_false bvarVal h_1 h_2 _ heq,
              denote_eq_false bvarVal h_1' h_2' _
                (by rw [← ih_eq1, ← ih_eq2]; exact heq)]

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
- `hEnvTy`: environment values are well-typed (type map, consistency, coverage).
- `hAnnot`: free variable annotations in `e₁` match `hEnvTy.tyMap`. -/
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
    (hEnvTy : Env.Typed env)
    (hAnnot : fvars_annotated_by hEnvTy.tyMap e₁)
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
        rw[ih h_arg h_arg' hOps.2 hAnnot.2]
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
        rw[ih h_fn h_fn' hOps.1 hAnnot.1]
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
        rw [ih h_c h_c' hOps.1 hAnnot.1]
  | ite_reduce_then_branch econd ethen ethen' eelse hstep' ih =>
    cases h₁ with
    | ite h_c h_t h_e =>
      cases h₂ with
      | ite h_c' h_t' h_e' =>
        rw [denote_ite .nil h_c h_t h_e,
            denote_ite .nil h_c' h_t' h_e']
        rw [ih h_t h_t' hOps.2.1 hAnnot.2.1]
  | ite_reduce_else_branch econd ethen eelse eelse' hstep' ih =>
    cases h₁ with
    | ite h_c h_t h_e =>
      cases h₂ with
      | ite h_c' h_t' h_e' =>
        rw [denote_ite .nil h_c h_t h_e,
            denote_ite .nil h_c' h_t' h_e']
        rw [ih h_e h_e' hOps.2.2 hAnnot.2.2]
  | eq_reduce_true e1 e2 heql =>
    cases h₁ with
    | eq h_1 h_2 =>
      rw [denote_eq_true .nil h_1 h_2 _
          (eql_true_implies_denote_eq tcInterp opInterp fvarVal vt h_1 h_2
            hOps.1 hOps.2 hFwf hcwf heql)]
      rfl
  | eq_reduce_false e1 e2 heql =>
    cases h₁ with
    | eq h_1 h_2 =>
      rw [denote_eq_false .nil h_1 h_2 _
          (eql_false_implies_denote_ne tcInterp opInterp fvarVal vt h_1 h_2
            hOps.1 hOps.2 hFwf hcwf htfwf heql hConstrIC)]
      rfl
  | eq_reduce_lhs e1 e1' e2 hstep' ih =>
    cases h₁ with
    | eq h_1 h_2 =>
      cases h₂ with
      | eq h_1' h_2' =>
        have hty := HasTypeA_unique h_2 h_2'; subst hty
        have ih_eq := ih h_1 h_1' hOps.1 hAnnot.1
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
        have ih_eq := ih h_2 h_2' hOps.2 hAnnot.2
        by_cases heq : LExpr.denote tcInterp opInterp fvarVal vt .nil v1 _ h_1 =
            LExpr.denote tcInterp opInterp fvarVal vt .nil e2 _ h_2
        · rw [denote_eq_true .nil h_1 h_2 _ heq,
              denote_eq_true .nil h_1' h_2' _
                (by rw [← ih_eq]; exact heq)]
        · rw [denote_eq_false .nil h_1 h_2 _ heq,
              denote_eq_false .nil h_1' h_2' _
                (by rw [← ih_eq]; exact heq)]
  | abs_subst_fvars body x hfv =>
    cases h₁ with
    | abs h_body =>
      cases h₂ with
      | abs h_subst_body =>
        rw [denote_abs .nil h_body, denote_abs .nil h_subst_body]
        funext v
        exact substFvarsFromEnv_denote_preserved tcInterp opInterp fvarVal vt
          h_body h_subst_body hEnv hEnvLC hEnvTy hAnnot
  | quant_subst_fvars_body tr body x hfv =>
    cases h₁ with
    | quant h_tr h_body =>
      cases h₂ with
      | quant h_tr' h_subst_body =>
        have h_body_eq : ∀ v, LExpr.denote tcInterp opInterp fvarVal vt (.cons v .nil)
              body .bool h_body =
            LExpr.denote tcInterp opInterp fvarVal vt (.cons v .nil)
              (LExpr.substFvarsFromEnv env body) .bool h_subst_body :=
          fun v => substFvarsFromEnv_denote_preserved tcInterp opInterp fvarVal vt
            h_body h_subst_body hEnv hEnvLC hEnvTy hAnnot.2
        exact denote_quant_congr h_body h_subst_body _ _ h_body_eq
  | quant_subst_fvars_trigger tr body x hfv =>
    cases h₁ with
    | quant h_tr h_body =>
      cases h₂ with
      | quant h_tr' h_body' =>
        exact denote_quant_congr h_body h_body' _ _ fun _ => rfl
  | expand_fn e callee fnbody new_body args fn tySubst hcall hbody htySubst heq =>
    -- Step 1: Decompose the call
    obtain ⟨argTys, ty_op, m, name, h_args, hty_op, h_callee_eq, h_denote_e⟩ :=
      callOfLFunc_denote tcInterp opInterp fvarVal vt hcall h₁
    -- Step 2: Extract from OpsConsistent
    obtain ⟨tySubst', htySubst', h_ty_op_eq⟩ := OpsConsistent_callOfLFunc hOps hcall
    rw [h_callee_eq] at htySubst htySubst'
    have htySubst'_ct := LFunc.computeTypeSubst_of_opTypeSubst (args := args) htySubst'
    have h_tySubst_eq : tySubst' = tySubst := Option.some.inj (htySubst'_ct.symm.trans htySubst)
    subst h_tySubst_eq
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

/-- A single step preserves well-typedness.

Assumptions:
- `hFwt`: factory function bodies are well-typed.
- `hFeval`: factory concrete evaluators produce well-typed results.
- `hOps`: every op referenced in `e₁` has a corresponding factory entry.
- `hFwf`: the factory is well-formed (arities, types match declarations).
- `hEnvLC`: environment values are locally closed.
- `hEnvTy`: environment values are well-typed (type map, consistency, coverage).
- `hAnnot`: free variable annotations in `e₁` match `hEnvTy.tyMap`. -/
theorem Step.type_preserved
    {F : @Factory T} {env : Env T}
    {e₁ e₂ : LExpr T.mono} {τ : LMonoTy}
    (hstep : Step F env e₁ e₂)
    (h₁ : LExpr.HasTypeA [] e₁ τ)
    (hFwt : Factory.WellTyped F)
    (hFeval : Factory.EvalWellTyped F)
    (hOps : OpsConsistent F e₁)
    (hEnvLC : ∀ (x : T.Identifier) (e : LExpr T.mono), env x = some e → LExpr.lcAt 0 e = true)
    (hEnvTy : Env.Typed env)
    (hAnnot : fvars_annotated_by hEnvTy.tyMap e₁)
    : LExpr.HasTypeA [] e₂ τ := by
  induction hstep generalizing τ with
  | expand_fvar x e henv =>
    cases h₁ with
    | fvar =>
      have ⟨ty, hty⟩ := hEnvTy.cover x e henv
      have hty_eq : τ = ty := hAnnot ty hty
      subst hty_eq
      exact hEnvTy.wt x e τ henv hty
  | beta e1 v2 eres heq =>
    subst heq
    have ⟨aty, h_fn, h_arg⟩ := HasTypeA.app_inv h₁
    cases h_fn with
    | abs h_body =>
      have h_tc := substK_typeCheck (e := e1) (Δ₁ := []) (fun _ => h_arg)
      simp at h_tc
      rw [LExpr.HasTypeA_iff_typeCheck] at h_body ⊢
      simp only [LExpr.subst]
      rw [h_tc, h_body]
  | reduce_2 e1 e2 e2' hstep ih =>
    have ⟨aty, h_fn, h_arg⟩ := HasTypeA.app_inv h₁
    have h_arg' : LExpr.HasTypeA [] e2' aty :=
      ih h_arg hOps.2 hAnnot.2
    exact .app h_fn h_arg'
  | reduce_1 e1 e1' e2 hstep ih =>
    have ⟨aty, h_fn, h_arg⟩ := HasTypeA.app_inv h₁
    have h_fn' : LExpr.HasTypeA [] e1' (.arrow aty τ) :=
      ih h_fn hOps.1 hAnnot.1
    exact .app h_fn' h_arg
  | ite_reduce_then ethen eelse =>
    have ⟨_, h_t, _⟩ := HasTypeA.ite_inv h₁
    exact h_t
  | ite_reduce_else ethen eelse =>
    have ⟨_, _, h_e⟩ := HasTypeA.ite_inv h₁
    exact h_e
  | ite_reduce_cond econd econd' ethen eelse hstep ih =>
    have ⟨h_c, h_t, h_e⟩ := HasTypeA.ite_inv h₁
    have h_c' : LExpr.HasTypeA [] econd' .bool :=
      ih h_c hOps.1 hAnnot.1
    exact .ite h_c' h_t h_e
  | ite_reduce_then_branch econd ethen ethen' eelse hstep ih =>
    have ⟨h_c, h_t, h_e⟩ := HasTypeA.ite_inv h₁
    have h_t' : LExpr.HasTypeA [] ethen' τ :=
      ih h_t hOps.2.1 hAnnot.2.1
    exact .ite h_c h_t' h_e
  | ite_reduce_else_branch econd ethen eelse eelse' hstep ih =>
    have ⟨h_c, h_t, h_e⟩ := HasTypeA.ite_inv h₁
    have h_e' : LExpr.HasTypeA [] eelse' τ :=
      ih h_e hOps.2.2 hAnnot.2.2
    exact .ite h_c h_t h_e'
  | eq_reduce_true e1 e2 heql =>
    have ⟨_, h_τ, _, _⟩ := HasTypeA.eq_inv h₁
    subst h_τ; exact .const
  | eq_reduce_false e1 e2 heql =>
    have ⟨_, h_τ, _, _⟩ := HasTypeA.eq_inv h₁
    subst h_τ; exact .const
  | eq_reduce_lhs e1 e1' e2 hstep ih =>
    have ⟨eqty, h_τ, h_1, h_2⟩ := HasTypeA.eq_inv h₁
    subst h_τ
    have h_1' : LExpr.HasTypeA [] e1' eqty :=
      ih h_1 hOps.1 hAnnot.1
    exact .eq h_1' h_2
  | eq_reduce_rhs e1 e2 e2' hstep ih =>
    have ⟨eqty, h_τ, h_1, h_2⟩ := HasTypeA.eq_inv h₁
    subst h_τ
    have h_2' : LExpr.HasTypeA [] e2' eqty :=
      ih h_2 hOps.2 hAnnot.2
    exact .eq h_1 h_2'
  | expand_fn e callee fnbody new_body args fn tySubst hcall hbody htysubst heq =>
    subst heq
    -- Get tySubst' from OpsConsistent, then unify with tySubst
    obtain ⟨tySubst', htySubst', h_ty_op_eq⟩ := OpsConsistent_callOfLFunc hOps hcall
    have h_ts_eq : tySubst' = tySubst := by
      have h_ct := LFunc.computeTypeSubst_of_opTypeSubst (args := args) htySubst'
      rw [h_ct] at htysubst; cases htysubst; rfl
    subst h_ts_eq
    -- Get argTys and callee info from typing
    obtain ⟨argTys, ty_op, md, name, h_callee_eq, h_args, hty_op, _⟩ :=
      callOfLFunc_output_type hcall h₁
    have h_ty_op_val := h_ty_op_eq md name ty_op h_callee_eq
    have h_subst_arrow := subst_mkArrow' tySubst' fn.output (fn.inputs.map Prod.snd)
    rw [h_subst_arrow] at h_ty_op_val
    rw [hty_op] at h_ty_op_val
    have h_len : argTys.length = ((fn.inputs.map Prod.snd).map (LMonoTy.subst tySubst')).length := by
      simp; exact h_args.length_eq.symm.trans (Factory.callOfLFunc_arity hcall)
    have ⟨h_τ_eq, h_argTys_eq⟩ := LMonoTy.mkArrow'_injective h_len h_ty_op_val
    subst h_τ_eq h_argTys_eq
    -- Get body typing from Factory.WellTyped
    obtain ⟨_, _, _, h_callee_op, h_get⟩ := Factory.callOfLFunc_getElem? hcall
    rw [h_callee_eq] at h_callee_op; cases h_callee_op
    have h_fn_mem : name.name ∈ F := Factory.getElem?_some_implies_mem h_get
    have h_fn_eq : F[name.name] = fn := Factory.getElem?_some_getElem h_get
    have ⟨h_body_wt, h_body_annot⟩ := h_fn_eq ▸ hFwt name.name h_fn_mem fnbody (h_fn_eq ▸ hbody)
    -- applySubst preserves typing
    have h_applySubst_wt : LExpr.HasTypeA [] (fnbody.applySubst tySubst') (LMonoTy.subst tySubst' fn.output) :=
      applySubst_typeCheck tySubst' h_body_wt
    -- Annotation after applySubst
    have h_annot_subst := applySubst_fvars_annotated (S := tySubst') h_body_annot
    have h_map_eq : fn.inputs.map (fun (k, v) => (k, LMonoTy.subst tySubst' v)) =
        (fn.inputs.map Prod.fst).zip (fn.inputs.map Prod.snd |>.map (LMonoTy.subst tySubst')) := by
      rw [List.map_map]; induction fn.inputs with
      | nil => rfl
      | cons h t ih => simp [ih]
    rw [h_map_eq] at h_annot_subst
    -- Connect bindings structure
    have h_arity := Factory.callOfLFunc_arity hcall
    have h_keys_len : fn.inputs.keys.length = args.length := by
      rw [ListMap.keys_eq_map_fst]; simp [h_arity]
    have h_zip_fst : (fn.inputs.keys.zip args).map Prod.fst = fn.inputs.keys :=
      zip_map_fst_eq _ _ h_keys_len
    have h_zip_snd : (fn.inputs.keys.zip args).map Prod.snd = args :=
      zip_map_snd_eq _ _ h_keys_len
    -- Forall₂ for bindings
    have h_wt_bindings : List.Forall₂ (LExpr.HasTypeA [])
        ((fn.inputs.keys.zip args).map Prod.snd)
        (fn.inputs.map Prod.snd |>.map (LMonoTy.subst tySubst')) := by
      rw [h_zip_snd]; exact h_args
    -- Annotation matches
    have h_annot_match : fvars_annotated_by
        ((fn.inputs.keys.zip args).map Prod.fst |>.zip
          (fn.inputs.map Prod.snd |>.map (LMonoTy.subst tySubst')))
        (fnbody.applySubst tySubst') := by
      rw [h_zip_fst, ListMap.keys_eq_map_fst]; exact h_annot_subst
    exact substFvarsLifting_typeCheck h_wt_bindings h_annot_match h_applySubst_wt
  | eval_fn e callee e' args fn denotefn hcall heval hresult =>
    -- Get tySubst from OpsConsistent
    obtain ⟨tySubst, htySubst, h_ty_op_eq⟩ := OpsConsistent_callOfLFunc hOps hcall
    -- Get argTys and callee info from typing
    obtain ⟨argTys, ty_op, md, name, h_callee_eq, h_args, hty_op, _⟩ :=
      callOfLFunc_output_type hcall h₁
    have h_ty_op_val := h_ty_op_eq md name ty_op h_callee_eq
    have h_subst_arrow := subst_mkArrow' tySubst fn.output (fn.inputs.map Prod.snd)
    rw [h_subst_arrow] at h_ty_op_val
    rw [hty_op] at h_ty_op_val
    have h_len : argTys.length = ((fn.inputs.map Prod.snd).map (LMonoTy.subst tySubst)).length := by
      simp; exact h_args.length_eq.symm.trans (Factory.callOfLFunc_arity hcall)
    have ⟨h_τ_eq, h_argTys_eq⟩ := LMonoTy.mkArrow'_injective h_len h_ty_op_val
    subst h_τ_eq h_argTys_eq
    -- Get fn membership
    obtain ⟨_, _, _, h_callee_op, h_get⟩ := Factory.callOfLFunc_getElem? hcall
    rw [h_callee_eq] at h_callee_op; cases h_callee_op
    have h_fn_mem : name.name ∈ F := Factory.getElem?_some_implies_mem h_get
    have h_fn_eq : F[name.name] = fn := Factory.getElem?_some_getElem h_get
    -- Apply EvalWellTyped
    exact h_fn_eq ▸ hFeval name.name h_fn_mem denotefn (h_fn_eq ▸ heval)
      _ args e' tySubst hresult.symm (h_fn_eq ▸ h_args)
  | abs_subst_fvars body x hfv =>
    cases h₁ with
    | abs h_body =>
      apply LExpr.HasTypeA.abs
      exact substFvarsFromEnv_type_preserved h_body hEnvLC hEnvTy hAnnot
  | quant_subst_fvars_body tr body x hfv =>
    cases h₁ with
    | quant h_tr h_body =>
      have ⟨h_annot_tr, h_annot_body⟩ := hAnnot
      exact LExpr.HasTypeA.quant h_tr
        (substFvarsFromEnv_type_preserved h_body hEnvLC hEnvTy h_annot_body)
  | quant_subst_fvars_trigger tr body x hfv =>
    cases h₁ with
    | quant h_tr h_body =>
      have ⟨h_annot_tr, h_annot_body⟩ := hAnnot
      exact LExpr.HasTypeA.quant
        (substFvarsFromEnv_type_preserved h_tr hEnvLC hEnvTy h_annot_tr)
        h_body

omit [Inhabited T.mono.base.IDMeta] [DecidableEq T.IDMeta] in
/-- `substFvarsFromEnv` preserves `fvars_annotated_by`, provided all environment
values satisfy `fvars_annotated_by`. -/
private theorem substFvarsFromEnv_fvars_annotated [DecidableEq T.IDMeta]
    {e : LExpr T.mono}
    {env : Env T} {tyMap : Map T.Identifier LMonoTy}
    (h : fvars_annotated_by tyMap e)
    (hEnvAnnot : ∀ (x : T.Identifier) (v : LExpr T.mono), env x = some v → fvars_annotated_by tyMap v)
    : fvars_annotated_by tyMap (LExpr.substFvarsFromEnv env e) := by
  induction e with
  | const | bvar | op => exact h
  | fvar m name ty =>
    simp only [LExpr.substFvarsFromEnv]
    cases henv : env name with
    | none => exact h
    | some v => exact hEnvAnnot name v henv
  | abs m nm ty body ih =>
    simp only [LExpr.substFvarsFromEnv]
    exact ih h
  | quant m qk nm ty tr body ih_tr ih_body =>
    simp only [LExpr.substFvarsFromEnv]
    simp only [fvars_annotated_by] at h ⊢
    exact ⟨ih_tr h.1, ih_body h.2⟩
  | app m fn arg ih_fn ih_arg =>
    simp only [LExpr.substFvarsFromEnv]
    simp only [fvars_annotated_by] at h ⊢
    exact ⟨ih_fn h.1, ih_arg h.2⟩
  | eq m e1 e2 ih1 ih2 =>
    simp only [LExpr.substFvarsFromEnv]
    simp only [fvars_annotated_by] at h ⊢
    exact ⟨ih1 h.1, ih2 h.2⟩
  | ite m c t f ihc iht ihf =>
    simp only [LExpr.substFvarsFromEnv]
    simp only [fvars_annotated_by] at h ⊢
    exact ⟨ihc h.1, iht h.2.1, ihf h.2.2⟩

omit [Inhabited T.mono.base.IDMeta] [DecidableEq T.IDMeta] in
/-- `substFvarsFromEnv` preserves `OpsConsistent`, provided all environment
values satisfy `OpsConsistent`. -/
private theorem substFvarsFromEnv_OpsConsistent
    {F : @Factory T} {e : LExpr T.mono}
    {env : Env T}
    (hOps : OpsConsistent F e)
    (hEnvOps : ∀ (x : T.Identifier) (v : LExpr T.mono), env x = some v → OpsConsistent F v)
    : OpsConsistent F (LExpr.substFvarsFromEnv env e) := by
  induction e with
  | const | bvar | op => exact hOps
  | fvar m name ty =>
    simp only [LExpr.substFvarsFromEnv]
    cases henv : env name with
    | none => exact hOps
    | some v => exact hEnvOps name v henv
  | abs m nm ty body ih =>
    simp only [LExpr.substFvarsFromEnv, OpsConsistent]
    exact ih hOps
  | quant m qk nm ty tr body ih_tr ih_body =>
    simp only [LExpr.substFvarsFromEnv, OpsConsistent]
    exact ⟨ih_tr hOps.1, ih_body hOps.2⟩
  | app m fn arg ih_fn ih_arg =>
    simp only [LExpr.substFvarsFromEnv, OpsConsistent]
    exact ⟨ih_fn hOps.1, ih_arg hOps.2⟩
  | ite m c t f ihc iht ihf =>
    simp only [LExpr.substFvarsFromEnv, OpsConsistent]
    exact ⟨ihc hOps.1, iht hOps.2.1, ihf hOps.2.2⟩
  | eq m e1 e2 ih1 ih2 =>
    simp only [LExpr.substFvarsFromEnv, OpsConsistent]
    exact ⟨ih1 hOps.1, ih2 hOps.2⟩

/-- A single step preserves `OpsConsistent`. -/
theorem Step.OpsConsistent_preserved
    {F : @Factory T} {env : Env T}
    {e₁ e₂ : LExpr T.mono}
    (hstep : Step F env e₁ e₂)
    (hOps : OpsConsistent F e₁)
    (hEnvOps : ∀ (x : T.Identifier) (e : LExpr T.mono), env x = some e → OpsConsistent F e)
    (hFBodyOps : Factory.BodyOpsConsistent F)
    (hFEvalOps : Factory.EvalOpsConsistent F)
    : OpsConsistent F e₂ := by
  induction hstep with
  | expand_fvar x e henv => exact hEnvOps x e henv
  | beta e1 v2 eres heq =>
    subst heq
    simp only [LExpr.subst]
    exact OpsConsistent_substK hOps.1 (fun _ => hOps.2)
  | reduce_1 e1 e1' e2 hstep ih =>
    exact ⟨ih hOps.1, hOps.2⟩
  | reduce_2 e1 e2 e2' hstep ih =>
    exact ⟨hOps.1, ih hOps.2⟩
  | ite_reduce_then ethen eelse =>
    exact hOps.2.1
  | ite_reduce_else ethen eelse =>
    exact hOps.2.2
  | ite_reduce_cond econd econd' ethen eelse hstep ih =>
    exact ⟨ih hOps.1, hOps.2.1, hOps.2.2⟩
  | ite_reduce_then_branch econd ethen ethen' eelse hstep ih =>
    exact ⟨hOps.1, ih hOps.2.1, hOps.2.2⟩
  | ite_reduce_else_branch econd ethen eelse eelse' hstep ih =>
    exact ⟨hOps.1, hOps.2.1, ih hOps.2.2⟩
  | eq_reduce_true e1 e2 heql =>
    trivial
  | eq_reduce_false e1 e2 heql =>
    trivial
  | eq_reduce_lhs e1 e1' e2 hstep ih =>
    exact ⟨ih hOps.1, hOps.2⟩
  | eq_reduce_rhs e1 e2 e2' hstep ih =>
    exact ⟨hOps.1, ih hOps.2⟩
  | expand_fn e callee fnbody new_body args fn tySubst hcall hbody htysubst heq =>
    subst heq
    -- Get fn membership and name
    obtain ⟨md, name, ty_callee, h_callee_op, h_get⟩ := Factory.callOfLFunc_getElem? hcall
    have h_fn_mem : name.name ∈ F := Factory.getElem?_some_implies_mem h_get
    have h_fn_eq : F[name.name] = fn := Factory.getElem?_some_getElem h_get
    -- Body satisfies OpsConsistent after applySubst
    have h_body_eq : (F[name.name]).body = some fnbody := by rw [h_fn_eq]; exact hbody
    have h_body_ops : OpsConsistent F (fnbody.applySubst tySubst) :=
      hFBodyOps name.name h_fn_mem fnbody tySubst h_body_eq
    -- Args satisfy OpsConsistent
    have h_args_ops : ∀ a ∈ args, OpsConsistent F a :=
      OpsConsistent_callOfLFunc_args hOps hcall
    -- substFvarsLifting preserves OpsConsistent
    have h_sm_ops : ∀ k v, Map.find? (fn.inputs.keys.zip args) k = some v → OpsConsistent F v := by
      intro k v hfind
      have h_mem := Map.find?_mem _ _ _ hfind
      have h_in_args : v ∈ args := (List.of_mem_zip h_mem).2
      exact h_args_ops v h_in_args
    exact OpsConsistent_substFvarsLifting h_body_ops h_sm_ops
  | eval_fn e callee e' args fn denotefn hcall heval hresult =>
    obtain ⟨_, name, _, _, h_get⟩ := Factory.callOfLFunc_getElem? hcall
    have h_fn_mem : name.name ∈ F := Factory.getElem?_some_implies_mem h_get
    have h_fn_eq : F[name.name] = fn := Factory.getElem?_some_getElem h_get
    have h_eval_eq : (F[name.name]).concreteEval = some denotefn := by rw [h_fn_eq]; exact heval
    exact hFEvalOps name.name h_fn_mem denotefn _ args e' h_eval_eq hresult
  | abs_subst_fvars body x hfv =>
    exact substFvarsFromEnv_OpsConsistent hOps hEnvOps
  | quant_subst_fvars_body tr body x hfv =>
    exact ⟨hOps.1, substFvarsFromEnv_OpsConsistent hOps.2 hEnvOps⟩
  | quant_subst_fvars_trigger tr body x hfv =>
    exact ⟨substFvarsFromEnv_OpsConsistent hOps.1 hEnvOps, hOps.2⟩

/-- A single step preserves `fvars_annotated_by`. -/
theorem Step.fvars_annotated_preserved
    {F : @Factory T} {env : Env T}
    {e₁ e₂ : LExpr T.mono}
    (hstep : Step F env e₁ e₂)
    (hEnvTy : Env.Typed env)
    (hAnnot : fvars_annotated_by hEnvTy.tyMap e₁)
    (hEnvAnnot : ∀ (x : T.Identifier) (e : LExpr T.mono), env x = some e →
        fvars_annotated_by hEnvTy.tyMap e)
    (hFBodyAnnot : Factory.BodyAnnotated F hEnvTy.tyMap)
    (hFEvalAnnot : Factory.EvalAnnotated F hEnvTy.tyMap)
    : fvars_annotated_by hEnvTy.tyMap e₂ := by
  induction hstep with
  | expand_fvar x e henv => exact hEnvAnnot x e henv
  | beta e1 v2 eres heq =>
    subst heq
    simp only [LExpr.subst]
    exact fvars_annotated_by_substK hAnnot.1 (fun _ => hAnnot.2)
  | reduce_1 e1 e1' e2 hstep ih => exact ⟨ih hAnnot.1, hAnnot.2⟩
  | reduce_2 e1 e2 e2' hstep ih => exact ⟨hAnnot.1, ih hAnnot.2⟩
  | ite_reduce_then ethen eelse => exact hAnnot.2.1
  | ite_reduce_else ethen eelse => exact hAnnot.2.2
  | ite_reduce_cond econd econd' ethen eelse hstep ih =>
    exact ⟨ih hAnnot.1, hAnnot.2.1, hAnnot.2.2⟩
  | ite_reduce_then_branch econd ethen ethen' eelse hstep ih =>
    exact ⟨hAnnot.1, ih hAnnot.2.1, hAnnot.2.2⟩
  | ite_reduce_else_branch econd ethen eelse eelse' hstep ih =>
    exact ⟨hAnnot.1, hAnnot.2.1, ih hAnnot.2.2⟩
  | eq_reduce_true e1 e2 heql => trivial
  | eq_reduce_false e1 e2 heql => trivial
  | eq_reduce_lhs e1 e1' e2 hstep ih => exact ⟨ih hAnnot.1, hAnnot.2⟩
  | eq_reduce_rhs e1 e2 e2' hstep ih => exact ⟨hAnnot.1, ih hAnnot.2⟩
  | expand_fn e callee fnbody new_body args fn tySubst hcall hbody htysubst heq =>
    subst heq
    obtain ⟨_, name, _, _, h_get⟩ := Factory.callOfLFunc_getElem? hcall
    have h_fn_mem : name.name ∈ F := Factory.getElem?_some_implies_mem h_get
    have h_fn_eq : F[name.name] = fn := Factory.getElem?_some_getElem h_get
    have h_body_eq : (F[name.name]).body = some fnbody := by rw [h_fn_eq]; exact hbody
    have h_body_annot : fvars_annotated_by hEnvTy.tyMap (fnbody.applySubst tySubst) :=
      hFBodyAnnot name.name h_fn_mem fnbody tySubst h_body_eq
    have h_args_annot : ∀ a ∈ args, fvars_annotated_by hEnvTy.tyMap a :=
      fvars_annotated_by_callOfLFunc_args hAnnot hcall
    have h_sm_annot : ∀ k v, Map.find? (fn.inputs.keys.zip args) k = some v →
        fvars_annotated_by hEnvTy.tyMap v := by
      intro k v hfind
      have h_mem := Map.find?_mem _ _ _ hfind
      exact h_args_annot v (List.of_mem_zip h_mem).2
    exact fvars_annotated_by_substFvarsLifting h_body_annot h_sm_annot
  | eval_fn e callee e' args fn denotefn hcall heval hresult =>
    obtain ⟨_, name, _, _, h_get⟩ := Factory.callOfLFunc_getElem? hcall
    have h_fn_mem : name.name ∈ F := Factory.getElem?_some_implies_mem h_get
    have h_fn_eq : F[name.name] = fn := Factory.getElem?_some_getElem h_get
    have h_eval_eq : (F[name.name]).concreteEval = some denotefn := by rw [h_fn_eq]; exact heval
    exact hFEvalAnnot name.name h_fn_mem denotefn _ args e' h_eval_eq hresult
  | abs_subst_fvars body x hfv =>
    exact substFvarsFromEnv_fvars_annotated hAnnot hEnvAnnot
  | quant_subst_fvars_body tr body x hfv =>
    exact ⟨hAnnot.1, substFvarsFromEnv_fvars_annotated hAnnot.2 hEnvAnnot⟩
  | quant_subst_fvars_trigger tr body x hfv =>
    exact ⟨substFvarsFromEnv_fvars_annotated hAnnot.1 hEnvAnnot, hAnnot.2⟩

/-- Multi-step version: `HasTypeA` is preserved by `StepStar`.

Assumptions:
- `hEnvWF`: environment well-formedness (local closure, typing, annotations, ops).
- `hFWF`: factory well-formedness for step preservation (body typing, eval typing, etc.).
- `hOps`: every op referenced in `e₁` has a corresponding factory entry.
- `hAnnot`: free variable annotations in `e₁` match the environment type map. -/
theorem StepStar.type_preserved
    {F : @Factory T} {env : Env T}
    {e₁ e₂ : LExpr T.mono} {τ : LMonoTy}
    (hsteps : StepStar F env e₁ e₂)
    (h₁ : LExpr.HasTypeA [] e₁ τ)
    (hEnvWF : Env.StepWF F env)
    (hFWF : Factory.StepWF F hEnvWF.typed.tyMap)
    (hOps : OpsConsistent F e₁)
    (hAnnot : fvars_annotated_by hEnvWF.typed.tyMap e₁)
    : LExpr.HasTypeA [] e₂ τ := by
  induction hsteps with
  | refl => exact h₁
  | step x y z hstep hrest ih =>
    have h_mid := Step.type_preserved hstep h₁ hFWF.wt hFWF.evalWt hOps hEnvWF.lc hEnvWF.typed hAnnot
    have h_ops_mid := Step.OpsConsistent_preserved hstep hOps hEnvWF.ops hFWF.bodyOps hFWF.evalOps
    have h_annot_mid := Step.fvars_annotated_preserved hstep hEnvWF.typed hAnnot hEnvWF.annot hFWF.bodyAnnot hFWF.evalAnnot
    exact ih h_mid h_ops_mid h_annot_mid

/-- Multi-step version: if `e₁` reduces to `e₂` in zero or more steps, and
both are well-typed at `τ`, they have the same denotation.

Assumptions:
- `hEnvWF`: environment well-formedness (local closure, typing, annotations, ops).
- `hFWF`: factory well-formedness for step preservation (body typing, eval typing, etc.).
- `hFacWF`: factory and type-factory well-formedness.
- `hIC`: interpretation consistency (factory bodies and environment values denote correctly).
- `hOps`: every op referenced in `e₁` has a corresponding factory entry.
- `hAnnot`: free variable annotations in `e₁` match the environment type map. -/
theorem StepStar.denote_preserved
    {F : @Factory T} {env : Env T} {tf : @TypeFactory T.IDMeta}
    {e₁ e₂ : LExpr T.mono} {τ : LMonoTy}
    (hsteps : StepStar F env e₁ e₂)
    (h₁ : LExpr.HasTypeA [] e₁ τ)
    (h₂ : LExpr.HasTypeA [] e₂ τ)
    (hEnvWF : Env.StepWF F env)
    (hFWF : Factory.StepWF F hEnvWF.typed.tyMap)
    (hFacWF : Factory.WF F tf)
    (hIC : InterpConsistent tcInterp opInterp fvarVal F env)
    (hOps : OpsConsistent F e₁)
    (hAnnot : fvars_annotated_by hEnvWF.typed.tyMap e₁)
    : LExpr.denote tcInterp opInterp fvarVal vt .nil e₁ τ h₁ =
      LExpr.denote tcInterp opInterp fvarVal vt .nil e₂ τ h₂ := by
  induction hsteps with
  | refl => rfl
  | step x y z hstep hrest ih =>
    have h_mid := Step.type_preserved hstep h₁ hFWF.wt hFWF.evalWt hOps hEnvWF.lc hEnvWF.typed hAnnot
    have h_ops_mid := Step.OpsConsistent_preserved hstep hOps hEnvWF.ops hFWF.bodyOps hFWF.evalOps
    have h_annot_mid := Step.fvars_annotated_preserved hstep hEnvWF.typed hAnnot hEnvWF.annot hFWF.bodyAnnot hFWF.evalAnnot
    have h_step_eq := Step.denote_preserved (tcInterp := tcInterp) (opInterp := opInterp) (fvarVal := fvarVal) (vt := vt) (tf := tf) hstep h₁ h_mid hIC.factory hFWF.wt hIC.env hOps hFacWF.factoryWF hFacWF.constrWF hIC.constr hFacWF.tfWF hEnvWF.lc hEnvWF.typed hAnnot
    have h_rest_eq := ih h_mid h₂ h_ops_mid h_annot_mid
    exact h_step_eq.trans h_rest_eq

/-- Corollary of `StepStar.denote_preserved` that requires no assumptions
on`e₂`. It derives the typing proof for `e₂` via `StepStar.type_preserved`. -/
theorem StepStar.denote_preserved'
    {F : @Factory T} {env : Env T} {tf : @TypeFactory T.IDMeta}
    {e₁ e₂ : LExpr T.mono} {τ : LMonoTy}
    (hsteps : StepStar F env e₁ e₂)
    (h₁ : LExpr.HasTypeA [] e₁ τ)
    (hEnvWF : Env.StepWF F env)
    (hFWF : Factory.StepWF F hEnvWF.typed.tyMap)
    (hFacWF : Factory.WF F tf)
    (hIC : InterpConsistent tcInterp opInterp fvarVal F env)
    (hOps : OpsConsistent F e₁)
    (hAnnot : fvars_annotated_by hEnvWF.typed.tyMap e₁)
    : LExpr.denote tcInterp opInterp fvarVal vt .nil e₁ τ h₁ =
      LExpr.denote tcInterp opInterp fvarVal vt .nil e₂ τ
        (StepStar.type_preserved hsteps h₁ hEnvWF hFWF hOps hAnnot) :=
  StepStar.denote_preserved tcInterp opInterp fvarVal vt hsteps h₁
    (StepStar.type_preserved hsteps h₁ hEnvWF hFWF hOps hAnnot)
    hEnvWF hFWF hFacWF hIC hOps hAnnot

end

section
variable [DecidableEq T.IDMeta]

/-- Soundness of the evaluator w.r.t. denotational semantics: if `e₂ = eval n σ e`
and both `e` and `e₂` are well-typed at `τ`, then `denote e = denote e₂`.
This is a simple composition of `eval_StepStar` and `StepStar.denote_preserved`.
-/
theorem eval_denote_sound
    [DecidableEq T.Metadata] [Inhabited T.IDMeta]
    [Std.ToFormat T.Metadata] [Std.ToFormat T.IDMeta]
    [Traceable LExpr.EvalProvenance T.Metadata]
    {F : @Factory T} {env : Env T} {e e₂ : LExpr T.mono} {τ : LMonoTy} {n : Nat}
    {tf : @TypeFactory T.IDMeta}
    (hEval : e₂ = (LExpr.eval n F env e).fst)
    (h₁ : LExpr.HasTypeA [] e τ)
    (h₂ : LExpr.HasTypeA [] e₂ τ)
    (hEnvWF : Env.StepWF F env)
    (hFWF : Factory.StepWF F hEnvWF.typed.tyMap)
    (hFacWF : Factory.WF F tf)
    (hIC : InterpConsistent tcInterp opInterp fvarVal F env)
    (hOps : OpsConsistent F e)
    (hAnnot : fvars_annotated_by hEnvWF.typed.tyMap e)
    : LExpr.denote tcInterp opInterp fvarVal vt .nil e τ h₁ =
      LExpr.denote tcInterp opInterp fvarVal vt .nil e₂ τ h₂ := by
  obtain ⟨e', hsteps, h_erase⟩ := eval_StepStar F env e e₂ n hFacWF.factoryWF hEval
  have h_ty_e' := StepStar.type_preserved hsteps h₁ hEnvWF hFWF hOps hAnnot
  have h_step_eq := StepStar.denote_preserved tcInterp opInterp fvarVal vt hsteps h₁ h_ty_e' hEnvWF hFWF hFacWF hIC hOps hAnnot
  have h_denote_e' := denote_replaceMetadata tcInterp opInterp fvarVal vt .nil (fun _ => ()) h_ty_e'
  have h_denote_e₂ := denote_replaceMetadata tcInterp opInterp fvarVal vt .nil (fun _ => ()) h₂
  rw [h_step_eq, h_denote_e']
  rw [h_denote_e₂]
  congr 1

end

end Lambda
