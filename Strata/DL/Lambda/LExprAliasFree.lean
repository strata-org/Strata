/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

import Strata.DL.Lambda.LExprTypeSpec
import all Strata.DL.Lambda.LExprTypeSpec

/-! ## Alias-free infrastructure

This module proves properties of `aliasFree` and `AliasesResolved`:

1. Alias-free types are fixpoints of `resolveAliases`.
2. The output of `resolveAliases` is alias-free when `AliasesResolved` holds.
3. `instantiateWithCheck` produces alias-free output.
4. `typeBoundVar` preserves the alias list and produces alias-free types.
-/

namespace Lambda

open LExpr

section

variable {T : LExprParams} [Std.ToFormat T.IDMeta]

/-- Splits on `h` once and closes the first (error) branch via `simp at h` or `contradiction`.
    Fails if neither closes the branch. -/
macro "elim_err" h:ident : tactic =>
  `(tactic| (split at $h:ident; · (solve | simp at $h:ident | contradiction)))

/-- Repeatedly splits on `h` and closes error branches until a split fails or
    the error branch can't be closed. -/
macro "elim_errs" h:ident : tactic =>
  `(tactic| repeat (split at $h:ident; · (solve | simp at $h:ident | contradiction)))

/-! ### Alias-free fixpoint lemmas -/

mutual
/-- Alias-free type lists are fixpoints of `resolveAliases`. -/
private theorem resolveAliasesList_aliasFree (mtys : LMonoTys) (Env : TEnv T.IDMeta)
    (h_af : LMonoTys.aliasFree Env.context.aliases mtys) :
    LMonoTys.resolveAliases mtys Env = .ok (mtys, Env) := by
  match mtys with
  | [] => simp [LMonoTys.resolveAliases, Pure.pure, Except.pure]
  | hd :: tl =>
    simp only [LMonoTys.resolveAliases, Bind.bind, Except.bind]
    have h_hd := resolveAliases_aliasFree hd Env h_af.1
    rw [h_hd]; dsimp
    have h_tl := resolveAliasesList_aliasFree tl Env h_af.2
    rw [h_tl]; simp [Pure.pure, Except.pure]
termination_by sizeOf mtys

/-- Alias-free types are fixpoints of `resolveAliases`: resolving a type that
    already contains no alias references returns it unchanged. -/
theorem resolveAliases_aliasFree (mty : LMonoTy) (Env : TEnv T.IDMeta)
    (h_af : LMonoTy.aliasFree Env.context.aliases mty) :
    LMonoTy.resolveAliases mty Env = .ok (mty, Env) := by
  match mty with
  | .ftvar _ => simp [LMonoTy.resolveAliases, Pure.pure, Except.pure]
  | .bitvec _ => simp [LMonoTy.resolveAliases, Pure.pure, Except.pure]
  | .tcons name args =>
    simp only [LMonoTy.resolveAliases, Bind.bind, Except.bind]
    have h_args := resolveAliasesList_aliasFree args Env h_af.2
    rw [h_args]; dsimp
    simp only [Pure.pure, Except.pure, LMonoTy.tconsAliasSimple]
    rw [h_af.1]
termination_by sizeOf mty
end


/-- `typeBoundVar` only adds to the type scope — it does not modify the alias list. -/
theorem typeBoundVar_aliases_eq [DecidableEq T.IDMeta] [HasGen T.IDMeta] (C : LContext T) (Env : TEnv T.IDMeta)
    (bty : Option LMonoTy) (xv : T.Identifier) (xty : LMonoTy) (Env' : TEnv T.IDMeta)
    (h : typeBoundVar C Env bty = .ok (xv, xty, Env')) :
    Env'.context.aliases = Env.context.aliases := by
  simp only [typeBoundVar, Bind.bind, Except.bind] at h
  elim_err h
  rename_i v_gen h_gen; obtain ⟨xv_raw, Env_g⟩ := v_gen
  dsimp at h; cases bty with
  | some bty_val =>
    dsimp at h; elim_err h
    rename_i v_ic h_ic; obtain ⟨bty_ic, Env_ic⟩ := v_ic
    cases h
    simp only [TEnv.addInNewestContext, TEnv.updateContext, TEnv.context]
    have h_ctx_g := liftGenEnv_context Env xv Env_g h_gen
    have h_ctx_ic := LMonoTy_instantiateWithCheck_context' bty_val C Env_g _ ⟨bty_ic, Env_ic⟩ h_ic
    have h_ctx : (⟨bty_ic, Env_ic⟩ : TEnv T.IDMeta).context = Env.context := by
      simp [TEnv.context] at h_ctx_ic h_ctx_g ⊢; rw [h_ctx_ic, h_ctx_g]
    exact congrArg TContext.aliases h_ctx
  | none =>
    dsimp at h; elim_err h
    rename_i v_tg h_tg; obtain ⟨tv, Env_tv⟩ := v_tg
    cases h
    simp only [TEnv.addInNewestContext, TEnv.updateContext, TEnv.context]
    have h_ctx_g := liftGenEnv_context Env xv Env_g h_gen
    have h_ctx_tg := TEnv.genTyVar_context Env_g tv Env_tv h_tg
    have h_ctx : Env_tv.context = Env.context := by
      simp [TEnv.context] at h_ctx_tg h_ctx_g ⊢; rw [h_ctx_tg, h_ctx_g]
    exact congrArg TContext.aliases h_ctx


/-- A member of an alias-free type list is itself alias-free. -/
private theorem aliasFree_of_mem (aliases : List TypeAlias) (vals : LMonoTys) (v : LMonoTy)
    (h_vals : LMonoTys.aliasFree aliases vals) (h_mem : v ∈ vals) :
    LMonoTy.aliasFree aliases v := by
  induction vals with
  | nil => simp at h_mem
  | cons hd tl ih =>
    simp [LMonoTys.aliasFree] at h_vals
    cases List.mem_cons.mp h_mem with
    | inl h_eq => subst h_eq; exact h_vals.1
    | inr h_tl => exact ih h_vals.2 h_tl

/-- `openVars` preserves list length. -/
private theorem openVars_length (vars : List TyIdentifier) (vals : LMonoTys)
    (mtys : LMonoTys) :
    (LMonoTys.openVars vars vals mtys).length = mtys.length := by
  induction mtys with
  | nil => simp [LMonoTys.openVars]
  | cons hd tl ih => simp [LMonoTys.openVars, ih]

mutual
/-- Substituting alias-free values into alias-free type lists preserves alias-freeness. -/
private theorem openVarsList_aliasFree (vars : List TyIdentifier) (vals : LMonoTys)
    (aliases : List TypeAlias) (mtys : LMonoTys)
    (h_body : LMonoTys.aliasFree aliases mtys)
    (h_vals : LMonoTys.aliasFree aliases vals) :
    LMonoTys.aliasFree aliases (LMonoTys.openVars vars vals mtys) := by
  match mtys with
  | [] => simp [LMonoTys.openVars, LMonoTys.aliasFree]
  | hd :: tl =>
    simp only [LMonoTys.openVars, LMonoTys.aliasFree]
    exact ⟨openVars_aliasFree vars vals aliases hd h_body.1 h_vals,
           openVarsList_aliasFree vars vals aliases tl h_body.2 h_vals⟩
termination_by sizeOf mtys

/-- Substituting alias-free values into an alias-free type preserves alias-freeness. -/
private theorem openVars_aliasFree (vars : List TyIdentifier) (vals : LMonoTys)
    (aliases : List TypeAlias) (mty : LMonoTy)
    (h_body : LMonoTy.aliasFree aliases mty)
    (h_vals : LMonoTys.aliasFree aliases vals) :
    LMonoTy.aliasFree aliases (LMonoTy.openVars vars vals mty) := by
  match mty with
  | .ftvar x =>
    simp only [LMonoTy.openVars]
    split
    · rename_i fst_val v h_find
      have h_mem := zip_find_mem_snd vars vals x (fst_val, v) h_find
      exact aliasFree_of_mem aliases vals v h_vals h_mem
    · simp [LMonoTy.aliasFree]
  | .bitvec _ => simp [LMonoTy.openVars, LMonoTy.aliasFree]
  | .tcons name args =>
    simp only [LMonoTy.openVars, LMonoTy.aliasFree]
    have h_len : (LMonoTys.openVars vars vals args).length = args.length :=
      openVars_length vars vals args
    rw [h_len]
    exact ⟨h_body.1, openVarsList_aliasFree vars vals aliases args h_body.2 h_vals⟩
termination_by sizeOf mty
end

/-- `tconsAliasSimple` produces an alias-free type when aliases are resolved and args are alias-free. -/
private theorem tconsAliasSimple_aliasFree (name : String) (args : LMonoTys)
    (aliases : List TypeAlias)
    (h_resolved : ∀ a, a ∈ aliases → LMonoTy.aliasFree aliases a.type)
    (h_args : LMonoTys.aliasFree aliases args) :
    LMonoTy.aliasFree aliases (LMonoTy.tconsAliasSimple name args aliases) := by
  simp only [LMonoTy.tconsAliasSimple]
  split
  · -- no matching alias: result is .tcons name args
    rename_i h_none
    simp only [LMonoTy.aliasFree]
    exact ⟨h_none, h_args⟩
  · -- matching alias found
    rename_i a h_find
    have h_mem : a ∈ aliases := List.mem_of_find?_eq_some h_find
    have h_body_af := h_resolved a h_mem
    exact openVars_aliasFree a.typeArgs args aliases a.type h_body_af h_args

mutual
/-- The output of `resolveAliases` is alias-free when all aliases in the context are resolved. -/
private theorem resolveAliases_output_aliasFree_aux
    (mty : LMonoTy) (Env : TEnv T.IDMeta)
    (result : LMonoTy) (Env' : TEnv T.IDMeta)
    (h : LMonoTy.resolveAliases mty Env = .ok (result, Env'))
    (h_resolved : TContext.AliasesResolved Env.context) :
    LMonoTy.aliasFree Env.context.aliases result := by
  match mty with
  | .ftvar _ =>
    simp [LMonoTy.resolveAliases, Pure.pure, Except.pure] at h
    obtain ⟨h_res, _⟩ := h
    subst h_res
    simp [LMonoTy.aliasFree]
  | .bitvec _ =>
    simp [LMonoTy.resolveAliases, Pure.pure, Except.pure] at h
    obtain ⟨h_res, _⟩ := h
    subst h_res
    simp [LMonoTy.aliasFree]
  | .tcons name args =>
    simp [LMonoTy.resolveAliases, Bind.bind, Except.bind] at h
    elim_err h
    rename_i args_result h_args
    obtain ⟨args', Env_mid⟩ := args_result
    dsimp at h h_args
    simp [Pure.pure, Except.pure] at h
    obtain ⟨h_res, h_env⟩ := h
    subst h_res h_env
    have h_ctx_mid := LMonoTys.resolveAliases_context args Env args' Env_mid h_args
    have h_resolved_mid : TContext.AliasesResolved Env_mid.context := by
      rw [h_ctx_mid]; exact h_resolved
    have h_args_af := resolveAliasesList_output_aliasFree args Env args' Env_mid h_args h_resolved
    rw [← h_ctx_mid]
    rw [← h_ctx_mid] at h_args_af
    exact tconsAliasSimple_aliasFree name args' Env_mid.context.aliases
      h_resolved_mid h_args_af
termination_by sizeOf mty

/-- The output of `resolveAliases` on a list is alias-free when aliases are resolved. -/
private theorem resolveAliasesList_output_aliasFree
    (mtys : LMonoTys) (Env : TEnv T.IDMeta)
    (results : LMonoTys) (Env' : TEnv T.IDMeta)
    (h : LMonoTys.resolveAliases mtys Env = .ok (results, Env'))
    (h_resolved : TContext.AliasesResolved Env.context) :
    LMonoTys.aliasFree Env.context.aliases results := by
  match mtys with
  | [] =>
    simp [LMonoTys.resolveAliases, Pure.pure, Except.pure] at h
    obtain ⟨h_res, _⟩ := h
    subst h_res
    simp [LMonoTys.aliasFree]
  | hd :: tl =>
    simp [LMonoTys.resolveAliases, Bind.bind, Except.bind] at h
    elim_err h
    rename_i hd_result h_hd
    obtain ⟨hd', Env_hd⟩ := hd_result
    dsimp at h h_hd
    elim_err h
    rename_i tl_result h_tl
    obtain ⟨tl', Env_tl⟩ := tl_result
    dsimp at h h_tl
    simp [Pure.pure, Except.pure] at h
    obtain ⟨h_res, h_env⟩ := h
    subst h_res h_env
    have h_ctx_hd := LMonoTy.resolveAliases_context hd Env hd' Env_hd h_hd
    have h_resolved_hd : TContext.AliasesResolved Env_hd.context := by
      rw [h_ctx_hd]; exact h_resolved
    constructor
    · exact resolveAliases_output_aliasFree_aux hd Env hd' Env_hd h_hd h_resolved
    · have h_tl_af := resolveAliasesList_output_aliasFree tl Env_hd tl' Env_tl h_tl h_resolved_hd
      rw [h_ctx_hd] at h_tl_af
      exact h_tl_af
termination_by sizeOf mtys
end

/-- The output of `resolveAliases` is always alias-free when the context aliases
    are themselves fully resolved. -/
theorem resolveAliases_output_aliasFree
  (mty : LMonoTy) (Env : TEnv T.IDMeta)
    (result : LMonoTy) (Env' : TEnv T.IDMeta)
    (h : LMonoTy.resolveAliases mty Env = .ok (result, Env'))
    (h_resolved : TContext.AliasesResolved Env.context) :
    LMonoTy.aliasFree Env.context.aliases result :=
  resolveAliases_output_aliasFree_aux mty Env result Env' h h_resolved


/-- `instantiateWithCheck` produces alias-free output, since it runs `resolveAliases`
    internally after instantiating bound type variables. -/
theorem instantiateWithCheck_aliasFree
  (mty : LMonoTy) (C : LContext T)
    (Env : TEnv T.IDMeta) (result : LMonoTy) (Env' : TEnv T.IDMeta)
    (h : LMonoTy.instantiateWithCheck mty C Env = .ok (result, Env'))
    (h_resolved : TContext.AliasesResolved Env.context) :
    LMonoTy.aliasFree Env.context.aliases result := by
  -- Decompose instantiateWithCheck using the existing theorem
  have ⟨mty_ie, Env_ie, Env_ra, h_ie, h_ra⟩ :=
    LMonoTy.instantiateWithCheck_decompose mty C Env result Env' h
  -- instantiateEnv preserves context
  have h_ie_ctx : Env_ie.context = Env.context :=
    LMonoTys.instantiateEnv_context _ _ _ _ _ h_ie
  -- Apply resolveAliases_output_aliasFree
  have h_resolved_ie : TContext.AliasesResolved Env_ie.context := by
    rw [h_ie_ctx]; exact h_resolved
  have h_af := resolveAliases_output_aliasFree mty_ie Env_ie result Env_ra h_ra h_resolved_ie
  rw [h_ie_ctx] at h_af
  exact h_af


/-- The type assigned to the bound variable by `typeBoundVar` is alias-free. -/
theorem typeBoundVar_xty_aliasFree [HasGen T.IDMeta] (C : LContext T) (Env : TEnv T.IDMeta)
    (bty : Option LMonoTy) (xv : T.Identifier) (xty : LMonoTy) (Env' : TEnv T.IDMeta)
    (h : typeBoundVar C Env bty = .ok (xv, xty, Env'))
    (h_resolved : TContext.AliasesResolved Env.context) :
    LMonoTy.aliasFree Env.context.aliases xty := by
  simp only [typeBoundVar, liftGenEnv, Bind.bind, Except.bind] at h
  elim_err h
  rename_i genResult h_gen
  -- Case split on bty
  split at h
  · -- bty = some bty_val: xty comes from instantiateWithCheck
    rename_i bty_val
    elim_err h
    rename_i result h_inst
    have heq := Except.ok.inj h
    simp [Prod.mk.injEq] at heq
    obtain ⟨_, h_xty, _⟩ := heq
    subst h_xty
    -- genResult.snd has same context as Env (liftGenEnv only changes genState)
    have h_gen_ctx : genResult.snd.context = Env.context := by
      elim_err h_gen
      rename_i a_id T'_env h_genVar
      have h_eq := Except.ok.inj h_gen; rw [← h_eq]
      simp only [TEnv.context]
      exact HasGen.genVar_context Env.genEnv a_id T'_env h_genVar
    have h_af := instantiateWithCheck_aliasFree bty_val C genResult.snd _ result h_inst
      (h_gen_ctx ▸ h_resolved)
    rw [h_gen_ctx] at h_af
    exact h_af
  · -- bty = none: xty = .ftvar xtyid, trivially alias-free
    rename_i h_none
    elim_err h
    rename_i genResult2 h_genTyVar
    have heq := Except.ok.inj h
    simp [Prod.mk.injEq] at heq
    obtain ⟨_, h_xty, _⟩ := heq
    subst h_xty
    simp [LMonoTy.aliasFree]

end

end Lambda
