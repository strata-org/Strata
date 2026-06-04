/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

import Strata.Languages.Core.CmdTypeSpec
import Strata.Languages.Core.CmdType
import Strata.DL.Imperative.CmdType

/-! ## Soundness of Command Typechecker

Proves that if the executable command typechecker succeeds, then the declarative
`CmdHasType` relation holds.
-/

namespace Core
namespace TypeSpec

open Lambda LExpr Imperative

/-! ### Helper lemmas -/

/-- Substitution applied to context preserves `find? x = none`. -/
private theorem subst_find_none (Γ : TContext Unit) (S : Subst) (x : CoreIdent) :
    Γ.types.find? x = none →
    (TContext.subst Γ S).types.find? x = none :=
  Lambda.TContext.subst_find_none Γ S x

/-- Substitution applied to context transforms `find? x = some ty`
to `find? x = some (LTy.subst S ty)`. -/
private theorem subst_find_some (Γ : TContext Unit) (S : Subst) (x : CoreIdent) (ty : LTy) :
    Γ.types.find? x = some ty →
    (TContext.subst Γ S).types.find? x = some (LTy.subst S ty) :=
  Lambda.TContext.subst_find_some Γ S x ty

/--
When all context types have empty `boundVars`, `polyKeysFresh` holds vacuously
for any substitution (the condition `boundVars ty ≠ []` is never triggered).
-/
private theorem Subst.polyKeysFresh_of_mono (S : Subst) (Γ : TContext Unit)
    (h_mono : ContextMono Γ) :
    Subst.polyKeysFresh (T := CoreLParams) S Γ := by
  intro a _ x ty h_find h_bv
  exact absurd (h_mono x ty h_find) h_bv

/--
For `init x := expr`: after preprocess, inferType, and unifyTypes, the expression
has the final monotype under the unified substitution applied to the original context.
-/
private theorem init_det_expr_HasType (C : LContext CoreLParams) (Env Env_pre Env_infer Env' : TEnv Unit)
    (x : CoreIdent) (expr e' : LExpr CoreLParams.mono)
    (xty pre_ty ety : LTy) (mty_pre : LMonoTy) (md : MetaData Expression)
    (h_pre : CmdType.preprocess C Env xty = .ok (pre_ty, Env_pre))
    (h_pre_mono : pre_ty = .forAll [] mty_pre)
    (h_infer : CmdType.inferType C Env_pre (.init x xty (.det expr) md) expr = .ok (e', ety, Env_infer))
    (h_unify : CmdType.unifyTypes Env_infer [(pre_ty, ety)] = .ok Env')
    (h_wf : TEnvWF (T := CoreLParams) Env)
    (h_fwf : FactoryWF C.functions)
    (h_mono : ContextMono Env.context) :
    HasType (T := CoreLParams) C (TContext.subst Env.context Env'.stateSubstInfo.subst) expr
      (.forAll [] (LMonoTy.subst Env'.stateSubstInfo.subst mty_pre)) := by
  have h_wf_pre : TEnvWF (T := CoreLParams) Env_pre :=
    CmdType.preprocess_preserves_TEnvWF C Env xty pre_ty Env_pre h_pre h_wf
  have h_ctx_pre : Env_pre.context = Env.context :=
    CmdType.preprocess_preserves_context C Env xty pre_ty Env_pre h_pre
  obtain ⟨mty_infer, h_ety_eq, h_hastype⟩ :=
    CmdType.inferType_HasType C Env_pre Env_infer (.init x xty (.det expr) md) expr e' ety h_infer h_wf_pre h_fwf
  have h_abs : Subst.absorbs Env'.stateSubstInfo.subst Env_infer.stateSubstInfo.subst :=
    CmdType.unifyTypes_absorbs Env_infer Env' [(pre_ty, ety)] h_unify
  have h_mono_pre : ContextMono Env_pre.context := h_ctx_pre ▸ h_mono
  have h_pkf : Subst.polyKeysFresh (T := CoreLParams) Env'.stateSubstInfo.subst Env_pre.context :=
    Subst.polyKeysFresh_of_mono _ _ h_mono_pre
  have h_ht := h_hastype Env'.stateSubstInfo.subst h_abs Env'.stateSubstInfo.isWF h_pkf
  rw [h_ctx_pre] at h_ht
  have h_unify_eq : LMonoTy.subst Env'.stateSubstInfo.subst mty_infer =
      LMonoTy.subst Env'.stateSubstInfo.subst mty_pre := by
    rw [h_pre_mono, h_ety_eq] at h_unify
    exact (CmdType.unifyTypes_eq Env_infer Env' mty_pre mty_infer h_unify).symm
  rw [h_unify_eq] at h_ht
  exact h_ht

/-- For `set x := expr`: the expression has the variable's type under the unified substitution. -/
private theorem set_det_HasType (C : LContext CoreLParams) (Env Env_infer Env' : TEnv Unit)
    (x : CoreIdent) (expr e' : LExpr CoreLParams.mono) (xty ety : LTy)
    (mty_x : LMonoTy) (h_xty_eq : xty = .forAll [] mty_x)
    (h_infer : CmdType.inferType C Env (.set x (.det expr) md) expr = .ok (e', ety, Env_infer))
    (h_unify : CmdType.unifyTypes Env_infer [(xty, ety)] = .ok Env')
    (h_wf : TEnvWF (T := CoreLParams) Env)
    (h_fwf : FactoryWF C.functions)
    (h_mono : ContextMono Env.context) :
    HasType (T := CoreLParams) C (TContext.subst Env.context Env'.stateSubstInfo.subst) expr
      (LTy.subst Env'.stateSubstInfo.subst xty) := by
  subst h_xty_eq
  obtain ⟨mty_infer, h_ety_eq, h_hastype⟩ :=
    CmdType.inferType_HasType C Env Env_infer (.set x (.det expr) md) expr e' ety h_infer h_wf h_fwf
  have h_abs : Subst.absorbs Env'.stateSubstInfo.subst Env_infer.stateSubstInfo.subst :=
    CmdType.unifyTypes_absorbs Env_infer Env' [(.forAll [] mty_x, ety)] h_unify
  have h_pkf : Subst.polyKeysFresh (T := CoreLParams) Env'.stateSubstInfo.subst Env.context :=
    Subst.polyKeysFresh_of_mono _ _ h_mono
  have h_ht := h_hastype Env'.stateSubstInfo.subst h_abs Env'.stateSubstInfo.isWF h_pkf
  rw [LTy.subst_forAll_nil]
  have h_unify_eq : LMonoTy.subst Env'.stateSubstInfo.subst mty_infer =
      LMonoTy.subst Env'.stateSubstInfo.subst mty_x := by
    rw [h_ety_eq] at h_unify
    exact (CmdType.unifyTypes_eq Env_infer Env' mty_x mty_infer h_unify).symm
  rw [h_unify_eq] at h_ht
  exact h_ht

/--
Common proof for assert/assume/cover: if `inferType` succeeds and the result
is bool-typed, then `HasType` holds for the expression at type bool, and
the context is preserved.
-/
private theorem inferType_bool_HasType (C : LContext CoreLParams) (Env Env_out : TEnv Unit)
    (c : Cmd Expression) (e e' : LExpr CoreLParams.mono) (ety : LTy)
    (h_infer : CmdType.inferType C Env c e = .ok (e', ety, Env_out))
    (h_isbool : CmdType.isBoolType ety = true)
    (h_wf : TEnvWF (T := CoreLParams) Env)
    (h_fwf : FactoryWF C.functions)
    (h_ne : Env.context.types ≠ [])
    (h_mono : ContextMono Env.context) :
    HasType (T := CoreLParams) C (TContext.subst Env.context Env_out.stateSubstInfo.subst) e
      (.forAll [] .bool) ∧
    Env_out.context = Env.context := by
  obtain ⟨mty, h_ety_eq, h_hastype⟩ := CmdType.inferType_HasType C Env Env_out c e e' ety h_infer h_wf h_fwf
  have h_bool_ty := CmdType.isBoolType_eq ety h_isbool
  rw [h_ety_eq] at h_bool_ty
  have h_mty_bool : mty = .bool := by cases h_bool_ty; rfl
  subst h_mty_bool
  have h_ctx := CmdType.inferType_preserves_context C Env Env_out c e e' ety h_infer h_wf h_ne h_fwf
  have h_ht := h_hastype Env_out.stateSubstInfo.subst
    (Subst.absorbs_refl _ Env_out.stateSubstInfo.isWF)
    Env_out.stateSubstInfo.isWF
    (Subst.polyKeysFresh_of_mono _ _ h_mono)
  rw [LMonoTy.subst_bool] at h_ht
  exact ⟨h_ht, h_ctx⟩

/--
Context scaffolding for the `init x := det` case: establishes that the final
context equals the original and computes the monotype inserted by `update`.
-/
theorem init_det_context_setup (C : LContext CoreLParams) (Env : TEnv Unit)
    (x : CoreIdent) (xty : LTy) (heq_det : LExpr CoreLParams.mono) (md : MetaData Expression)
    (v1 : LTy × TEnv Unit) (v2 : LExpr CoreLParams.mono × LTy × TEnv Unit)
    (Env_unified : TEnv Unit) (v3 : LTy × TEnv Unit)
    (h_preprocess : CmdType.preprocess C Env xty = .ok v1)
    (h_infer : CmdType.inferType C v1.snd (Cmd.init x xty (.det heq_det) md) heq_det = .ok v2)
    (h_unify : CmdType.unifyTypes v2.2.snd [(v1.fst, v2.2.fst)] = .ok Env_unified)
    (h_postprocess : CmdType.postprocess C Env_unified v1.fst = .ok v3)
    (h_wf : TEnvWF (T := CoreLParams) Env)
    (h_fwf : FactoryWF C.functions)
    (h_ne : Env.context.types ≠ []) :
    let S := (CmdType.update v3.snd x v3.fst).stateSubstInfo.subst
    v3.snd.context = Env.context ∧
    TEnvWF (T := CoreLParams) v1.snd ∧
    (∃ mty_pre, v1.fst = .forAll [] mty_pre ∧
      (∃ mty, LTy.subst S v3.fst = .forAll [] mty ∧
        mty = LMonoTy.subst Env_unified.stateSubstInfo.subst mty_pre ∧
        v3.snd = Env_unified)) := by
  have h_pre_mono := CmdType.preprocess_mono C Env xty v1.fst v1.snd h_preprocess
  obtain ⟨mty_pre, h_mty_pre⟩ := h_pre_mono
  have h_post_res := CmdType.postprocess_result C Env_unified v3.snd mty_pre v3.fst
    (h_mty_pre ▸ h_postprocess)
  have h_wf_pre : TEnvWF (T := CoreLParams) v1.snd :=
    CmdType.preprocess_preserves_TEnvWF C Env xty v1.fst v1.snd h_preprocess h_wf
  have h_ne_pre : v1.snd.context.types ≠ [] := by
    rw [CmdType.preprocess_preserves_context C Env xty v1.fst v1.snd h_preprocess]
    exact h_ne
  have h_ctx_eq : v3.snd.context = Env.context := by
    have h1 := h_post_res.2
    rw [h1]
    have h2 := CmdType.unifyTypes_preserves_context v2.2.snd Env_unified
      [(v1.fst, v2.2.fst)] h_unify
    rw [h2]
    have h3 := CmdType.inferType_preserves_context C v1.snd v2.2.snd
      (.init x xty (.det heq_det) md) heq_det v2.1 v2.2.fst h_infer
      h_wf_pre h_ne_pre h_fwf
    rw [h3]
    exact CmdType.preprocess_preserves_context C Env xty v1.fst v1.snd h_preprocess
  have h_v3_mono : ∃ mty, LTy.subst
      (CmdType.update v3.snd x v3.fst).stateSubstInfo.subst v3.fst = .forAll [] mty := by
    rw [CmdType.update_preserves_subst, h_post_res.1, LTy.subst_forAll_nil]
    exact ⟨_, rfl⟩
  obtain ⟨mty, h_mty⟩ := h_v3_mono
  have h_mty_eq : mty = LMonoTy.subst Env_unified.stateSubstInfo.subst mty_pre := by
    rw [CmdType.update_preserves_subst, h_post_res.2, h_post_res.1,
      LTy.subst_forAll_nil] at h_mty
    have h_idem := LMonoTy.subst_idempotent
      Env_unified.stateSubstInfo.subst Env_unified.stateSubstInfo.isWF mty_pre
    rw [h_idem] at h_mty
    cases h_mty; rfl
  exact ⟨h_ctx_eq, h_wf_pre, mty_pre, h_mty_pre, mty, h_mty, h_mty_eq, h_post_res.2⟩

/--
Context scaffolding for `init x := *` (nondet): the context is preserved and
the inserted type is mono.
-/
theorem init_nondet_context_setup (C : LContext CoreLParams) (Env : TEnv Unit)
    (x : CoreIdent) (xty : LTy)
    (v1 : LTy × TEnv Unit) (v2 : LTy × TEnv Unit)
    (h_preprocess : CmdType.preprocess C Env xty = .ok v1)
    (h_postprocess : CmdType.postprocess C v1.snd v1.fst = .ok v2)
    (h_find_none : Env.context.types.find? x = none) :
    let S := (CmdType.update v2.snd x v2.fst).stateSubstInfo.subst
    v2.snd.context = Env.context ∧
    (TContext.subst Env.context S).types.find? x = none ∧
    (∃ mty, LTy.subst S v2.fst = .forAll [] mty) := by
  have h_pre_mono := CmdType.preprocess_mono C Env xty v1.fst v1.snd h_preprocess
  obtain ⟨mty_pre, h_mty_pre⟩ := h_pre_mono
  have h_post_res := CmdType.postprocess_result C v1.snd v2.snd mty_pre v2.fst
    (h_mty_pre ▸ h_postprocess)
  have h_ctx_eq : v2.snd.context = Env.context := by
    rw [h_post_res.2]
    exact CmdType.preprocess_preserves_context C Env xty v1.fst v1.snd h_preprocess
  have h_find_none_subst := Lambda.TContext.subst_find_none Env.context
    (CmdType.update v2.snd x v2.fst).stateSubstInfo.subst x h_find_none
  have h_v2_mono : ∃ mty, LTy.subst (CmdType.update v2.snd x v2.fst).stateSubstInfo.subst
      v2.fst = .forAll [] mty := by
    rw [CmdType.update_preserves_subst, h_post_res.1, LTy.subst_forAll_nil]
    exact ⟨_, rfl⟩
  exact ⟨h_ctx_eq, h_find_none_subst, h_v2_mono⟩

/--
For `set x := *` (nondet): if `x` is in the context with a mono type, then
after substitution it remains mono.
-/
theorem set_nondet_sound (Env : TEnv Unit) (x : CoreIdent) (xty : LTy)
    (h_lookup : CmdType.lookup Env x = some xty)
    (h_mono : ContextMono Env.context) :
    ∃ mty, (TContext.subst Env.context Env.stateSubstInfo.subst).types.find? x =
      some (.forAll [] mty) := by
  have h_find := (CmdType.lookup_some_iff_find_some Env x xty).mp h_lookup
  have h_xty_bv := h_mono x xty h_find
  obtain ⟨xs, mty_x⟩ := xty
  simp [LTy.boundVars] at h_xty_bv
  subst h_xty_bv
  have h_find_subst := Lambda.TContext.subst_find_some Env.context Env.stateSubstInfo.subst x
    (.forAll [] mty_x) h_find
  rw [LTy.subst_forAll_nil] at h_find_subst
  exact ⟨_, h_find_subst⟩

/-! ### Main Soundness Theorem -/

/--
Soundness of the command typechecker: if `Cmd.typeCheck` succeeds, then the
declarative `CmdHasType` relation holds between the substituted input/output contexts.

The theorem uses the **final** substitution from `Env'` applied to both the input
and output contexts, since unification during the command may refine type variables.
-/
-- h_mono: In Core, all context types are `forAll [] mty` (boundVars = []) because
-- preprocess instantiates poly annotations into fresh unification vars, and
-- update/postprocess always stores `forAll [] _`. Makes polyKeysFresh vacuous.
theorem Cmd.typeCheck_sound (C : LContext CoreLParams) (Env : TEnv Unit)
    (cmd cmd' : Cmd Expression) (Env' : TEnv Unit)
    (h : Imperative.Cmd.typeCheck C Env cmd = .ok (cmd', Env'))
    (h_wf : TEnvWF (T := CoreLParams) Env)
    (h_fwf : FactoryWF C.functions)
    (h_ne : Env.context.types ≠ [])
    (h_mono : ContextMono Env.context) :
    CmdHasType C (TContext.subst Env.context Env'.stateSubstInfo.subst) cmd
      (TContext.subst Env'.context Env'.stateSubstInfo.subst) := by
  cases cmd with
  | init x xty e md =>
    simp only [Cmd.typeCheck, Bind.bind, Except.bind] at h
    split at h
    · -- lookup returned none → x is fresh
      rename_i h_lookup_none
      split at h
      · -- det case
        rename_i expr heq_det
        split at h
        · contradiction
        · rename_i h_not_in_fv
          split at h
          · contradiction
          · rename_i v1 h_preprocess
            split at h
            · contradiction
            · rename_i v2 h_infer
              split at h
              · contradiction
              · rename_i Env_unified h_unify
                split at h
                · contradiction
                · rename_i v3 h_postprocess
                  cases h
                  simp only [TypeContext.update, TypeContext.lookup, TypeContext.preprocess,
                    TypeContext.postprocess, TypeContext.inferType, TypeContext.unifyTypes,
                    TypeContext.freeVars] at *
                  have h_find_none := (CmdType.lookup_none_iff_find_none Env x).mp h_lookup_none
                  obtain ⟨h_ctx_eq, h_wf_pre, mty_pre, h_mty_pre, mty, h_mty, h_mty_eq, h_v3_eq⟩ :=
                    init_det_context_setup C Env x xty heq_det md v1 v2 Env_unified v3
                      h_preprocess h_infer h_unify h_postprocess h_wf h_fwf h_ne
                  have h_find_none_subst := subst_find_none Env.context
                    (CmdType.update v3.snd x v3.fst).stateSubstInfo.subst x h_find_none
                  have h_fresh_v3 : v3.snd.context.types.find? x = none :=
                    h_ctx_eq ▸ h_find_none
                  have h_update_ctx := CmdType.update_subst_context v3.snd x v3.fst
                    (CmdType.update v3.snd x v3.fst).stateSubstInfo.subst h_fresh_v3
                  rw [h_update_ctx, h_ctx_eq, h_mty]
                  have h_not_in_vars : x ∉ HasVarsPure.getVars (P := Expression) heq_det :=
                    fun h => h_not_in_fv ((CmdType.freeVars_eq_getVars heq_det x).mpr h)
                  have h_hastype : HasType (T := CoreLParams) C
                      (Env.context.subst (CmdType.update v3.snd x v3.fst).stateSubstInfo.subst)
                      heq_det (.forAll [] (LMonoTy.subst Env_unified.stateSubstInfo.subst mty_pre)) := by
                    rw [CmdType.update_preserves_subst, h_v3_eq]
                    exact init_det_expr_HasType C Env v1.snd v2.2.snd Env_unified x heq_det
                      v2.1 xty v1.fst v2.2.fst mty_pre md h_preprocess h_mty_pre
                      h_infer h_unify h_wf h_fwf h_mono
                  rw [h_mty_eq]
                  exact CmdHasType'.init_det _ x xty heq_det _ md
                    h_find_none_subst h_not_in_vars h_hastype
      · -- nondet case
        rename_i heq_nondet
        split at h
        · contradiction
        · rename_i v1 h_preprocess
          split at h
          · contradiction
          · rename_i v2 h_postprocess
            cases h
            simp only [TypeContext.update, TypeContext.lookup, TypeContext.preprocess,
              TypeContext.postprocess] at *
            have h_find_none := (CmdType.lookup_none_iff_find_none Env x).mp h_lookup_none
            obtain ⟨h_ctx_eq, h_find_none_subst, mty, h_mty⟩ :=
              init_nondet_context_setup C Env x xty v1 v2 h_preprocess h_postprocess h_find_none
            have h_fresh_v2 : v2.snd.context.types.find? x = none :=
              h_ctx_eq ▸ h_find_none
            have h_update_ctx := CmdType.update_subst_context v2.snd x v2.fst
              (CmdType.update v2.snd x v2.fst).stateSubstInfo.subst h_fresh_v2
            rw [h_update_ctx, h_ctx_eq, h_mty]
            exact CmdHasType'.init_nondet _ x xty mty md h_find_none_subst
    · -- lookup returned some → variable already declared → contradiction
      contradiction
  | set x e md =>
    simp only [Cmd.typeCheck, Bind.bind, Except.bind] at h
    split at h
    · contradiction
    · rename_i xty h_lookup
      cases e with
      | det expr =>
        simp only [] at h
        split at h
        · contradiction
        · rename_i v heq
          split at h
          · contradiction
          · rename_i Env_unified h_unify
            cases h
            obtain ⟨e', ety, Env_infer⟩ := v
            simp only at heq h_unify ⊢
            have h_find := (CmdType.lookup_some_iff_find_some Env x xty).mp h_lookup
            have h_find_subst := subst_find_some Env.context
              Env'.stateSubstInfo.subst x xty h_find
            have h_xty_bv := h_mono x xty h_find
            obtain ⟨xs, mty_x⟩ := xty
            simp [LTy.boundVars] at h_xty_bv
            subst h_xty_bv
            have h_hastype := set_det_HasType C Env Env_infer Env' x expr e'
              (.forAll [] mty_x) ety mty_x rfl heq h_unify h_wf h_fwf h_mono
            have h_ctx_infer := CmdType.inferType_preserves_context C Env Env_infer
              (.set x (.det expr) md) expr e' ety heq h_wf h_ne h_fwf
            have h_ctx_unify := CmdType.unifyTypes_preserves_context Env_infer Env'
              [(.forAll [] mty_x, ety)] h_unify
            have h_ctx : Env'.context = Env.context := by rw [h_ctx_unify, h_ctx_infer]
            rw [h_ctx]
            rw [LTy.subst_forAll_nil] at h_find_subst h_hastype
            exact CmdHasType'.set_det _ x (LMonoTy.subst Env'.stateSubstInfo.subst mty_x) expr md
              h_find_subst h_hastype
      | nondet =>
        simp at h
        cases h
        obtain ⟨mty, h_find_subst⟩ := set_nondet_sound Env x xty h_lookup h_mono
        exact CmdHasType'.set_nondet _ x mty md h_find_subst
  | assert label e md =>
    simp only [Cmd.typeCheck, Bind.bind, Except.bind] at h
    split at h
    · contradiction
    · rename_i v heq
      split at h
      · rename_i h_bool
        cases h
        obtain ⟨e', ety, Env_out⟩ := v
        obtain ⟨h_ht, h_ctx⟩ := inferType_bool_HasType C Env Env_out
          (.assert label e md) e e' ety heq h_bool h_wf h_fwf h_ne h_mono
        rw [h_ctx]
        exact CmdHasType'.assert _ label e md h_ht
      · contradiction
  | assume label e md =>
    simp only [Cmd.typeCheck, Bind.bind, Except.bind] at h
    split at h
    · contradiction
    · rename_i v heq
      split at h
      · rename_i h_bool
        cases h
        obtain ⟨e', ety, Env_out⟩ := v
        obtain ⟨h_ht, h_ctx⟩ := inferType_bool_HasType C Env Env_out
          (.assume label e md) e e' ety heq h_bool h_wf h_fwf h_ne h_mono
        rw [h_ctx]
        exact CmdHasType'.assume _ label e md h_ht
      · contradiction
  | cover label e md =>
    simp only [Cmd.typeCheck, Bind.bind, Except.bind] at h
    split at h
    · contradiction
    · rename_i v heq
      split at h
      · rename_i h_bool
        cases h
        obtain ⟨e', ety, Env_out⟩ := v
        obtain ⟨h_ht, h_ctx⟩ := inferType_bool_HasType C Env Env_out
          (.cover label e md) e e' ety heq h_bool h_wf h_fwf h_ne h_mono
        rw [h_ctx]
        exact CmdHasType'.cover _ label e md h_ht
      · contradiction

end TypeSpec
end Core
