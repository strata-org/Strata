/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

import Strata.Languages.Core.CmdTypeSpec
import Strata.Languages.Core.CmdTypeProps
import Strata.DL.Imperative.CmdType
import all Strata.DL.Imperative.CmdType
import all Strata.DL.Lambda.LExprResolveProps
import all Strata.DL.Lambda.Denote.LExprDenoteTySubst

/-! ## Soundness of Command Typechecker

This file relates the executable command typechecker `Imperative.Cmd.typeCheck`
to the two declarative typing relations. It contains two top-level proofs:

* **`Cmd.typeCheck_sound`** (Part I) — if `Cmd.typeCheck` succeeds, the
  declarative `CmdHasType` relation holds between the substituted input and
  output contexts. This is the *unannotated* soundness statement: it talks about
  the original command and the polymorphic `CmdHasType` relation, using the final
  substitution from `Env'` to ground the type variables refined during checking.

* **`Cmd.typeCheck_annotated_sound`** (Part II) — if `Cmd.typeCheck` succeeds,
  the *output* command (with the final substitution applied via `Cmd.applySubst`)
  satisfies the annotated, monomorphic `CmdHasTypeA` relation. This is the
  stronger statement consumed downstream, where expression types must be ground
  and match the types produced by `resolve`.

Both proofs proceed by the same case split over the command constructors
(`init`/`set`/`assert`/`assume`/`cover`), each backed by its own set of helper
lemmas grouped under the corresponding part below.
-/

namespace Core
namespace TypeSpec

open Lambda LExpr Imperative

/-- All context types are monomorphic (have empty bound variables).
In Core this always holds: `preprocess` instantiates poly annotations, and
`update`/`postprocess` stores only `forAll [] _`. -/
def ContextMono (Γ : TContext Unit) : Prop :=
  ∀ x ty, Γ.types.find? x = some ty → LTy.boundVars ty = []

/-! ### Helper lemmas -/

/--
When all context types have empty `boundVars`, `polyKeysFresh` holds vacuously
for any substitution (the condition `boundVars ty ≠ []` is never triggered).
-/
private theorem Subst.polyKeysFresh_of_mono (S : Subst) (Γ : TContext Unit)
    (h_mono : ContextMono Γ) :
    Subst.polyKeysFresh (T := CoreLParams) S Γ := by
  intro a _ x ty h_find h_bv
  exact absurd (h_mono x ty h_find) h_bv

/-! ### Inversion lemmas -/

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

/-! ## Part I — Unannotated soundness (`Cmd.typeCheck_sound`) -/

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

/-! ### Main Soundness Theorem -/

/--
Soundness of the command typechecker: if `Cmd.typeCheck` succeeds, then
`CmdHasType` holds between the substituted input/output contexts.

**Rigid-var-identity invariant** (`h_rigid_inv`):
`∀ v ∈ C.rigidTypeVars, subst S (ftvar v) = ftvar v`.

*Established* in `ProcedureType.typeCheck`: `setupInputEnv` generates fresh vars
(e.g. `$__ty0`) as rigid, then unifies the original names with them — the rigid
vars are values (not keys) of the initial substitution, so the invariant holds.
(TODO: prove)

*Preserved* by `Cmd.typeCheck_preserves_rigid_inv`: each command's `checkAnnotCompat`
verifies identity on all rigid vars after unification, rejecting any refinement.
-/
theorem Cmd.typeCheck_sound (C : LContext CoreLParams) (Env : TEnv Unit)
    (cmd cmd' : Cmd Expression) (Env' : TEnv Unit)
    (h : Imperative.Cmd.typeCheck C Env cmd = .ok (cmd', Env'))
    (h_wf : TEnvWF (T := CoreLParams) Env)
    (h_fwf : FactoryWF C.functions)
    (h_ne : Env.context.types ≠ [])
    (h_mono : ContextMono Env.context)
    (h_rigid_inv : ∀ v, v ∈ C.rigidTypeVars →
      LMonoTy.subst Env.stateSubstInfo.subst (.ftvar v) = .ftvar v) :
    CmdHasType C (TContext.subst Env.context Env'.stateSubstInfo.subst) cmd
      (TContext.subst Env'.context Env'.stateSubstInfo.subst) := by
  cases cmd with
  | init x xty e md =>
    simp only [Cmd.typeCheck, Bind.bind, Except.bind] at h
    -- lookup returned none → x is fresh (some → already declared → error branch)
    elim_err h
    rename_i h_lookup_none
    split at h
    · -- det case
      rename_i expr heq_det
      elim_err h
      rename_i h_not_in_fv
      elim_err h
      rename_i v1 h_preprocess
      elim_err h
      rename_i v2 h_infer
      elim_err h
      rename_i Env_unified h_unify
      elim_err h
      rename_i _u1 h_checkAnnot1
      elim_err h
      rename_i v3 h_postprocess
      cases h
      simp only [TypeContext.update, TypeContext.lookup, TypeContext.preprocess,
        TypeContext.postprocess, TypeContext.inferType, TypeContext.unifyTypes,
        TypeContext.freeVars, TypeContext.checkAnnotCompat] at *
      have h_find_none := (CmdType.lookup_none_iff_find_none Env x).mp h_lookup_none
      obtain ⟨h_ctx_eq, h_wf_pre, mty_pre, h_mty_pre, mty, h_mty, h_mty_eq, h_v3_eq⟩ :=
        init_det_context_setup C Env x xty heq_det md v1 v2 Env_unified v3
          h_preprocess h_infer h_unify h_postprocess h_wf h_fwf h_ne
      have h_find_none_subst := Lambda.TContext.subst_find_none Env.context
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
      have h_pp : CmdType.preprocess C Env xty = .ok (.forAll [] mty_pre, v1.snd) := by
        rw [h_preprocess, ← h_mty_pre]
      have h_rigid_unified := CmdType.checkAnnotCompat_rigid C Env_unified h_checkAnnot1
      have h_preprocess_subst := CmdType.preprocess_preserves_stateSubstInfo C Env xty v1.fst v1.snd h_preprocess
      have h_infer_absorbs := CmdType.inferType_absorbs C v1.snd v2.2.snd
        (.init x xty (.det heq_det) md) heq_det v2.1 v2.2.fst h_infer h_wf_pre h_fwf
      have h_unify_absorbs := CmdType.unifyTypes_absorbs v2.2.snd Env_unified _ h_unify
      have h_absorbs_unified : Subst.absorbs Env_unified.stateSubstInfo.subst
          Env.stateSubstInfo.subst :=
        Subst.absorbs_trans _ _ _
          (h_preprocess_subst ▸ h_infer_absorbs) h_unify_absorbs
      obtain ⟨tys, h_tys_len, h_rac⟩ := CmdType.preprocess_isInstance_rigidAnnotCompat C Env v1.snd
        Env_unified.stateSubstInfo.subst xty mty_pre h_pp h_wf
        h_rigid_unified h_absorbs_unified
      rw [← TContext.subst_aliases Env.context
        (CmdType.update v3.snd x v3.fst).stateSubstInfo.subst] at h_rac
      exact CmdHasType'.init_det _ x xty heq_det _ tys md
        h_find_none_subst h_not_in_vars h_tys_len h_rac h_hastype
    · -- nondet case
      rename_i heq_nondet
      elim_err h
      rename_i v1 h_preprocess
      elim_err h
      rename_i v2 h_postprocess
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
      obtain ⟨mty_pre, h_mty_pre⟩ := CmdType.preprocess_mono C Env xty v1.fst v1.snd h_preprocess
      have h_pr := CmdType.postprocess_result C v1.snd v2.snd mty_pre v2.fst
        (h_mty_pre ▸ h_postprocess)
      have h_subst_eq := CmdType.update_preserves_subst v2.snd x v2.fst
      -- Double-subst collapses by idempotence since postprocess preserves env.
      have h_mty_eq : mty = LMonoTy.subst v2.snd.stateSubstInfo.subst mty_pre := by
        have h_mty' := h_mty
        rw [h_subst_eq, h_pr.1, LTy.subst_forAll_nil] at h_mty'
        have h_eq := ((LTy.forAll.injEq _ _ _ _ ▸ h_mty').2).symm
        rw [h_pr.2] at h_eq
        rw [LMonoTy.subst_idempotent v1.snd.stateSubstInfo.subst
          v1.snd.stateSubstInfo.isWF mty_pre] at h_eq
        rw [← h_pr.2] at h_eq
        exact h_eq
      have h_pp : CmdType.preprocess C Env xty = .ok (.forAll [] mty_pre, v1.snd) := by
        rw [h_preprocess, ← h_mty_pre]
      -- v2.snd = v1.snd (postprocess preserves), so v2.snd.subst = Env.subst.
      have h_v2_subst : v2.snd.stateSubstInfo = Env.stateSubstInfo := by
        rw [h_pr.2]
        exact CmdType.preprocess_preserves_stateSubstInfo C Env xty v1.fst v1.snd h_preprocess
      have h_rigid_v2 : ∀ v, v ∈ C.rigidTypeVars →
          LMonoTy.subst v2.snd.stateSubstInfo.subst (.ftvar v) = .ftvar v := by
        intro v hv; rw [congrArg (·.subst) h_v2_subst]; exact h_rigid_inv v hv
      have h_absorbs_nondet : Subst.absorbs v2.snd.stateSubstInfo.subst
          Env.stateSubstInfo.subst := by
        rw [congrArg (·.subst) h_v2_subst]
        exact Subst.absorbs_refl _ Env.stateSubstInfo.isWF
      obtain ⟨tys, h_tys_len, h_rac0⟩ :=
        CmdType.preprocess_isInstance_rigidAnnotCompat C Env v1.snd
          v2.snd.stateSubstInfo.subst xty mty_pre h_pp h_wf
          h_rigid_v2 h_absorbs_nondet
      rw [← h_mty_eq] at h_rac0
      rw [← TContext.subst_aliases Env.context
        (CmdType.update v2.snd x v2.fst).stateSubstInfo.subst] at h_rac0
      exact CmdHasType'.init_nondet _ x xty mty tys md h_find_none_subst h_tys_len h_rac0
  | set x e md =>
    simp only [Cmd.typeCheck, Bind.bind, Except.bind] at h
    elim_err h
    rename_i xty h_lookup
    cases e with
    | det expr =>
      simp only [] at h
      elim_err h
      rename_i v heq
      elim_err h
      rename_i Env_unified h_unify
      elim_err h
      rename_i _u h_checkAnnot
      cases h
      obtain ⟨e', ety, Env_infer⟩ := v
      simp only at heq h_unify ⊢
      have h_find := (CmdType.lookup_some_iff_find_some Env x xty).mp h_lookup
      have h_find_subst := Lambda.TContext.subst_find_some Env.context
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
    elim_err h
    rename_i v heq
    elim_err h
    rename_i _u h_checkAnnot_a
    elim_err h
    rename_i h_bool
    cases h
    obtain ⟨e', ety, Env_out⟩ := v
    obtain ⟨h_ht, h_ctx⟩ := inferType_bool_HasType C Env Env_out
      (.assert label e md) e e' ety heq h_bool h_wf h_fwf h_ne h_mono
    rw [h_ctx]
    exact CmdHasType'.assert _ label e md h_ht
  | assume label e md =>
    simp only [Cmd.typeCheck, Bind.bind, Except.bind] at h
    elim_err h
    rename_i v heq
    elim_err h
    rename_i _u h_checkAnnot_a
    elim_err h
    rename_i h_bool
    cases h
    obtain ⟨e', ety, Env_out⟩ := v
    obtain ⟨h_ht, h_ctx⟩ := inferType_bool_HasType C Env Env_out
      (.assume label e md) e e' ety heq h_bool h_wf h_fwf h_ne h_mono
    rw [h_ctx]
    exact CmdHasType'.assume _ label e md h_ht
  | cover label e md =>
    simp only [Cmd.typeCheck, Bind.bind, Except.bind] at h
    elim_err h
    rename_i v heq
    elim_err h
    rename_i _u h_checkAnnot_a
    elim_err h
    rename_i h_bool
    cases h
    obtain ⟨e', ety, Env_out⟩ := v
    obtain ⟨h_ht, h_ctx⟩ := inferType_bool_HasType C Env Env_out
      (.cover label e md) e e' ety heq h_bool h_wf h_fwf h_ne h_mono
    rw [h_ctx]
    exact CmdHasType'.cover _ label e md h_ht

/-! ## Part II — Annotated soundness (`Cmd.typeCheck_annotated_sound`) -/

-- Lemmas about [getVars] preservation for freshness hypothesis

/-- Rewriting user-provided type annotations leaves the free variables unchanged. -/
private theorem replaceUserProvidedType_getVars (e : LExpr T) (f : T.TypeType → T.TypeType) :
    LExpr.getVars (LExpr.replaceUserProvidedType e f) = LExpr.getVars e := by
  induction e with
  | const | bvar | op => simp [LExpr.replaceUserProvidedType, LExpr.getVars]
  | fvar => simp [LExpr.replaceUserProvidedType, LExpr.getVars]
  | app _ _ _ ih1 ih2 => simp [LExpr.replaceUserProvidedType, LExpr.getVars, ih1, ih2]
  | abs _ _ _ _ ih => simp [LExpr.replaceUserProvidedType, LExpr.getVars, ih]
  | quant _ _ _ _ _ _ ih1 ih2 => simp [LExpr.replaceUserProvidedType, LExpr.getVars, ih1, ih2]
  | ite _ _ _ _ ih1 ih2 ih3 => simp [LExpr.replaceUserProvidedType, LExpr.getVars, ih1, ih2, ih3]
  | eq _ _ _ ih1 ih2 => simp [LExpr.replaceUserProvidedType, LExpr.getVars, ih1, ih2]

/-- Applying a type substitution to an expression leaves its free variables unchanged. -/
private theorem applySubst_getVars_eq (e : LExpr CoreLParams.mono) (S : Subst) :
    LExpr.getVars (e.applySubst S) = LExpr.getVars e := by
  rw [LExpr.applySubst_eq_replaceUserProvidedType]
  exact replaceUserProvidedType_getVars e _

/-- Expressions that are equal modulo type annotations have the same free variables. -/
private theorem eqModuloAnnotations_getVars
    {e₁ : LExpr ⟨⟨M₁, IDMeta⟩, Ty₁⟩} {e₂ : LExpr ⟨⟨M₂, IDMeta⟩, Ty₂⟩}
    (h : EqModuloAnnotations e₁ e₂) :
    LExpr.getVars e₁ = LExpr.getVars e₂ := by
  induction e₁ generalizing e₂ <;>
  cases e₂ <;> simp [EqModuloAnnotations, LExpr.getVars] at h ⊢ <;>
  grind


/-- Apply a type substitution to all expressions in a command. -/
def Cmd.applySubst (c : Cmd Expression) (S : Subst) : Cmd Expression :=
  match c with
  | .init x xty (.det e) md => .init x xty (.det (e.applySubst S)) md
  | .init x xty .nondet md => .init x xty .nondet md
  | .set x (.det e) md => .set x (.det (e.applySubst S)) md
  | .set x .nondet md => .set x .nondet md
  | .assert l e md => .assert l (e.applySubst S) md
  | .assume l e md => .assume l (e.applySubst S) md
  | .cover l e md => .cover l (e.applySubst S) md

/-- `inferType` produces an expression satisfying `HasTypeA`. -/
theorem CmdType.inferType_HasTypeA (C : LContext CoreLParams) (Env Env' : TEnv Unit)
    (c : Cmd Expression) (e e' : LExpr CoreLParams.mono) (ety : LTy)
    (h : CmdType.inferType C Env c e = .ok (e', ety, Env'))
    (h_wf : TEnvWF (T := CoreLParams) Env)
    (h_fwf : FactoryWF C.functions)
    (h_resolved : TContext.AliasesResolved Env.context) :
    ∃ mty, ety = .forAll [] mty ∧ LExpr.HasTypeA [] e' mty := by
  obtain ⟨ea, h_resolve, h_e'_eq, h_ety⟩ := CmdType.inferType_decompose C Env c e e' ety Env' h
  subst h_e'_eq
  exact ⟨ea.toLMonoTy, h_ety, resolve_HasTypeA e ea C Env Env' h_resolve h_wf h_fwf h_resolved⟩

/--
Common proof for assert/assume/cover: if `inferType` succeeds and the result
is bool-typed, then `HasTypeA` holds for the substituted expression at type bool,
and the context is preserved.
-/
private theorem inferType_bool_HasTypeA (C : LContext CoreLParams) (Env Env_out : TEnv Unit)
    (c : Cmd Expression) (e e' : LExpr CoreLParams.mono) (ety : LTy)
    (h_infer : CmdType.inferType C Env c e = .ok (e', ety, Env_out))
    (h_isbool : CmdType.isBoolType ety = true)
    (h_wf : TEnvWF (T := CoreLParams) Env)
    (h_fwf : FactoryWF C.functions)
    (h_ne : Env.context.types ≠ [])
    (h_resolved : TContext.AliasesResolved Env.context) :
    LExpr.HasTypeA [] (e'.applySubst Env_out.stateSubstInfo.subst) .bool ∧
    Env_out.context = Env.context := by
  obtain ⟨mty, h_ety, h_hta⟩ := CmdType.inferType_HasTypeA C Env Env_out c e e' ety
    h_infer h_wf h_fwf h_resolved
  have h_bool_mty : mty = .bool := by
    have h_eq := CmdType.isBoolType_eq _ h_isbool
    rw [h_ety] at h_eq; cases h_eq; rfl
  subst h_bool_mty
  have h_ctx := CmdType.inferType_preserves_context C Env Env_out c e e' ety h_infer h_wf h_ne h_fwf
  have h_hta_subst := applySubst_typeCheck Env_out.stateSubstInfo.subst h_hta
  simp [LMonoTy.subst_bool] at h_hta_subst
  exact ⟨h_hta_subst, h_ctx⟩

/--
Annotated soundness of the command typechecker: if `Cmd.typeCheck` succeeds,
the output command satisfies `CmdHasTypeA` between the substituted contexts.

The substitution is needed because variable types in `Env.context` may contain
unresolved type variables. After applying the final substitution, the context
types become ground and match the expression types from `resolve` (which already
applies the substitution internally).
-/
theorem Cmd.typeCheck_annotated_sound (C : LContext CoreLParams) (Env : TEnv Unit)
    (cmd cmd' : Cmd Expression) (Env' : TEnv Unit)
    (h : Imperative.Cmd.typeCheck C Env cmd = .ok (cmd', Env'))
    (h_wf : TEnvWF (T := CoreLParams) Env)
    (h_fwf : FactoryWF C.functions)
    (h_ne : Env.context.types ≠ [])
    (h_mono : ContextMono Env.context)
    (h_resolved : TContext.AliasesResolved Env.context) :
    CmdHasTypeA C (TContext.subst Env.context Env'.stateSubstInfo.subst)
      (TypeSpec.Cmd.applySubst cmd' Env'.stateSubstInfo.subst)
      (TContext.subst Env'.context Env'.stateSubstInfo.subst) := by
  cases cmd with
  | init x xty e md =>
    simp only [Cmd.typeCheck, Bind.bind, Except.bind] at h
    -- x fresh (some → already declared → error branch)
    elim_err h
    rename_i h_lookup_none
    split at h
    · -- det case
      rename_i expr heq_det
      elim_err h
      rename_i h_not_in_fv
      elim_err h
      rename_i v1 h_preprocess
      elim_err h
      rename_i v2 h_infer
      elim_err h
      rename_i Env_unified h_unify
      elim_err h
      rename_i _u2 h_checkAnnot2
      elim_err h
      rename_i v3 h_postprocess
      cases h
      simp only [TypeContext.update, TypeContext.lookup, TypeContext.preprocess,
        TypeContext.postprocess, TypeContext.inferType, TypeContext.unifyTypes,
        TypeContext.freeVars, TypeContext.checkAnnotCompat] at *
      have h_find_none := (CmdType.lookup_none_iff_find_none Env x).mp h_lookup_none
      obtain ⟨h_ctx_eq, h_wf_pre, mty_pre, h_mty_pre, mty, h_mty, h_mty_eq, h_v3_eq⟩ :=
        init_det_context_setup C Env x xty heq_det md v1 v2 Env_unified v3
          h_preprocess h_infer h_unify h_postprocess h_wf h_fwf h_ne
      have h_fresh_v3 : v3.snd.context.types.find? x = none :=
        h_ctx_eq ▸ h_find_none
      have h_update_ctx := CmdType.update_subst_context v3.snd x v3.fst
        (CmdType.update v3.snd x v3.fst).stateSubstInfo.subst h_fresh_v3
      rw [h_update_ctx, h_ctx_eq, h_mty]
      have h_ctx_pre := CmdType.preprocess_preserves_context C Env xty v1.fst v1.snd h_preprocess
      have h_resolved_pre : TContext.AliasesResolved v1.snd.context :=
        h_ctx_pre ▸ h_resolved
      obtain ⟨mty_infer, h_ety_eq, h_hta⟩ := CmdType.inferType_HasTypeA C v1.snd v2.2.snd
        (Cmd.init x xty (.det heq_det) md) heq_det v2.1 v2.2.fst
        h_infer h_wf_pre h_fwf h_resolved_pre
      have h_subst_eq : (CmdType.update v3.snd x v3.fst).stateSubstInfo.subst =
          Env_unified.stateSubstInfo.subst := by
        rw [CmdType.update_preserves_subst, h_v3_eq]
      have h_hta_subst := applySubst_typeCheck
        (CmdType.update v3.snd x v3.fst).stateSubstInfo.subst h_hta
      simp at h_hta_subst
      have h_unify_eq : LMonoTy.subst
          (CmdType.update v3.snd x v3.fst).stateSubstInfo.subst mty_infer = mty := by
        rw [h_subst_eq, h_mty_eq]
        rw [h_mty_pre, h_ety_eq] at h_unify
        exact (CmdType.unifyTypes_eq v2.2.snd Env_unified mty_pre mty_infer h_unify).symm
      rw [h_unify_eq] at h_hta_subst
      have h_not_in_vars : x ∉ HasVarsPure.getVars (P := Expression) heq_det :=
        fun hv => h_not_in_fv ((CmdType.freeVars_eq_getVars heq_det x).mpr hv)
      have h_resolve_eq := CmdType.inferType_decompose C v1.snd
        (Cmd.init x xty (.det heq_det) md) heq_det v2.1 v2.2.fst v2.2.snd h_infer
      obtain ⟨ea, h_resolve, h_v2_eq, _⟩ := h_resolve_eq
      have h_ws_pre : WellScoped heq_det v1.snd.context :=
        CmdType.inferType_fvars_in_knownVars C v1.snd
          (Cmd.init x xty (.det heq_det) md) heq_det v2.1 v2.2.fst v2.2.snd h_infer
      have h_eqmod := resolve_eqModuloAnnotations heq_det ea C v1.snd v2.2.snd h_resolve
        h_wf_pre (h_ctx_pre ▸ h_ne) h_resolved_pre h_fwf h_ws_pre
      have h_vars_eq : LExpr.getVars v2.1 = LExpr.getVars heq_det := by
        rw [h_v2_eq]
        exact eqModuloAnnotations_getVars h_eqmod
      have h_not_in_v2 : x ∉ HasVarsPure.getVars (P := Expression)
          (v2.1.applySubst (CmdType.update v3.snd x v3.fst).stateSubstInfo.subst) := by
        simp only [HasVarsPure.getVars, Imperative.HasVarsPure.getVars]
        rw [applySubst_getVars_eq]
        simp only [HasVarsPure.getVars, Imperative.HasVarsPure.getVars] at h_not_in_vars
        rw [h_vars_eq]
        exact h_not_in_vars
      simp only [Cmd.applySubst]
      have h_find_none_subst := Lambda.TContext.subst_find_none Env.context
        (CmdType.update v3.snd x v3.fst).stateSubstInfo.subst x h_find_none
      -- The output command's declared type `v3.fst` is already the monotype `mty`,
      -- so the instantiation is trivial (`tys = []`) and `AliasEquiv` is reflexive.
      have h_pr := CmdType.postprocess_result C Env_unified v3.snd mty_pre v3.fst
        (h_mty_pre ▸ h_postprocess)
      have h_v3_mty : v3.fst = LTy.forAll [] mty := by rw [h_pr.1, h_mty_eq]
      have h_open : LTy.openFull v3.fst [] = mty := by
        rw [h_v3_mty]
        simp only [LTy.openFull, LTy.boundVars, LTy.toMonoTypeUnsafe, List.zip_nil_left]
        exact LMonoTy.subst_emptyS (by simp [Subst.hasEmptyScopes, Map.isEmpty])
      have h_tyslen : ([] : List LMonoTy).length = (LTy.boundVars v3.fst).length := by
        rw [h_v3_mty]; simp [LTy.boundVars]
      have h_rac : RigidAnnotCompat (Env.context.subst
          (CmdType.update v3.snd x v3.fst).stateSubstInfo.subst).aliases
          C.rigidTypeVars (LTy.openFull v3.fst []) mty := by
        rw [h_open]; exact .of_eq
      exact CmdHasType'.init_det _ x v3.fst _ _ [] md
        h_find_none_subst h_not_in_v2 h_tyslen h_rac h_hta_subst
    · -- nondet case
      rename_i heq_nondet
      elim_err h
      rename_i v1 h_preprocess
      elim_err h
      rename_i v2 h_postprocess
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
      simp only [Cmd.applySubst]
      -- The output command's declared type `v2.fst` is already the monotype `mty`.
      obtain ⟨mty_pre, h_mty_pre⟩ := CmdType.preprocess_mono C Env xty v1.fst v1.snd h_preprocess
      have h_pr := CmdType.postprocess_result C v1.snd v2.snd mty_pre v2.fst
        (h_mty_pre ▸ h_postprocess)
      have h_subst_eq := CmdType.update_preserves_subst v2.snd x v2.fst
      have h_v2_mty : v2.fst = LTy.forAll [] mty := by
        have h_mty' := h_mty
        rw [h_subst_eq, h_pr.1, LTy.subst_forAll_nil] at h_mty'
        rw [h_pr.2] at h_mty'
        have h_idem := LMonoTy.subst_idempotent v1.snd.stateSubstInfo.subst
          v1.snd.stateSubstInfo.isWF mty_pre
        rw [h_idem] at h_mty'
        rw [h_pr.1]; exact h_mty'
      have h_open : LTy.openFull v2.fst [] = mty := by
        rw [h_v2_mty]
        simp only [LTy.openFull, LTy.boundVars, LTy.toMonoTypeUnsafe, List.zip_nil_left]
        exact LMonoTy.subst_emptyS (by simp [Subst.hasEmptyScopes, Map.isEmpty])
      have h_tyslen : ([] : List LMonoTy).length = (LTy.boundVars v2.fst).length := by
        rw [h_v2_mty]; simp [LTy.boundVars]
      have h_rac : RigidAnnotCompat (Env.context.subst
          (CmdType.update v2.snd x v2.fst).stateSubstInfo.subst).aliases
          C.rigidTypeVars (LTy.openFull v2.fst []) mty := by
        rw [h_open]; exact .of_eq
      exact CmdHasType'.init_nondet _ x v2.fst mty [] md h_find_none_subst h_tyslen h_rac
  | set x e md =>
    simp only [Cmd.typeCheck, Bind.bind, Except.bind] at h
    elim_err h
    rename_i xty h_lookup
    cases e with
    | det expr =>
      simp only [] at h
      elim_err h
      rename_i v heq
      elim_err h
      rename_i Env_unified h_unify
      elim_err h
      rename_i _u h_checkAnnot
      cases h
      obtain ⟨e', ety, Env_infer⟩ := v
      simp at heq h_unify ⊢
      have h_find := (CmdType.lookup_some_iff_find_some Env x xty).mp h_lookup
      have h_xty_bv := h_mono x xty h_find
      obtain ⟨xs, mty_x⟩ := xty
      simp [LTy.boundVars] at h_xty_bv
      subst h_xty_bv
      have h_find_subst := Lambda.TContext.subst_find_some Env.context
        Env'.stateSubstInfo.subst x (.forAll [] mty_x) h_find
      rw [LTy.subst_forAll_nil] at h_find_subst
      obtain ⟨mty_infer, h_ety_eq, h_hta⟩ := CmdType.inferType_HasTypeA C Env _
        (.set x (.det expr) md) expr _ _ heq h_wf h_fwf h_resolved
      have h_ctx_infer := CmdType.inferType_preserves_context C Env Env_infer
        (.set x (.det expr) md) expr e' ety heq h_wf h_ne h_fwf
      have h_ctx_unify := CmdType.unifyTypes_preserves_context Env_infer Env'
        [(.forAll [] mty_x, ety)] h_unify
      have h_ctx : Env'.context = Env.context := by rw [h_ctx_unify, h_ctx_infer]
      rw [h_ctx]
      have h_unify_eq : LMonoTy.subst Env'.stateSubstInfo.subst mty_infer =
          LMonoTy.subst Env'.stateSubstInfo.subst mty_x := by
        rw [h_ety_eq] at h_unify
        exact (CmdType.unifyTypes_eq Env_infer Env' mty_x mty_infer h_unify).symm
      have h_hta_subst := applySubst_typeCheck Env'.stateSubstInfo.subst h_hta
      simp at h_hta_subst
      rw [h_unify_eq] at h_hta_subst
      simp only [Cmd.applySubst]
      exact CmdHasType'.set_det _ x (LMonoTy.subst Env'.stateSubstInfo.subst mty_x) _ md
        h_find_subst h_hta_subst
    | nondet =>
      simp at h
      cases h
      obtain ⟨mty, h_find_subst⟩ := set_nondet_sound Env x xty h_lookup h_mono
      exact CmdHasType'.set_nondet _ x mty md h_find_subst
  | assert label e md =>
    simp only [Cmd.typeCheck, Bind.bind, Except.bind] at h
    elim_err h
    rename_i v heq
    elim_err h
    rename_i _u h_checkAnnot_a2
    elim_err h
    rename_i h_bool
    cases h
    obtain ⟨e', ety, Env_out⟩ := v
    simp at heq
    obtain ⟨h_hta, h_ctx⟩ := inferType_bool_HasTypeA C Env Env_out
      (.assert label e md) e e' ety heq h_bool h_wf h_fwf h_ne h_resolved
    rw [h_ctx]
    exact CmdHasType'.assert _ label _ md h_hta
  | assume label e md =>
    simp only [Cmd.typeCheck, Bind.bind, Except.bind] at h
    elim_err h
    rename_i v heq
    elim_err h
    rename_i _u h_checkAnnot_a2
    elim_err h
    rename_i h_bool
    cases h
    obtain ⟨e', ety, Env_out⟩ := v
    simp at heq
    obtain ⟨h_hta, h_ctx⟩ := inferType_bool_HasTypeA C Env Env_out
      (.assume label e md) e e' ety heq h_bool h_wf h_fwf h_ne h_resolved
    rw [h_ctx]
    exact CmdHasType'.assume _ label _ md h_hta
  | cover label e md =>
    simp only [Cmd.typeCheck, Bind.bind, Except.bind] at h
    elim_err h
    rename_i v heq
    elim_err h
    rename_i _u h_checkAnnot_a2
    elim_err h
    rename_i h_bool
    cases h
    obtain ⟨e', ety, Env_out⟩ := v
    simp at heq
    obtain ⟨h_hta, h_ctx⟩ := inferType_bool_HasTypeA C Env Env_out
      (.cover label e md) e e' ety heq h_bool h_wf h_fwf h_ne h_resolved
    rw [h_ctx]
    exact CmdHasType'.cover _ label _ md h_hta

end TypeSpec
end Core
