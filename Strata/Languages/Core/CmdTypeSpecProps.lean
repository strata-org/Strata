/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

import Strata.Languages.Core.CmdTypeSpec
import Strata.Languages.Core.CmdTypeProps
import all Strata.Languages.Core.CmdType
import all Strata.Languages.Core.CmdTypeProps
import all Strata.Languages.Core.StatementType
import Strata.DL.Imperative.CmdType
import all Strata.DL.Imperative.CmdType
import all Strata.DL.Imperative.Cmd
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

/-- `ContextMono` transports across context equivalence (it reads `Γ` only
    through `find?`). Since the `HMap` migration made context preservation an
    `Equiv` rather than a structural equality, this replaces the old `rw [h_ctx]`. -/
theorem ContextMono.of_equiv {Γ Γ' : TContext Unit}
    (h : TContext.Equiv (T := CoreLParams) Γ Γ') (h_mono : ContextMono Γ) : ContextMono Γ' := by
  intro x ty h_find
  exact h_mono x ty ((h.find? x).trans h_find)

/--
When all context types have empty `boundVars`, `polyKeysFresh` holds vacuously
for any substitution (the condition `boundVars ty ≠ []` is never triggered).
-/
private theorem Subst.polyKeysFresh_of_mono (S : Subst) (Γ : TContext Unit)
    (h_mono : ContextMono Γ) :
    Subst.polyKeysFresh (T := CoreLParams) S Γ := by
  intro a _ x ty h_find h_bv
  exact absurd (h_mono x ty h_find) h_bv

/-- All context types are well-kinded (relative to `C`'s registered arities).
    A `TEnv`-level invariant preserved by `Cmd.typeCheck`, mirroring `ContextMono`.
    The `set`-det case unifies against a context type, so its output subst is
    range-well-kinded only if context types are themselves well-kinded. -/
def ContextWellKinded (C : LContext CoreLParams) (Γ : TContext Unit) : Prop :=
  ∀ x mty, Γ.types.find? x = some (.forAll [] mty) →
    LMonoTy.WellKinded (fun n => C.knownTypes[n]?) mty

/-- `ContextWellKinded` transports across context equivalence (reads via `find?`). -/
theorem ContextWellKinded.of_equiv {C : LContext CoreLParams} {Γ Γ' : TContext Unit}
    (h : TContext.Equiv (T := CoreLParams) Γ Γ') (h_wk : ContextWellKinded C Γ) :
    ContextWellKinded C Γ' := by
  intro x mty h_find
  exact h_wk x mty ((h.find? x).trans h_find)

/-- **Bundled WK preservation.** A successful `Cmd.typeCheck` step preserves BOTH
    the subst-range well-kindedness AND the context-types well-kindedness invariants
    (relative to `C`'s registered arities). The two are bundled because they are
    coupled: after `init`/`set` the stored context type is the unified/substituted
    result, well-kinded only given a range-well-kinded subst. -/
theorem Cmd.typeCheck_preserves_WK (C : LContext CoreLParams) (Env : TEnv Unit)
    (cmd cmd' : Cmd Expression) (Env' : TEnv Unit)
    (h : Imperative.Cmd.typeCheck C Env cmd = .ok (cmd', Env'))
    (h_base : BaseTypesWK C)
    (h_wf : TEnvWF (T := CoreLParams) Env)
    (h_fwf : FactoryWF C.functions)
    (h_ne : Env.context.types ≠ [])
    (h_mono : ContextMono Env.context)
    (h_wk : Subst.RangeWellKinded (fun n => C.knownTypes[n]?) Env.stateSubstInfo.subst)
    (h_cwk : ContextWellKinded C Env.context) :
    Subst.RangeWellKinded (fun n => C.knownTypes[n]?) Env'.stateSubstInfo.subst ∧
      ContextWellKinded C Env'.context := by
  cases cmd with
  | init x xty e md =>
    simp only [Cmd.typeCheck, Bind.bind, Except.bind] at h
    elim_err h; rename_i h_lookup
    split at h
    · rename_i expr _
      elim_err h; rename_i h_not_in_fv
      elim_err h; rename_i v1 h_preprocess
      elim_err h; rename_i v2 h_infer
      elim_err h; rename_i Env_unified h_unify
      elim_err h; rename_i _u h_check
      elim_err h; rename_i v3 h_postprocess; cases h
      simp only [TypeContext.update, TypeContext.lookup, TypeContext.preprocess,
        TypeContext.postprocess, TypeContext.inferType, TypeContext.unifyTypes,
        TypeContext.freeVars, TypeContext.checkAnnotCompat] at *
      obtain ⟨v1ty, Env_pre⟩ := v1
      obtain ⟨e', ety, Env_infer⟩ := v2
      obtain ⟨mty_pre, h_mty_pre⟩ := CmdType.preprocess_mono C Env xty v1ty Env_pre h_preprocess
      subst h_mty_pre
      have h_pre_subst : Env_pre.stateSubstInfo = Env.stateSubstInfo :=
        CmdType.preprocess_preserves_stateSubstInfo C Env xty _ Env_pre h_preprocess
      have h_wk_pre : Subst.RangeWellKinded (fun n => C.knownTypes[n]?) Env_pre.stateSubstInfo.subst := by
        rw [congrArg (·.subst) h_pre_subst]; exact h_wk
      have h_pre_wk : LMonoTy.WellKinded (fun n => C.knownTypes[n]?) mty_pre :=
        CmdType.preprocess_WellKindedTy C Env Env_pre xty mty_pre h_preprocess h_wk
      obtain ⟨h_wk_infer, h_infer_wk⟩ :=
        CmdType.inferType_RangeWellKinded C Env_pre Env_infer _ _ e' ety h_infer h_base h_wk_pre
      obtain ⟨mty_inf, h_ety_eq, _⟩ :=
        CmdType.inferType_output_fresh C Env_pre Env_infer _ _ e' ety h_infer
          (CmdType.preprocess_preserves_TEnvWF C Env xty _ Env_pre h_preprocess h_wf) h_fwf
      have h_inf_wk : LMonoTy.WellKinded (fun n => C.knownTypes[n]?) mty_inf :=
        h_infer_wk mty_inf h_ety_eq
      subst h_ety_eq
      have h_wk_unified : Subst.RangeWellKinded (fun n => C.knownTypes[n]?)
          Env_unified.stateSubstInfo.subst :=
        CmdType.unifyTypes_RangeWellKinded C Env_infer Env_unified mty_pre mty_inf h_unify
          h_pre_wk h_inf_wk h_wk_infer
      obtain ⟨v3fst, v3snd⟩ := v3
      obtain ⟨h_v3_fst, h_v3_snd⟩ := CmdType.postprocess_result C Env_unified v3snd mty_pre v3fst
        (by rw [h_postprocess])
      refine ⟨by rw [CmdType.update_preserves_subst, h_v3_snd]; exact h_wk_unified, ?_⟩
      rw [h_v3_snd, h_v3_fst]
      have h_stored_wk : LMonoTy.WellKinded (fun n => C.knownTypes[n]?)
          (LMonoTy.subst Env_unified.stateSubstInfo.subst mty_pre) :=
        LMonoTy.WellKinded_subst _ _ _ h_pre_wk
          (fun v _ => h_wk_unified.lookup _ v)
      have h_ctx_pre : Env_pre.context = Env.context :=
        CmdType.preprocess_preserves_context C Env xty _ Env_pre h_preprocess
      have h_ne_pre : Env_pre.context.types ≠ [] := h_ctx_pre ▸ h_ne
      have h_ctx_infer : TContext.Equiv (T := CoreLParams) Env_infer.context Env_pre.context :=
        CmdType.inferType_preserves_context C Env_pre Env_infer _ _ e' _
          h_infer (CmdType.preprocess_preserves_TEnvWF C Env xty _ Env_pre h_preprocess h_wf)
          h_ne_pre h_fwf
      have h_ctx_unify : Env_unified.context = Env_infer.context :=
        CmdType.unifyTypes_preserves_context Env_infer Env_unified _ h_unify
      have h_cwk_unified : ContextWellKinded C Env_unified.context := by
        rw [h_ctx_unify]
        exact ContextWellKinded.of_equiv (h_ctx_infer.trans (TContext.Equiv.of_eq h_ctx_pre)).symm h_cwk
      intro y mty h_find
      simp only [CmdType.update, TEnv.addInNewestContext, TEnv.updateContext, TEnv.context] at h_find
      rcases Strata.Util.HMaps.find?_addInNewest_single Env_unified.genEnv.context.types x
          (.forAll [] (LMonoTy.subst Env_unified.stateSubstInfo.subst mty_pre)) y with
        ⟨h_new, _⟩ | h_old
      · rw [h_new] at h_find; injection h_find with h_find
        injection h_find with _ h_mty; subst h_mty; exact h_stored_wk
      · rw [h_old] at h_find
        exact h_cwk_unified y mty (by simpa only [TEnv.context] using h_find)
    · rename_i _
      elim_err h; rename_i v1 h_preprocess
      elim_err h; rename_i v2 h_postprocess; cases h
      simp only [TypeContext.update, TypeContext.preprocess, TypeContext.postprocess] at *
      obtain ⟨v1ty, Env_pre⟩ := v1
      obtain ⟨mty_pre, h_mty_pre⟩ := CmdType.preprocess_mono C Env xty v1ty Env_pre h_preprocess
      subst h_mty_pre
      obtain ⟨v2fst, v2snd⟩ := v2
      obtain ⟨h_v2_fst, h_v2_snd⟩ := CmdType.postprocess_result C Env_pre v2snd mty_pre v2fst
        (by rw [h_postprocess])
      have h_pre_subst : Env_pre.stateSubstInfo = Env.stateSubstInfo :=
        CmdType.preprocess_preserves_stateSubstInfo C Env xty _ Env_pre h_preprocess
      have h_pre_wk : LMonoTy.WellKinded (fun n => C.knownTypes[n]?) mty_pre :=
        CmdType.preprocess_WellKindedTy C Env Env_pre xty mty_pre h_preprocess h_wk
      refine ⟨by rw [CmdType.update_preserves_subst, h_v2_snd, congrArg (·.subst) h_pre_subst]; exact h_wk, ?_⟩
      rw [h_v2_snd, h_v2_fst]
      have h_stored_wk : LMonoTy.WellKinded (fun n => C.knownTypes[n]?)
          (LMonoTy.subst Env_pre.stateSubstInfo.subst mty_pre) := by
        rw [congrArg (·.subst) h_pre_subst]
        exact LMonoTy.WellKinded_subst _ _ _ h_pre_wk (fun v _ => h_wk.lookup _ v)
      have h_ctx_pre : Env_pre.context = Env.context :=
        CmdType.preprocess_preserves_context C Env xty _ Env_pre h_preprocess
      have h_cwk_pre : ContextWellKinded C Env_pre.context := h_ctx_pre ▸ h_cwk
      intro y mty h_find
      simp only [CmdType.update, TEnv.addInNewestContext, TEnv.updateContext, TEnv.context] at h_find
      rcases Strata.Util.HMaps.find?_addInNewest_single Env_pre.genEnv.context.types x
          (.forAll [] (LMonoTy.subst Env_pre.stateSubstInfo.subst mty_pre)) y with
        ⟨h_new, _⟩ | h_old
      · rw [h_new] at h_find; injection h_find with h_find
        injection h_find with _ h_mty; subst h_mty; exact h_stored_wk
      · rw [h_old] at h_find
        exact h_cwk_pre y mty (by simpa only [TEnv.context] using h_find)
  | set x e md =>
    simp only [Cmd.typeCheck, Bind.bind, Except.bind] at h
    elim_err h; rename_i xty h_lookup
    cases e with
    | det expr =>
      simp only [] at h
      elim_err h; rename_i v h_infer
      elim_err h; rename_i Env_unified h_unify
      elim_err h; rename_i _u h_check; cases h
      simp only [TypeContext.lookup, TypeContext.inferType, TypeContext.unifyTypes,
        TypeContext.checkAnnotCompat] at *
      obtain ⟨e', ety, Env_infer⟩ := v
      have h_find := (CmdType.lookup_some_iff_find_some Env x xty).mp h_lookup
      have h_xty_bv : LTy.boundVars xty = [] := h_mono x xty h_find
      obtain ⟨xs, mty_x⟩ := xty
      simp only [LTy.boundVars] at h_xty_bv; subst h_xty_bv
      have h_xty_wk : LMonoTy.WellKinded (fun n => C.knownTypes[n]?) mty_x := h_cwk x mty_x h_find
      obtain ⟨h_wk_infer, h_infer_wk⟩ :=
        CmdType.inferType_RangeWellKinded C Env Env_infer _ _ e' ety h_infer h_base h_wk
      obtain ⟨mty_inf, h_ety_eq, _⟩ :=
        CmdType.inferType_output_fresh C Env Env_infer _ expr e' ety h_infer h_wf h_fwf
      have h_inf_wk : LMonoTy.WellKinded (fun n => C.knownTypes[n]?) mty_inf :=
        h_infer_wk mty_inf h_ety_eq
      subst h_ety_eq
      simp only [] at h_unify
      have h_wk_unified : Subst.RangeWellKinded (fun n => C.knownTypes[n]?)
          Env'.stateSubstInfo.subst :=
        CmdType.unifyTypes_RangeWellKinded C Env_infer Env' mty_x mty_inf h_unify
          h_xty_wk h_inf_wk h_wk_infer
      refine ⟨h_wk_unified, ?_⟩
      have h_ctx_infer : TContext.Equiv (T := CoreLParams) Env_infer.context Env.context :=
        CmdType.inferType_preserves_context C Env Env_infer _ expr e' _ h_infer h_wf h_ne h_fwf
      have h_ctx_unify : Env'.context = Env_infer.context :=
        CmdType.unifyTypes_preserves_context Env_infer Env' _ h_unify
      rw [h_ctx_unify]
      exact ContextWellKinded.of_equiv h_ctx_infer.symm h_cwk
    | nondet =>
      simp at h; cases h
      exact ⟨h_wk, h_cwk⟩
  | assert label e md =>
    simp only [Cmd.typeCheck, Bind.bind, Except.bind] at h
    elim_err h; rename_i v h_infer
    elim_err h; rename_i _u h_check
    elim_err h; cases h
    obtain ⟨e', ety, Env_infer⟩ := v
    obtain ⟨h_wk_infer, _⟩ :=
      CmdType.inferType_RangeWellKinded C Env Env_infer _ _ e' ety h_infer h_base h_wk
    refine ⟨h_wk_infer, ?_⟩
    exact ContextWellKinded.of_equiv
      (CmdType.inferType_preserves_context C Env Env_infer _ e e' ety h_infer h_wf h_ne h_fwf).symm
      h_cwk
  | assume label e md =>
    simp only [Cmd.typeCheck, Bind.bind, Except.bind] at h
    elim_err h; rename_i v h_infer
    elim_err h; rename_i _u h_check
    elim_err h; cases h
    obtain ⟨e', ety, Env_infer⟩ := v
    obtain ⟨h_wk_infer, _⟩ :=
      CmdType.inferType_RangeWellKinded C Env Env_infer _ _ e' ety h_infer h_base h_wk
    refine ⟨h_wk_infer, ?_⟩
    exact ContextWellKinded.of_equiv
      (CmdType.inferType_preserves_context C Env Env_infer _ e e' ety h_infer h_wf h_ne h_fwf).symm
      h_cwk
  | cover label e md =>
    simp only [Cmd.typeCheck, Bind.bind, Except.bind] at h
    elim_err h; rename_i v h_infer
    elim_err h; rename_i _u h_check
    elim_err h; cases h
    obtain ⟨e', ety, Env_infer⟩ := v
    obtain ⟨h_wk_infer, _⟩ :=
      CmdType.inferType_RangeWellKinded C Env Env_infer _ _ e' ety h_infer h_base h_wk
    refine ⟨h_wk_infer, ?_⟩
    exact ContextWellKinded.of_equiv
      (CmdType.inferType_preserves_context C Env Env_infer _ e e' ety h_infer h_wf h_ne h_fwf).symm
      h_cwk

/-! ### Inversion lemmas -/

/--
Context setup for the `init x := det` case: establishes that the final
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
    TContext.Equiv (T := CoreLParams) v3.snd.context Env.context ∧
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
  have h_ctx_eq : TContext.Equiv (T := CoreLParams) v3.snd.context Env.context := by
    -- postprocess + unify preserve the context on the nose; inferType only up to Equiv.
    have h1 := h_post_res.2
    have h2 := CmdType.unifyTypes_preserves_context v2.2.snd Env_unified
      [(v1.fst, v2.2.fst)] h_unify
    have h3 := CmdType.inferType_preserves_context C v1.snd v2.2.snd
      (.init x xty (.det heq_det) md) heq_det v2.1 v2.2.fst h_infer
      h_wf_pre h_ne_pre h_fwf
    have h4 := CmdType.preprocess_preserves_context C Env xty v1.fst v1.snd h_preprocess
    -- v3.snd.context = Env_unified.context = v2.2.snd.context ≈ v1.snd.context = Env.context
    rw [h1, h2]
    exact h3.trans (TContext.Equiv.of_eq h4)
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
Context setup for `init x := *` (nondet): the context is preserved and
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
theorem set_nondet_sound (Env : TEnv Unit) (x : CoreIdent) (xty : LTy) (S : Subst)
    (h_lookup : CmdType.lookup Env x = some xty)
    (h_mono : ContextMono Env.context) :
    ∃ mty, (TContext.subst Env.context S).types.find? x =
      some (.forAll [] mty) := by
  have h_find := (CmdType.lookup_some_iff_find_some Env x xty).mp h_lookup
  have h_xty_bv := h_mono x xty h_find
  obtain ⟨xs, mty_x⟩ := xty
  simp [LTy.boundVars] at h_xty_bv
  subst h_xty_bv
  have h_find_subst := Lambda.TContext.subst_find_some Env.context S x
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
    (S : Subst)
    (h_pre : CmdType.preprocess C Env xty = .ok (pre_ty, Env_pre))
    (h_pre_mono : pre_ty = .forAll [] mty_pre)
    (h_infer : CmdType.inferType C Env_pre (.init x xty (.det expr) md) expr = .ok (e', ety, Env_infer))
    (h_unify : CmdType.unifyTypes Env_infer [(pre_ty, ety)] = .ok Env')
    (h_wf : TEnvWF (T := CoreLParams) Env)
    (h_fwf : FactoryWF C.functions)
    (h_mono : ContextMono Env.context)
    (hS_abs : Subst.absorbs S Env'.stateSubstInfo.subst)
    (hS_wf : SubstWF S) :
    HasType (T := CoreLParams) C (TContext.subst Env.context S) expr
      (.forAll [] (LMonoTy.subst S mty_pre)) := by
  have h_wf_pre : TEnvWF (T := CoreLParams) Env_pre :=
    CmdType.preprocess_preserves_TEnvWF C Env xty pre_ty Env_pre h_pre h_wf
  have h_ctx_pre : Env_pre.context = Env.context :=
    CmdType.preprocess_preserves_context C Env xty pre_ty Env_pre h_pre
  obtain ⟨mty_infer, h_ety_eq, h_hastype⟩ :=
    CmdType.inferType_HasType C Env_pre Env_infer (.init x xty (.det expr) md) expr e' ety h_infer h_wf_pre h_fwf
  have h_abs : Subst.absorbs Env'.stateSubstInfo.subst Env_infer.stateSubstInfo.subst :=
    CmdType.unifyTypes_absorbs Env_infer Env' [(pre_ty, ety)] h_unify
  have h_abs_S : Subst.absorbs S Env_infer.stateSubstInfo.subst :=
    Subst.absorbs_trans Env_infer.stateSubstInfo.subst Env'.stateSubstInfo.subst S h_abs hS_abs
  have h_mono_pre : ContextMono Env_pre.context := h_ctx_pre ▸ h_mono
  have h_pkf : Subst.polyKeysFresh (T := CoreLParams) S Env_pre.context :=
    Subst.polyKeysFresh_of_mono _ _ h_mono_pre
  have h_ht := h_hastype S h_abs_S hS_wf h_pkf
  rw [h_ctx_pre] at h_ht
  have h_unify_eq : LMonoTy.subst S mty_infer = LMonoTy.subst S mty_pre := by
    have h_base : LMonoTy.subst Env'.stateSubstInfo.subst mty_infer =
        LMonoTy.subst Env'.stateSubstInfo.subst mty_pre := by
      rw [h_pre_mono, h_ety_eq] at h_unify
      exact (CmdType.unifyTypes_eq Env_infer Env' mty_pre mty_infer h_unify).symm
    calc LMonoTy.subst S mty_infer
        = LMonoTy.subst S (LMonoTy.subst Env'.stateSubstInfo.subst mty_infer) :=
          (LMonoTy.subst_absorbs S Env'.stateSubstInfo.subst mty_infer hS_abs).symm
      _ = LMonoTy.subst S (LMonoTy.subst Env'.stateSubstInfo.subst mty_pre) := by rw [h_base]
      _ = LMonoTy.subst S mty_pre := LMonoTy.subst_absorbs S Env'.stateSubstInfo.subst mty_pre hS_abs
  rw [h_unify_eq] at h_ht
  exact h_ht

/-- For `set x := expr`: the expression has the variable's type under the unified substitution. -/
private theorem set_det_HasType (C : LContext CoreLParams) (Env Env_infer Env' : TEnv Unit)
    (x : CoreIdent) (expr e' : LExpr CoreLParams.mono) (xty ety : LTy)
    (mty_x : LMonoTy) (S : Subst) (h_xty_eq : xty = .forAll [] mty_x)
    (h_infer : CmdType.inferType C Env (.set x (.det expr) md) expr = .ok (e', ety, Env_infer))
    (h_unify : CmdType.unifyTypes Env_infer [(xty, ety)] = .ok Env')
    (h_wf : TEnvWF (T := CoreLParams) Env)
    (h_fwf : FactoryWF C.functions)
    (h_mono : ContextMono Env.context)
    (hS_abs : Subst.absorbs S Env'.stateSubstInfo.subst)
    (hS_wf : SubstWF S) :
    HasType (T := CoreLParams) C (TContext.subst Env.context S) expr
      (LTy.subst S xty) := by
  subst h_xty_eq
  obtain ⟨mty_infer, h_ety_eq, h_hastype⟩ :=
    CmdType.inferType_HasType C Env Env_infer (.set x (.det expr) md) expr e' ety h_infer h_wf h_fwf
  have h_abs : Subst.absorbs Env'.stateSubstInfo.subst Env_infer.stateSubstInfo.subst :=
    CmdType.unifyTypes_absorbs Env_infer Env' [(.forAll [] mty_x, ety)] h_unify
  have h_abs_S : Subst.absorbs S Env_infer.stateSubstInfo.subst :=
    Subst.absorbs_trans Env_infer.stateSubstInfo.subst Env'.stateSubstInfo.subst S h_abs hS_abs
  have h_pkf : Subst.polyKeysFresh (T := CoreLParams) S Env.context :=
    Subst.polyKeysFresh_of_mono _ _ h_mono
  have h_ht := h_hastype S h_abs_S hS_wf h_pkf
  rw [LTy.subst_forAll_nil]
  have h_unify_eq : LMonoTy.subst S mty_infer = LMonoTy.subst S mty_x := by
    have h_base : LMonoTy.subst Env'.stateSubstInfo.subst mty_infer =
        LMonoTy.subst Env'.stateSubstInfo.subst mty_x := by
      rw [h_ety_eq] at h_unify
      exact (CmdType.unifyTypes_eq Env_infer Env' mty_x mty_infer h_unify).symm
    calc LMonoTy.subst S mty_infer
        = LMonoTy.subst S (LMonoTy.subst Env'.stateSubstInfo.subst mty_infer) :=
          (LMonoTy.subst_absorbs S Env'.stateSubstInfo.subst mty_infer hS_abs).symm
      _ = LMonoTy.subst S (LMonoTy.subst Env'.stateSubstInfo.subst mty_x) := by rw [h_base]
      _ = LMonoTy.subst S mty_x := LMonoTy.subst_absorbs S Env'.stateSubstInfo.subst mty_x hS_abs
  rw [h_unify_eq] at h_ht
  exact h_ht

/--
Common proof for assert/assume/cover: if `inferType` succeeds and the result
is bool-typed, then `HasType` holds for the expression at type bool, and
the context is preserved.
-/
private theorem inferType_bool_HasType (C : LContext CoreLParams) (Env Env_out : TEnv Unit)
    (c : Cmd Expression) (e e' : LExpr CoreLParams.mono) (ety : LTy) (S : Subst)
    (h_infer : CmdType.inferType C Env c e = .ok (e', ety, Env_out))
    (h_isbool : CmdType.isBoolType ety = true)
    (h_wf : TEnvWF (T := CoreLParams) Env)
    (h_fwf : FactoryWF C.functions)
    (h_ne : Env.context.types ≠ [])
    (h_mono : ContextMono Env.context)
    (hS_abs : Subst.absorbs S Env_out.stateSubstInfo.subst)
    (hS_wf : SubstWF S) :
    HasType (T := CoreLParams) C (TContext.subst Env.context S) e
      (.forAll [] .bool) ∧
    TContext.Equiv (T := CoreLParams) Env_out.context Env.context := by
  obtain ⟨mty, h_ety_eq, h_hastype⟩ := CmdType.inferType_HasType C Env Env_out c e e' ety h_infer h_wf h_fwf
  have h_bool_ty := CmdType.isBoolType_eq ety h_isbool
  rw [h_ety_eq] at h_bool_ty
  have h_mty_bool : mty = .bool := by cases h_bool_ty; rfl
  subst h_mty_bool
  have h_ctx := CmdType.inferType_preserves_context C Env Env_out c e e' ety h_infer h_wf h_ne h_fwf
  have h_ht := h_hastype S hS_abs hS_wf
    (Subst.polyKeysFresh_of_mono _ _ h_mono)
  rw [LMonoTy.subst_bool] at h_ht
  exact ⟨h_ht, h_ctx⟩

/-! ### Main Soundness Theorem -/

/--
Soundness of the command typechecker: if `Cmd.typeCheck` succeeds, then
`CmdHasType` holds between the substituted input/output contexts.

The rigid-var-identity hypothesis `∀ v ∈ C.rigidTypeVars, subst S (ftvar v) = ftvar v`
is established in `ProcedureType.typeCheck` (rigid vars are values, not keys, of the
initial substitution) and preserved by `Cmd.typeCheck_preserves_rigid_inv` (each
command's `checkAnnotCompat` rejects any refinement of a rigid var).
-/
theorem Cmd.typeCheck_sound_gen (C : LContext CoreLParams) (Env : TEnv Unit)
    (cmd cmd' : Cmd Expression) (Env' : TEnv Unit)
    (h : Imperative.Cmd.typeCheck C Env cmd = .ok (cmd', Env'))
    (h_wf : TEnvWF (T := CoreLParams) Env)
    (h_fwf : FactoryWF C.functions)
    (h_ne : Env.context.types ≠ [])
    (h_mono : ContextMono Env.context)
    -- Step-local well-kindedness inputs (replace the false global `RangeWellKinded S`): the
    -- CURRENT subst is range-WK against `C`, and `C` registers the base type arities. Consumed
    -- only by the `init` case's `WellKindedTy` obligation (see `init_(non)det_WellKindedTy`).
    (h_base_ty : BaseTypesWK C)
    (h_wk_in : Subst.RangeWellKinded (fun n => C.knownTypes[n]?) Env.stateSubstInfo.subst) :
    ∀ S, Subst.absorbs S Env'.stateSubstInfo.subst → SubstWF S →
      (∀ v, v ∈ C.rigidTypeVars → LMonoTy.subst S (.ftvar v) = .ftvar v) →
      CmdHasType C (TContext.subst Env.context S) cmd
        (TContext.subst Env'.context S) := by
  intro S hS_abs hS_wf hS_rigid
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
      -- `Env'.subst = (update v3.snd x v3.fst).subst = v3.snd.subst = Env_unified.subst`.
      have h_env'_subst : (CmdType.update v3.snd x v3.fst).stateSubstInfo.subst =
          Env_unified.stateSubstInfo.subst := by
        rw [CmdType.update_preserves_subst, h_v3_eq]
      have hS_abs_unified : Subst.absorbs S Env_unified.stateSubstInfo.subst :=
        h_env'_subst ▸ hS_abs
      have h_find_none_subst := Lambda.TContext.subst_find_none Env.context S x h_find_none
      have h_fresh_v3 : v3.snd.context.types.find? x = none := by
        rw [h_ctx_eq.find? x]; exact h_find_none
      have h_ne_v3 : v3.snd.context.types ≠ [] := h_ctx_eq.symm.types_ne_nil h_ne
      have h_update_ctx := CmdType.update_subst_context v3.snd x v3.fst S h_ne_v3 h_fresh_v3
      -- The stored type at `S` collapses to `forAll [] (subst S mty_pre)`.
      have h_pr := CmdType.postprocess_result C Env_unified v3.snd mty_pre v3.fst
        (h_mty_pre ▸ h_postprocess)
      have h_stored : LTy.subst S v3.fst = .forAll [] (LMonoTy.subst S mty_pre) := by
        rw [h_pr.1, LTy.subst_forAll_nil,
          LMonoTy.subst_absorbs S Env_unified.stateSubstInfo.subst mty_pre hS_abs_unified]
      have h_not_in_vars : x ∉ HasVarsPure.getVars (P := Expression) heq_det :=
        fun h => h_not_in_fv ((CmdType.freeVars_eq_getVars heq_det x).mpr h)
      have h_hastype : HasType (T := CoreLParams) C
          (Env.context.subst S)
          heq_det (.forAll [] (LMonoTy.subst S mty_pre)) :=
        init_det_expr_HasType C Env v1.snd v2.2.snd Env_unified x heq_det
          v2.1 xty v1.fst v2.2.fst mty_pre md S h_preprocess h_mty_pre
          h_infer h_unify h_wf h_fwf h_mono hS_abs_unified hS_wf
      have h_pp : CmdType.preprocess C Env xty = .ok (.forAll [] mty_pre, v1.snd) := by
        rw [h_preprocess, ← h_mty_pre]
      have h_preprocess_subst := CmdType.preprocess_preserves_stateSubstInfo C Env xty v1.fst v1.snd h_preprocess
      have h_infer_absorbs := CmdType.inferType_absorbs C v1.snd v2.2.snd
        (.init x xty (.det heq_det) md) heq_det v2.1 v2.2.fst h_infer h_wf_pre h_fwf
      have h_unify_absorbs := CmdType.unifyTypes_absorbs v2.2.snd Env_unified _ h_unify
      have h_absorbs_unified : Subst.absorbs Env_unified.stateSubstInfo.subst
          Env.stateSubstInfo.subst :=
        Subst.absorbs_trans _ _ _
          (h_preprocess_subst ▸ h_infer_absorbs) h_unify_absorbs
      have hS_abs_env : Subst.absorbs S Env.stateSubstInfo.subst :=
        Subst.absorbs_trans _ _ _ h_absorbs_unified hS_abs_unified
      obtain ⟨tys, h_tys_len, h_rac⟩ := CmdType.preprocess_isInstance_rigidAnnotCompat C Env v1.snd
        S xty mty_pre h_pp h_wf hS_rigid hS_abs_env
      rw [← TContext.subst_aliases Env.context S] at h_rac
      -- Output-context Equiv: subst-of-update ≈ insert into (v3.snd.context.subst S)
      -- ≈ insert into (Env.context.subst S), with the stored type at `subst S mty_pre`.
      have h_out_equiv : TContext.Equiv (T := CoreLParams)
          ((CmdType.update v3.snd x v3.fst).context.subst S)
          { Env.context.subst S with
            types := (Env.context.subst S).types.insert x (.forAll [] (LMonoTy.subst S mty_pre)) } := by
        refine h_update_ctx.trans ?_
        rw [h_stored]
        exact TContext.Equiv.insert (h_ctx_eq.subst S) x (.forAll [] (LMonoTy.subst S mty_pre))
      have h_wk_stored : C.WellKindedTy (LMonoTy.subst S mty_pre) :=
        CmdType.init_det_WellKindedTy C Env S x xty heq_det md v1 mty_pre v2 Env_unified h_pp
          h_infer (h_mty_pre ▸ h_unify) v3 (h_mty_pre ▸ h_postprocess)
          h_wf h_fwf h_base_ty h_wk_in hS_rigid hS_abs_unified
      exact CmdHasType'.init_det _ x xty heq_det _ tys md _
        h_find_none_subst h_not_in_vars h_tys_len h_rac h_wk_stored h_hastype h_out_equiv
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
      obtain ⟨h_ctx_eq, _h_find_none_subst_old, mty, h_mty⟩ :=
        init_nondet_context_setup C Env x xty v1 v2 h_preprocess h_postprocess h_find_none
      have h_find_none_subst := Lambda.TContext.subst_find_none Env.context S x h_find_none
      have h_fresh_v2 : v2.snd.context.types.find? x = none :=
        h_ctx_eq ▸ h_find_none
      have h_ne_v2 : v2.snd.context.types ≠ [] := h_ctx_eq ▸ h_ne
      have h_update_ctx := CmdType.update_subst_context v2.snd x v2.fst S h_ne_v2 h_fresh_v2
      obtain ⟨mty_pre, h_mty_pre⟩ := CmdType.preprocess_mono C Env xty v1.fst v1.snd h_preprocess
      have h_pr := CmdType.postprocess_result C v1.snd v2.snd mty_pre v2.fst
        (h_mty_pre ▸ h_postprocess)
      have h_pp : CmdType.preprocess C Env xty = .ok (.forAll [] mty_pre, v1.snd) := by
        rw [h_preprocess, ← h_mty_pre]
      -- v2.snd = v1.snd (postprocess preserves), so v2.snd.subst = Env.subst.
      have h_v2_subst : v2.snd.stateSubstInfo = Env.stateSubstInfo := by
        rw [h_pr.2]
        exact CmdType.preprocess_preserves_stateSubstInfo C Env xty v1.fst v1.snd h_preprocess
      -- `Env'.subst = (update v2.snd x v2.fst).subst = v2.snd.subst = Env.subst`.
      have h_env'_subst : (CmdType.update v2.snd x v2.fst).stateSubstInfo.subst =
          Env.stateSubstInfo.subst := by
        rw [CmdType.update_preserves_subst, congrArg (·.subst) h_v2_subst]
      have hS_abs_env : Subst.absorbs S Env.stateSubstInfo.subst :=
        h_env'_subst ▸ hS_abs
      have h_v1_subst : v1.snd.stateSubstInfo.subst = Env.stateSubstInfo.subst :=
        congrArg (·.subst) (CmdType.preprocess_preserves_stateSubstInfo C Env xty v1.fst v1.snd h_preprocess)
      -- The stored type at `S` collapses to `forAll [] (subst S mty_pre)`.
      have h_stored : LTy.subst S v2.fst = .forAll [] (LMonoTy.subst S mty_pre) := by
        rw [h_pr.1, LTy.subst_forAll_nil, h_v1_subst,
          LMonoTy.subst_absorbs S Env.stateSubstInfo.subst mty_pre hS_abs_env]
      obtain ⟨tys, h_tys_len, h_rac0⟩ :=
        CmdType.preprocess_isInstance_rigidAnnotCompat C Env v1.snd
          S xty mty_pre h_pp h_wf hS_rigid hS_abs_env
      rw [← TContext.subst_aliases Env.context S] at h_rac0
      have h_out_equiv : TContext.Equiv (T := CoreLParams)
          ((CmdType.update v2.snd x v2.fst).context.subst S)
          { Env.context.subst S with
            types := (Env.context.subst S).types.insert x (.forAll [] (LMonoTy.subst S mty_pre)) } := by
        refine h_update_ctx.trans ?_
        rw [h_stored]
        exact TContext.Equiv.insert ((TContext.Equiv.of_eq (T := CoreLParams) h_ctx_eq).subst S) x
          (.forAll [] (LMonoTy.subst S mty_pre))
      have h_wk_stored : C.WellKindedTy (LMonoTy.subst S mty_pre) :=
        CmdType.init_nondet_WellKindedTy C Env S xty v1 mty_pre v2 h_pp
          (h_mty_pre ▸ h_postprocess) h_wk_in hS_rigid hS_abs_env
      exact CmdHasType'.init_nondet _ x xty (LMonoTy.subst S mty_pre) tys md _
        h_find_none_subst h_tys_len h_rac0 h_wk_stored h_out_equiv
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
      have h_find_subst := Lambda.TContext.subst_find_some Env.context S x xty h_find
      have h_xty_bv := h_mono x xty h_find
      obtain ⟨xs, mty_x⟩ := xty
      simp [LTy.boundVars] at h_xty_bv
      subst h_xty_bv
      have h_hastype := set_det_HasType C Env Env_infer Env' x expr e'
        (.forAll [] mty_x) ety mty_x S rfl heq h_unify h_wf h_fwf h_mono hS_abs hS_wf
      have h_ctx_infer : TContext.Equiv (T := CoreLParams) Env_infer.context Env.context :=
        CmdType.inferType_preserves_context C Env Env_infer
          (.set x (.det expr) md) expr e' ety heq h_wf h_ne h_fwf
      have h_ctx_unify := CmdType.unifyTypes_preserves_context Env_infer Env'
        [(.forAll [] mty_x, ety)] h_unify
      have h_ctx : TContext.Equiv (T := CoreLParams) Env'.context Env.context := by
        rw [h_ctx_unify]; exact h_ctx_infer
      rw [LTy.subst_forAll_nil] at h_find_subst h_hastype
      exact CmdHasType'.set_det _ x (LMonoTy.subst S mty_x) expr md _
        h_find_subst h_hastype (h_ctx.subst S)
    | nondet =>
      simp at h
      cases h
      obtain ⟨mty, h_find_subst⟩ := set_nondet_sound Env x xty S h_lookup h_mono
      exact CmdHasType'.set_nondet _ x mty md _ h_find_subst (TContext.Equiv.refl _)
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
      (.assert label e md) e e' ety S heq h_bool h_wf h_fwf h_ne h_mono hS_abs hS_wf
    exact CmdHasType'.assert _ label e md _ h_ht (h_ctx.subst S)
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
      (.assume label e md) e e' ety S heq h_bool h_wf h_fwf h_ne h_mono hS_abs hS_wf
    exact CmdHasType'.assume _ label e md _ h_ht (h_ctx.subst S)
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
      (.cover label e md) e e' ety S heq h_bool h_wf h_fwf h_ne h_mono hS_abs hS_wf
    exact CmdHasType'.cover _ label e md _ h_ht (h_ctx.subst S)

/--
Soundness of the command typechecker (fixed final-substitution corollary): if
`Cmd.typeCheck` succeeds, then `CmdHasType` holds between the substituted
input/output contexts, grounding type variables at `Env'.stateSubstInfo.subst`.
The `S := Env'.stateSubstInfo.subst` instance of `Cmd.typeCheck_sound_gen`.
-/
theorem Cmd.typeCheck_sound (C : LContext CoreLParams) (Env : TEnv Unit)
    (cmd cmd' : Cmd Expression) (Env' : TEnv Unit)
    (h : Imperative.Cmd.typeCheck C Env cmd = .ok (cmd', Env'))
    (h_wf : TEnvWF (T := CoreLParams) Env)
    (h_fwf : FactoryWF C.functions)
    (h_ne : Env.context.types ≠ [])
    (h_mono : ContextMono Env.context)
    (h_base : BaseTypesWK C)
    (h_wk : Subst.RangeWellKinded (fun n => C.knownTypes[n]?) Env.stateSubstInfo.subst)
    (h_rigid_inv : ∀ v, v ∈ C.rigidTypeVars →
      LMonoTy.subst Env.stateSubstInfo.subst (.ftvar v) = .ftvar v) :
    CmdHasType C (TContext.subst Env.context Env'.stateSubstInfo.subst) cmd
      (TContext.subst Env'.context Env'.stateSubstInfo.subst) := by
  have h_rigid' : ∀ v, v ∈ C.rigidTypeVars →
      LMonoTy.subst Env'.stateSubstInfo.subst (.ftvar v) = .ftvar v :=
    Core.Cmd.typeCheck_preserves_rigid_inv C Env cmd cmd' Env' h h_rigid_inv
  exact Cmd.typeCheck_sound_gen C Env cmd cmd' Env' h h_wf h_fwf h_ne h_mono h_base h_wk
    Env'.stateSubstInfo.subst (Subst.absorbs_refl _ Env'.stateSubstInfo.isWF)
    Env'.stateSubstInfo.isWF h_rigid'

/-- **Whole-`Cmd.typeCheck` threading preservation.** A successful `Cmd.typeCheck`
    step preserves the environment well-formedness invariants threaded by the
    statement-level `go` induction, and refines the running substitution:

    * `TEnvWF Env'` — the output environment is still well-formed;
    * `Env'.context.types ≠ []` — the type-scope stays non-empty;
    * `ContextMono Env'.context` — context types stay monomorphic;
    * `Subst.absorbs Env'.subst Env.subst` — the substitution only grows.

    Rigid-identity preservation is separate (`Cmd.typeCheck_preserves_rigid_inv`).
    The `LContext` `C` is unchanged by commands, so it is not mentioned. -/
theorem Cmd.typeCheck_preserves (C : LContext CoreLParams) (Env : TEnv Unit)
    (cmd cmd' : Cmd Expression) (Env' : TEnv Unit)
    (h : Imperative.Cmd.typeCheck C Env cmd = .ok (cmd', Env'))
    (h_wf : TEnvWF (T := CoreLParams) Env)
    (h_fwf : FactoryWF C.functions)
    (h_ne : Env.context.types ≠ [])
    (h_mono : ContextMono Env.context) :
    TEnvWF (T := CoreLParams) Env' ∧
    Env'.context.types ≠ [] ∧
    ContextMono Env'.context ∧
    Subst.absorbs Env'.stateSubstInfo.subst Env.stateSubstInfo.subst := by
  cases cmd with
  | init x xty e md =>
    simp only [Cmd.typeCheck, Bind.bind, Except.bind] at h
    elim_err h; rename_i h_lookup
    split at h
    · -- det: preprocess → inferType → unifyTypes → checkAnnotCompat → postprocess → update
      rename_i expr _
      elim_err h; rename_i h_not_in_fv
      elim_err h; rename_i v1 h_preprocess
      elim_err h; rename_i v2 h_infer
      elim_err h; rename_i Env_unified h_unify
      elim_err h; rename_i _u h_check
      elim_err h; rename_i v3 h_postprocess; cases h
      simp only [TypeContext.update, TypeContext.lookup, TypeContext.preprocess,
        TypeContext.postprocess, TypeContext.inferType, TypeContext.unifyTypes,
        TypeContext.freeVars, TypeContext.checkAnnotCompat] at *
      obtain ⟨v1ty, Env_pre⟩ := v1
      obtain ⟨e', ety, Env_infer⟩ := v2
      -- preprocess output type is `forAll [] mty_pre`.
      obtain ⟨mty_pre, h_mty_pre⟩ := CmdType.preprocess_mono C Env xty v1ty Env_pre h_preprocess
      subst h_mty_pre
      -- WF chain: Env →pre Env_pre →infer Env_infer →unify Env_unified →update Env'.
      have h_wf_pre : TEnvWF (T := CoreLParams) Env_pre :=
        CmdType.preprocess_preserves_TEnvWF C Env xty _ Env_pre h_preprocess h_wf
      -- inferType output type is `forAll [] mty_inf`, fresh at Env_infer.
      obtain ⟨mty_inf, h_ety_eq, h_inf_fresh⟩ :=
        CmdType.inferType_output_fresh C Env_pre Env_infer _ _ e' ety h_infer h_wf_pre h_fwf
      subst h_ety_eq
      have h_wf_infer : TEnvWF (T := CoreLParams) Env_infer :=
        CmdType.inferType_TEnvWF C Env_pre Env_infer _ _ e' (.forAll [] mty_inf) h_infer h_wf_pre h_fwf
      -- preprocess output type fresh at Env_pre, lifted to Env_infer.
      have h_pre_fresh : ∀ v, v ∈ LMonoTy.freeVars mty_pre →
          ∀ n, n ≥ Env_pre.genEnv.genState.tyGen → v ≠ TState.tyPrefix ++ toString n :=
        CmdType.preprocess_output_fresh C Env xty mty_pre Env_pre h_preprocess h_wf
      have h_infer_mono : Env_infer.genEnv.genState.tyGen ≥ Env_pre.genEnv.genState.tyGen :=
        CmdType.inferType_genState_mono C Env_pre Env_infer _ _ e' (.forAll [] mty_inf) h_infer h_wf_pre h_fwf
      have h_pre_fresh' : ∀ v, v ∈ LMonoTy.freeVars mty_pre →
          ∀ n, n ≥ Env_infer.genEnv.genState.tyGen → v ≠ TState.tyPrefix ++ toString n :=
        fun v hv n hn => h_pre_fresh v hv n (Nat.le_trans h_infer_mono hn)
      have h_wf_unified : TEnvWF (T := CoreLParams) Env_unified :=
        CmdType.unifyTypes_TEnvWF Env_infer Env_unified mty_pre mty_inf h_unify h_wf_infer
          h_pre_fresh' h_inf_fresh
      -- postprocess output type is `forAll [] (subst Env_unified.subst mty_pre)`, env unchanged.
      obtain ⟨v3fst, v3snd⟩ := v3
      obtain ⟨h_v3_fst, h_v3_snd⟩ := CmdType.postprocess_result C Env_unified v3snd mty_pre v3fst
        (by rw [h_postprocess])
      -- `v3snd = Env_unified` and `v3fst = forAll [] (subst Env_unified.subst mty_pre)`.
      rw [h_v3_snd, h_v3_fst]
      -- Env' = update Env_unified x (forAll [] (subst Env_unified.subst mty_pre)).
      have h_ctx_unify : Env_unified.context = Env_infer.context :=
        CmdType.unifyTypes_preserves_context Env_infer Env_unified _ h_unify
      have h_ctx_pre : Env_pre.context = Env.context :=
        CmdType.preprocess_preserves_context C Env xty _ Env_pre h_preprocess
      have h_ne_pre : Env_pre.context.types ≠ [] := h_ctx_pre ▸ h_ne
      have h_ctx_infer : TContext.Equiv (T := CoreLParams) Env_infer.context Env_pre.context :=
        CmdType.inferType_preserves_context C Env_pre Env_infer _ _ e' (.forAll [] mty_inf)
          h_infer h_wf_pre h_ne_pre h_fwf
      -- update step. The stored type's freeVars are gen-fresh at Env_unified.
      have h_unify_mono : Env_unified.genEnv.genState.tyGen ≥ Env_infer.genEnv.genState.tyGen := by
        rw [CmdType.unifyTypes_preserves_genState Env_infer Env_unified _ h_unify]
        exact Nat.le_refl _
      have h_stored_fresh : ∀ v, v ∈ LMonoTy.freeVars
          (LMonoTy.subst Env_unified.stateSubstInfo.subst mty_pre) →
          ∀ n, n ≥ Env_unified.genEnv.genState.tyGen → v ≠ TState.tyPrefix ++ toString n :=
        Lambda.LExpr.freeVars_subst_genFresh Env_unified.stateSubstInfo mty_pre
          Env_unified.genEnv.genState h_wf_unified.substFreshForGen
          (fun v hv n hn => h_pre_fresh' v hv n (Nat.le_trans h_unify_mono hn))
      refine ⟨CmdType.update_TEnvWF Env_unified x _ h_wf_unified h_stored_fresh,
        CmdType.update_types_ne Env_unified x _, ?_, ?_⟩
      · exact CmdType.update_ContextMono Env_unified x _
          (h_ctx_unify ▸ ContextMono.of_equiv h_ctx_infer.symm (h_ctx_pre ▸ h_mono))
      · -- absorbs: subst chain Env →pre Env_infer →unify Env_unified →(update preserves)→ Env'.
        rw [CmdType.update_preserves_subst]
        have h_pre_subst : Env_pre.stateSubstInfo.subst = Env.stateSubstInfo.subst :=
          congrArg (·.subst) (CmdType.preprocess_preserves_stateSubstInfo C Env xty _ Env_pre h_preprocess)
        have h_infer_abs := CmdType.inferType_absorbs C Env_pre Env_infer _ _ e'
          (.forAll [] mty_inf) h_infer h_wf_pre h_fwf
        have h_unify_abs := CmdType.unifyTypes_absorbs Env_infer Env_unified _ h_unify
        exact Subst.absorbs_trans _ _ _
          (h_pre_subst ▸ h_infer_abs) h_unify_abs
    · -- nondet: preprocess → postprocess → update
      rename_i _
      elim_err h; rename_i v1 h_preprocess
      elim_err h; rename_i v2 h_postprocess; cases h
      simp only [TypeContext.update, TypeContext.preprocess, TypeContext.postprocess] at *
      obtain ⟨v1ty, Env_pre⟩ := v1
      obtain ⟨mty_pre, h_mty_pre⟩ := CmdType.preprocess_mono C Env xty v1ty Env_pre h_preprocess
      subst h_mty_pre
      have h_wf_pre : TEnvWF (T := CoreLParams) Env_pre :=
        CmdType.preprocess_preserves_TEnvWF C Env xty _ Env_pre h_preprocess h_wf
      have h_pre_fresh : ∀ v, v ∈ LMonoTy.freeVars mty_pre →
          ∀ n, n ≥ Env_pre.genEnv.genState.tyGen → v ≠ TState.tyPrefix ++ toString n :=
        CmdType.preprocess_output_fresh C Env xty mty_pre Env_pre h_preprocess h_wf
      obtain ⟨v2fst, v2snd⟩ := v2
      obtain ⟨h_v2_fst, h_v2_snd⟩ := CmdType.postprocess_result C Env_pre v2snd mty_pre v2fst
        (by rw [h_postprocess])
      rw [h_v2_snd, h_v2_fst]
      have h_ctx_pre : Env_pre.context = Env.context :=
        CmdType.preprocess_preserves_context C Env xty _ Env_pre h_preprocess
      have h_stored_fresh : ∀ v, v ∈ LMonoTy.freeVars
          (LMonoTy.subst Env_pre.stateSubstInfo.subst mty_pre) →
          ∀ n, n ≥ Env_pre.genEnv.genState.tyGen → v ≠ TState.tyPrefix ++ toString n :=
        Lambda.LExpr.freeVars_subst_genFresh Env_pre.stateSubstInfo mty_pre
          Env_pre.genEnv.genState h_wf_pre.substFreshForGen h_pre_fresh
      refine ⟨CmdType.update_TEnvWF Env_pre x _ h_wf_pre h_stored_fresh,
        CmdType.update_types_ne Env_pre x _, ?_, ?_⟩
      · exact CmdType.update_ContextMono Env_pre x _ (h_ctx_pre ▸ h_mono)
      · rw [CmdType.update_preserves_subst]
        have h_pre_subst : Env_pre.stateSubstInfo.subst = Env.stateSubstInfo.subst :=
          congrArg (·.subst) (CmdType.preprocess_preserves_stateSubstInfo C Env xty _ Env_pre h_preprocess)
        rw [h_pre_subst]; exact Subst.absorbs_refl _ Env.stateSubstInfo.isWF
  | set x e md =>
    simp only [Cmd.typeCheck, Bind.bind, Except.bind] at h
    elim_err h; rename_i xty h_lookup
    cases e with
    | det expr =>
      simp only [] at h
      elim_err h; rename_i v h_infer
      elim_err h; rename_i Env_unified h_unify
      elim_err h; rename_i _u h_check; cases h
      simp only [TypeContext.lookup, TypeContext.inferType, TypeContext.unifyTypes,
        TypeContext.checkAnnotCompat] at *
      obtain ⟨e', ety, Env_infer⟩ := v
      have h_find := (CmdType.lookup_some_iff_find_some Env x xty).mp h_lookup
      -- The context type `xty` is monomorphic (ContextMono) and gen-fresh (ctxFreshForGen).
      have h_xty_bv : LTy.boundVars xty = [] := h_mono x xty h_find
      obtain ⟨xs, mty_x⟩ := xty
      simp only [LTy.boundVars] at h_xty_bv; subst h_xty_bv
      -- inferType output type is `forAll [] mty_inf`, fresh at Env_infer.
      obtain ⟨mty_inf, h_ety_eq, h_inf_fresh⟩ :=
        CmdType.inferType_output_fresh C Env Env_infer (.set x (.det expr) md) expr e' ety
          h_infer h_wf h_fwf
      subst h_ety_eq
      have h_wf_infer : TEnvWF (T := CoreLParams) Env_infer :=
        CmdType.inferType_TEnvWF C Env Env_infer _ expr e' (.forAll [] mty_inf) h_infer h_wf h_fwf
      have h_ctx_infer : TContext.Equiv (T := CoreLParams) Env_infer.context Env.context :=
        CmdType.inferType_preserves_context C Env Env_infer _ expr e' (.forAll [] mty_inf)
          h_infer h_wf h_ne h_fwf
      -- The context type's freeVars are gen-fresh at Env (ctxFreshForGen), lifted to Env_infer.
      have h_xty_fresh : ∀ v, v ∈ LMonoTy.freeVars mty_x →
          ∀ n, n ≥ Env.genEnv.genState.tyGen → v ≠ TState.tyPrefix ++ toString n := by
        intro v hv n hn
        refine h_wf.ctxFreshForGen v ?_ n hn
        refine TContext.mem_knownTypeVars_of_find h_find ?_
        have h_fv : LTy.freeVars (.forAll [] mty_x) = LMonoTy.freeVars mty_x := by
          simp [LTy.freeVars, List.removeAll, List.filter_eq_self]
        rw [h_fv]; exact hv
      have h_infer_mono : Env_infer.genEnv.genState.tyGen ≥ Env.genEnv.genState.tyGen :=
        CmdType.inferType_genState_mono C Env Env_infer _ expr e' (.forAll [] mty_inf) h_infer h_wf h_fwf
      have h_xty_fresh' : ∀ v, v ∈ LMonoTy.freeVars mty_x →
          ∀ n, n ≥ Env_infer.genEnv.genState.tyGen → v ≠ TState.tyPrefix ++ toString n :=
        fun v hv n hn => h_xty_fresh v hv n (Nat.le_trans h_infer_mono hn)
      have h_wf_unified : TEnvWF (T := CoreLParams) Env' :=
        CmdType.unifyTypes_TEnvWF Env_infer Env' mty_x mty_inf h_unify h_wf_infer
          h_xty_fresh' h_inf_fresh
      have h_ctx_unify : Env'.context = Env_infer.context :=
        CmdType.unifyTypes_preserves_context Env_infer Env' _ h_unify
      have h_ctx' : TContext.Equiv (T := CoreLParams) Env'.context Env.context := by
        rw [h_ctx_unify]; exact h_ctx_infer
      refine ⟨h_wf_unified, ?_, ?_, ?_⟩
      · exact h_ctx'.symm.types_ne_nil h_ne
      · exact ContextMono.of_equiv h_ctx'.symm h_mono
      · have h_infer_abs := CmdType.inferType_absorbs C Env Env_infer _ expr e'
          (.forAll [] mty_inf) h_infer h_wf h_fwf
        have h_unify_abs := CmdType.unifyTypes_absorbs Env_infer Env' _ h_unify
        exact Subst.absorbs_trans _ _ _ h_infer_abs h_unify_abs
    | nondet =>
      simp at h; cases h
      exact ⟨h_wf, h_ne, h_mono, Subst.absorbs_refl _ Env.stateSubstInfo.isWF⟩
  | assert label e md =>
    simp only [Cmd.typeCheck, Bind.bind, Except.bind] at h
    elim_err h; rename_i v h_infer
    elim_err h; rename_i _u h_check
    elim_err h; cases h
    obtain ⟨e', ety, Env_infer⟩ := v
    refine ⟨CmdType.inferType_TEnvWF C Env Env_infer _ e e' ety h_infer h_wf h_fwf, ?_, ?_, ?_⟩
    · exact (CmdType.inferType_preserves_context C Env Env_infer _ e e' ety h_infer h_wf h_ne h_fwf).symm.types_ne_nil h_ne
    · exact ContextMono.of_equiv (CmdType.inferType_preserves_context C Env Env_infer _ e e' ety h_infer h_wf h_ne h_fwf).symm h_mono
    · exact CmdType.inferType_absorbs C Env Env_infer _ e e' ety h_infer h_wf h_fwf
  | assume label e md =>
    simp only [Cmd.typeCheck, Bind.bind, Except.bind] at h
    elim_err h; rename_i v h_infer
    elim_err h; rename_i _u h_check
    elim_err h; cases h
    obtain ⟨e', ety, Env_infer⟩ := v
    refine ⟨CmdType.inferType_TEnvWF C Env Env_infer _ e e' ety h_infer h_wf h_fwf, ?_, ?_, ?_⟩
    · exact (CmdType.inferType_preserves_context C Env Env_infer _ e e' ety h_infer h_wf h_ne h_fwf).symm.types_ne_nil h_ne
    · exact ContextMono.of_equiv (CmdType.inferType_preserves_context C Env Env_infer _ e e' ety h_infer h_wf h_ne h_fwf).symm h_mono
    · exact CmdType.inferType_absorbs C Env Env_infer _ e e' ety h_infer h_wf h_fwf
  | cover label e md =>
    simp only [Cmd.typeCheck, Bind.bind, Except.bind] at h
    elim_err h; rename_i v h_infer
    elim_err h; rename_i _u h_check
    elim_err h; cases h
    obtain ⟨e', ety, Env_infer⟩ := v
    refine ⟨CmdType.inferType_TEnvWF C Env Env_infer _ e e' ety h_infer h_wf h_fwf, ?_, ?_, ?_⟩
    · exact (CmdType.inferType_preserves_context C Env Env_infer _ e e' ety h_infer h_wf h_ne h_fwf).symm.types_ne_nil h_ne
    · exact ContextMono.of_equiv (CmdType.inferType_preserves_context C Env Env_infer _ e e' ety h_infer h_wf h_ne h_fwf).symm h_mono
    · exact CmdType.inferType_absorbs C Env Env_infer _ e e' ety h_infer h_wf h_fwf

/-- **Structural shape preservation** for `Imperative.Cmd.typeCheck`: a successful
    run preserves the *tail* of the `types` stack (`Strata.Util.HMaps.pop`), the alias list, and is
    gen-counter monotone (no well-scoping assumption). This is what lets
    `block`/`goBlock` recover the input context after `popContext`. -/
theorem Cmd.typeCheck_preserves_shape (C : LContext CoreLParams) (Env : TEnv Unit)
    (cmd cmd' : Cmd Expression) (Env' : TEnv Unit)
    (h : Imperative.Cmd.typeCheck C Env cmd = .ok (cmd', Env'))
    (h_wf : TEnvWF (T := CoreLParams) Env)
    (h_fwf : FactoryWF C.functions)
    (h_ne : Env.context.types ≠ []) :
    Strata.Util.HMaps.Equiv (Strata.Util.HMaps.pop Env'.context.types)
      (Strata.Util.HMaps.pop Env.context.types) ∧
    Env'.context.aliases = Env.context.aliases ∧
    Env'.genEnv.genState.tyGen ≥ Env.genEnv.genState.tyGen := by
  cases cmd with
  | init x xty e md =>
    simp only [Cmd.typeCheck, Bind.bind, Except.bind] at h
    elim_err h; rename_i h_lookup
    split at h
    · -- det: preprocess → inferType → unifyTypes → checkAnnotCompat → postprocess → update
      rename_i expr _
      elim_err h; rename_i h_not_in_fv
      elim_err h; rename_i v1 h_preprocess
      elim_err h; rename_i v2 h_infer
      elim_err h; rename_i Env_unified h_unify
      elim_err h; rename_i _u h_check
      elim_err h; rename_i v3 h_postprocess; cases h
      simp only [TypeContext.update, TypeContext.lookup, TypeContext.preprocess,
        TypeContext.postprocess, TypeContext.inferType, TypeContext.unifyTypes,
        TypeContext.freeVars, TypeContext.checkAnnotCompat] at *
      obtain ⟨v1ty, Env_pre⟩ := v1
      obtain ⟨e', ety, Env_infer⟩ := v2
      obtain ⟨v3fst, v3snd⟩ := v3
      -- `postprocess` leaves the env unchanged: `v3snd = Env_unified`.
      obtain ⟨mty_pre, h_mty_pre⟩ := CmdType.preprocess_mono C Env xty v1ty Env_pre h_preprocess
      subst h_mty_pre
      obtain ⟨_, h_v3_snd⟩ := CmdType.postprocess_result C Env_unified v3snd mty_pre v3fst
        (by rw [h_postprocess])
      rw [h_v3_snd]
      -- Context-equality chain Env →pre →infer →unify (all full-preservation steps).
      have h_wf_pre : TEnvWF (T := CoreLParams) Env_pre :=
        CmdType.preprocess_preserves_TEnvWF C Env xty _ Env_pre h_preprocess h_wf
      have h_ctx_pre : Env_pre.context = Env.context :=
        CmdType.preprocess_preserves_context C Env xty _ Env_pre h_preprocess
      have h_ne_pre : Env_pre.context.types ≠ [] := h_ctx_pre ▸ h_ne
      have h_ctx_infer : TContext.Equiv (T := CoreLParams) Env_infer.context Env_pre.context :=
        CmdType.inferType_preserves_context C Env_pre Env_infer _ _ e' ety
          h_infer h_wf_pre h_ne_pre h_fwf
      have h_ctx_unify : Env_unified.context = Env_infer.context :=
        CmdType.unifyTypes_preserves_context Env_infer Env_unified _ h_unify
      -- Env_unified.context ≈ Env.context (Eq through pre/unify, Equiv through infer).
      have h_ctx_chain : TContext.Equiv (T := CoreLParams) Env_unified.context Env.context := by
        rw [h_ctx_unify]; exact h_ctx_infer.trans (TContext.Equiv.of_eq h_ctx_pre)
      refine ⟨?_, ?_, ?_⟩
      · rw [CmdType.update_types_pop]; exact h_ctx_chain.1.pop
      · rw [CmdType.update_aliases]; exact h_ctx_chain.2
      · -- tyGen chain: pre-mono, infer-mono, unify-eq, update-eq.
        rw [CmdType.update_tyGen]
        have h_pre_mono := CmdType.preprocess_genState_mono C Env xty _ Env_pre h_preprocess
        have h_infer_mono := CmdType.inferType_genState_mono C Env_pre Env_infer _ _ e' ety
          h_infer h_wf_pre h_fwf
        have h_unify_eq := CmdType.unifyTypes_preserves_genState Env_infer Env_unified _ h_unify
        rw [h_unify_eq]
        exact Nat.le_trans h_pre_mono h_infer_mono
    · -- nondet: preprocess → postprocess(=id) → update
      rename_i _
      elim_err h; rename_i v1 h_preprocess
      elim_err h; rename_i v2 h_postprocess; cases h
      simp only [TypeContext.update, TypeContext.preprocess, TypeContext.postprocess] at *
      obtain ⟨v1ty, Env_pre⟩ := v1
      obtain ⟨v2fst, v2snd⟩ := v2
      obtain ⟨mty_pre, h_mty_pre⟩ := CmdType.preprocess_mono C Env xty v1ty Env_pre h_preprocess
      subst h_mty_pre
      obtain ⟨_, h_v2_snd⟩ := CmdType.postprocess_result C Env_pre v2snd mty_pre v2fst
        (by rw [h_postprocess])
      rw [h_v2_snd]
      have h_ctx_pre : Env_pre.context = Env.context :=
        CmdType.preprocess_preserves_context C Env xty _ Env_pre h_preprocess
      refine ⟨?_, ?_, ?_⟩
      · rw [CmdType.update_types_pop, h_ctx_pre]
      · rw [CmdType.update_aliases, h_ctx_pre]
      · rw [CmdType.update_tyGen]
        exact CmdType.preprocess_genState_mono C Env xty _ Env_pre h_preprocess
  | set x e md =>
    simp only [Cmd.typeCheck, Bind.bind, Except.bind] at h
    elim_err h; rename_i xty h_lookup
    cases e with
    | det expr =>
      simp only [] at h
      elim_err h; rename_i v h_infer
      elim_err h; rename_i Env_unified h_unify
      elim_err h; rename_i _u h_check; cases h
      simp only [TypeContext.lookup, TypeContext.inferType, TypeContext.unifyTypes,
        TypeContext.checkAnnotCompat] at *
      obtain ⟨e', ety, Env_infer⟩ := v
      -- `set` only re-types an existing var: context is preserved up to Equiv.
      have h_ctx_infer : TContext.Equiv (T := CoreLParams) Env_infer.context Env.context :=
        CmdType.inferType_preserves_context C Env _ _ expr e' ety h_infer h_wf h_ne h_fwf
      have h_ctx_unify : Env'.context = Env_infer.context :=
        CmdType.unifyTypes_preserves_context Env_infer Env' _ h_unify
      have h_ctx : TContext.Equiv (T := CoreLParams) Env'.context Env.context := by
        rw [h_ctx_unify]; exact h_ctx_infer
      refine ⟨h_ctx.1.pop, h_ctx.2, ?_⟩
      have h_infer_mono := CmdType.inferType_genState_mono C Env _ _ expr e' ety h_infer h_wf h_fwf
      rw [CmdType.unifyTypes_preserves_genState Env_infer Env' _ h_unify]
      exact h_infer_mono
    | nondet =>
      simp at h; cases h
      exact ⟨Strata.Util.HMaps.Equiv.refl _, rfl, Nat.le_refl _⟩
  | assert label e md =>
    simp only [Cmd.typeCheck, Bind.bind, Except.bind] at h
    elim_err h; rename_i v h_infer
    elim_err h; rename_i _u h_check
    elim_err h; cases h
    obtain ⟨e', ety, Env_infer⟩ := v
    have h_ctx := CmdType.inferType_preserves_context C Env Env_infer _ e e' ety h_infer h_wf h_ne h_fwf
    exact ⟨h_ctx.1.pop, h_ctx.2,
      CmdType.inferType_genState_mono C Env Env_infer _ e e' ety h_infer h_wf h_fwf⟩
  | assume label e md =>
    simp only [Cmd.typeCheck, Bind.bind, Except.bind] at h
    elim_err h; rename_i v h_infer
    elim_err h; rename_i _u h_check
    elim_err h; cases h
    obtain ⟨e', ety, Env_infer⟩ := v
    have h_ctx := CmdType.inferType_preserves_context C Env Env_infer _ e e' ety h_infer h_wf h_ne h_fwf
    exact ⟨h_ctx.1.pop, h_ctx.2,
      CmdType.inferType_genState_mono C Env Env_infer _ e e' ety h_infer h_wf h_fwf⟩
  | cover label e md =>
    simp only [Cmd.typeCheck, Bind.bind, Except.bind] at h
    elim_err h; rename_i v h_infer
    elim_err h; rename_i _u h_check
    elim_err h; cases h
    obtain ⟨e', ety, Env_infer⟩ := v
    have h_ctx := CmdType.inferType_preserves_context C Env Env_infer _ e e' ety h_infer h_wf h_ne h_fwf
    exact ⟨h_ctx.1.pop, h_ctx.2,
      CmdType.inferType_genState_mono C Env Env_infer _ e e' ety h_infer h_wf h_fwf⟩

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
    (c : Cmd Expression) (e e' : LExpr CoreLParams.mono) (ety : LTy) (S : Subst)
    (h_infer : CmdType.inferType C Env c e = .ok (e', ety, Env_out))
    (h_isbool : CmdType.isBoolType ety = true)
    (h_wf : TEnvWF (T := CoreLParams) Env)
    (h_fwf : FactoryWF C.functions)
    (h_ne : Env.context.types ≠ [])
    (h_resolved : TContext.AliasesResolved Env.context) :
    LExpr.HasTypeA [] (e'.applySubst S) .bool ∧
    TContext.Equiv (T := CoreLParams) Env_out.context Env.context := by
  obtain ⟨mty, h_ety, h_hta⟩ := CmdType.inferType_HasTypeA C Env Env_out c e e' ety
    h_infer h_wf h_fwf h_resolved
  have h_bool_mty : mty = .bool := by
    have h_eq := CmdType.isBoolType_eq _ h_isbool
    rw [h_ety] at h_eq; cases h_eq; rfl
  subst h_bool_mty
  have h_ctx := CmdType.inferType_preserves_context C Env Env_out c e e' ety h_infer h_wf h_ne h_fwf
  have h_hta_subst := applySubst_typeCheck S h_hta
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
theorem Cmd.typeCheck_annotated_sound_gen (C : LContext CoreLParams) (Env : TEnv Unit)
    (cmd cmd' : Cmd Expression) (Env' : TEnv Unit)
    (h : Imperative.Cmd.typeCheck C Env cmd = .ok (cmd', Env'))
    (h_wf : TEnvWF (T := CoreLParams) Env)
    (h_fwf : FactoryWF C.functions)
    (h_ne : Env.context.types ≠ [])
    (h_mono : ContextMono Env.context)
    (h_resolved : TContext.AliasesResolved Env.context)
    -- Step-local well-kindedness inputs (replace the false global `RangeWellKinded S`): see
    -- `Cmd.typeCheck_sound_gen`. Consumed only by the `init` case.
    (h_base_ty : BaseTypesWK C)
    (h_wk_in : Subst.RangeWellKinded (fun n => C.knownTypes[n]?) Env.stateSubstInfo.subst) :
    ∀ S, Subst.absorbs S Env'.stateSubstInfo.subst → SubstWF S →
      (∀ v, v ∈ C.rigidTypeVars → LMonoTy.subst S (.ftvar v) = .ftvar v) →
      CmdHasTypeA C (TContext.subst Env.context S)
        (Core.Statement.Cmd.subst S cmd')
        (TContext.subst Env'.context S) := by
  intro S hS_abs hS_wf hS_rigid
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
      -- `Env'.subst = (update v3.snd x v3.fst).subst = v3.snd.subst = Env_unified.subst`.
      have h_env'_subst : (CmdType.update v3.snd x v3.fst).stateSubstInfo.subst =
          Env_unified.stateSubstInfo.subst := by
        rw [CmdType.update_preserves_subst, h_v3_eq]
      have hS_abs_unified : Subst.absorbs S Env_unified.stateSubstInfo.subst :=
        h_env'_subst ▸ hS_abs
      have h_fresh_v3 : v3.snd.context.types.find? x = none := by
        rw [h_ctx_eq.find? x]; exact h_find_none
      have h_ne_v3 : v3.snd.context.types ≠ [] := h_ctx_eq.symm.types_ne_nil h_ne
      have h_update_ctx := CmdType.update_subst_context v3.snd x v3.fst S h_ne_v3 h_fresh_v3
      have h_ctx_pre := CmdType.preprocess_preserves_context C Env xty v1.fst v1.snd h_preprocess
      have h_resolved_pre : TContext.AliasesResolved v1.snd.context :=
        h_ctx_pre ▸ h_resolved
      obtain ⟨mty_infer, h_ety_eq, h_hta⟩ := CmdType.inferType_HasTypeA C v1.snd v2.2.snd
        (Cmd.init x xty (.det heq_det) md) heq_det v2.1 v2.2.fst
        h_infer h_wf_pre h_fwf h_resolved_pre
      have h_hta_subst := applySubst_typeCheck S h_hta
      simp at h_hta_subst
      -- `subst S mty_infer = subst S mty_pre` via absorbs-collapse over Env_unified.subst.
      have h_unify_eq : LMonoTy.subst S mty_infer = LMonoTy.subst S mty_pre := by
        have h_base : LMonoTy.subst Env_unified.stateSubstInfo.subst mty_infer =
            LMonoTy.subst Env_unified.stateSubstInfo.subst mty_pre := by
          rw [h_mty_pre, h_ety_eq] at h_unify
          exact (CmdType.unifyTypes_eq v2.2.snd Env_unified mty_pre mty_infer h_unify).symm
        calc LMonoTy.subst S mty_infer
            = LMonoTy.subst S (LMonoTy.subst Env_unified.stateSubstInfo.subst mty_infer) :=
              (LMonoTy.subst_absorbs S _ mty_infer hS_abs_unified).symm
          _ = LMonoTy.subst S (LMonoTy.subst Env_unified.stateSubstInfo.subst mty_pre) := by rw [h_base]
          _ = LMonoTy.subst S mty_pre := LMonoTy.subst_absorbs S _ mty_pre hS_abs_unified
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
          (v2.1.applySubst S) := by
        simp only [HasVarsPure.getVars, Imperative.HasVarsPure.getVars]
        rw [applySubst_getVars_eq]
        simp only [HasVarsPure.getVars, Imperative.HasVarsPure.getVars] at h_not_in_vars
        rw [h_vars_eq]
        exact h_not_in_vars
      simp only [Core.Statement.Cmd.subst, Statement.substExprOrNondet, ExprOrNondet.map]
      have h_find_none_subst := Lambda.TContext.subst_find_none Env.context S x h_find_none
      -- The output command's declared type `v3.fst` collapses to `forAll [] (subst S mty_pre)`,
      -- so the instantiation is trivial (`tys = []`) and `AliasEquiv` is reflexive.
      have h_pr := CmdType.postprocess_result C Env_unified v3.snd mty_pre v3.fst
        (h_mty_pre ▸ h_postprocess)
      have h_stored : LTy.subst S v3.fst = .forAll [] (LMonoTy.subst S mty_pre) := by
        rw [h_pr.1, LTy.subst_forAll_nil,
          LMonoTy.subst_absorbs S Env_unified.stateSubstInfo.subst mty_pre hS_abs_unified]
      have h_open : LTy.openFull (LTy.forAll [] (LMonoTy.subst S mty_pre)) [] =
          LMonoTy.subst S mty_pre := Lambda.LExpr.openFull_nil_mono _
      have h_tyslen : ([] : List LMonoTy).length =
          (LTy.boundVars (LTy.forAll [] (LMonoTy.subst S mty_pre))).length := by
        simp [LTy.boundVars]
      have h_rac : RigidAnnotCompat (Env.context.subst S).aliases
          C.rigidTypeVars (LTy.openFull (LTy.forAll [] (LMonoTy.subst S mty_pre)) [])
          (LMonoTy.subst S mty_pre) := by
        rw [h_open]; exact .of_eq
      -- Output-context Equiv: subst-of-update ≈ insert into (Env.context.subst S).
      have h_out_equiv : TContext.Equiv (T := CoreLParams)
          ((CmdType.update v3.snd x v3.fst).context.subst S)
          { Env.context.subst S with
            types := (Env.context.subst S).types.insert x (.forAll [] (LMonoTy.subst S mty_pre)) } := by
        refine h_update_ctx.trans ?_
        rw [h_stored]
        exact TContext.Equiv.insert (h_ctx_eq.subst S) x (.forAll [] (LMonoTy.subst S mty_pre))
      rw [h_stored]
      have h_pp : CmdType.preprocess C Env xty = .ok (.forAll [] mty_pre, v1.snd) := by
        rw [h_preprocess, ← h_mty_pre]
      have hS_abs_env : Subst.absorbs S Env.stateSubstInfo.subst := by
        have h_pp_subst := CmdType.preprocess_preserves_stateSubstInfo C Env xty v1.fst v1.snd h_preprocess
        have h_infer_absorbs := CmdType.inferType_absorbs C v1.snd v2.2.snd
          (.init x xty (.det heq_det) md) heq_det v2.1 v2.2.fst h_infer h_wf_pre h_fwf
        have h_unify_absorbs := CmdType.unifyTypes_absorbs v2.2.snd Env_unified _ h_unify
        exact Subst.absorbs_trans _ _ _
          (Subst.absorbs_trans _ _ _ (h_pp_subst ▸ h_infer_absorbs) h_unify_absorbs) hS_abs_unified
      have h_wk_stored : C.WellKindedTy (LMonoTy.subst S mty_pre) :=
        CmdType.init_det_WellKindedTy C Env S x xty heq_det md v1 mty_pre v2 Env_unified h_pp
          h_infer (h_mty_pre ▸ h_unify) v3 (h_mty_pre ▸ h_postprocess)
          h_wf h_fwf h_base_ty h_wk_in hS_rigid hS_abs_unified
      exact CmdHasType'.init_det _ x (LTy.forAll [] (LMonoTy.subst S mty_pre))
        (v2.fst.applySubst S) _ [] md
        _ h_find_none_subst h_not_in_v2 h_tyslen h_rac h_wk_stored h_hta_subst h_out_equiv
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
      obtain ⟨h_ctx_eq, _h_find_none_subst_old, mty, h_mty⟩ :=
        init_nondet_context_setup C Env x xty v1 v2 h_preprocess h_postprocess h_find_none
      have h_fresh_v2 : v2.snd.context.types.find? x = none :=
        h_ctx_eq ▸ h_find_none
      have h_ne_v2 : v2.snd.context.types ≠ [] := h_ctx_eq ▸ h_ne
      have h_update_ctx := CmdType.update_subst_context v2.snd x v2.fst S h_ne_v2 h_fresh_v2
      simp only [Core.Statement.Cmd.subst, Statement.substExprOrNondet, ExprOrNondet.map]
      have h_find_none_subst := Lambda.TContext.subst_find_none Env.context S x h_find_none
      obtain ⟨mty_pre, h_mty_pre⟩ := CmdType.preprocess_mono C Env xty v1.fst v1.snd h_preprocess
      have h_pr := CmdType.postprocess_result C v1.snd v2.snd mty_pre v2.fst
        (h_mty_pre ▸ h_postprocess)
      have h_v1_subst : v1.snd.stateSubstInfo.subst = Env.stateSubstInfo.subst :=
        congrArg (·.subst) (CmdType.preprocess_preserves_stateSubstInfo C Env xty v1.fst v1.snd h_preprocess)
      -- `Env'.subst = (update v2.snd x v2.fst).subst = v2.snd.subst = v1.snd.subst = Env.subst`.
      have h_env'_subst : (CmdType.update v2.snd x v2.fst).stateSubstInfo.subst =
          Env.stateSubstInfo.subst := by
        rw [CmdType.update_preserves_subst, congrArg (·.stateSubstInfo.subst) h_pr.2, h_v1_subst]
      have hS_abs_env : Subst.absorbs S Env.stateSubstInfo.subst :=
        h_env'_subst ▸ hS_abs
      -- The output command's declared type `v2.fst` collapses to `forAll [] (subst S mty_pre)`.
      have h_stored : LTy.subst S v2.fst = .forAll [] (LMonoTy.subst S mty_pre) := by
        rw [h_pr.1, LTy.subst_forAll_nil, h_v1_subst,
          LMonoTy.subst_absorbs S Env.stateSubstInfo.subst mty_pre hS_abs_env]
      have h_open : LTy.openFull (LTy.forAll [] (LMonoTy.subst S mty_pre)) [] =
          LMonoTy.subst S mty_pre := Lambda.LExpr.openFull_nil_mono _
      have h_tyslen : ([] : List LMonoTy).length =
          (LTy.boundVars (LTy.forAll [] (LMonoTy.subst S mty_pre))).length := by
        simp [LTy.boundVars]
      have h_rac : RigidAnnotCompat (Env.context.subst S).aliases
          C.rigidTypeVars (LTy.openFull (LTy.forAll [] (LMonoTy.subst S mty_pre)) [])
          (LMonoTy.subst S mty_pre) := by
        rw [h_open]; exact .of_eq
      have h_out_equiv : TContext.Equiv (T := CoreLParams)
          ((CmdType.update v2.snd x v2.fst).context.subst S)
          { Env.context.subst S with
            types := (Env.context.subst S).types.insert x (.forAll [] (LMonoTy.subst S mty_pre)) } := by
        refine h_update_ctx.trans ?_
        rw [h_stored]
        exact TContext.Equiv.insert ((TContext.Equiv.of_eq (T := CoreLParams) h_ctx_eq).subst S) x
          (.forAll [] (LMonoTy.subst S mty_pre))
      rw [h_stored]
      have h_pp : CmdType.preprocess C Env xty = .ok (.forAll [] mty_pre, v1.snd) := by
        rw [h_preprocess, ← h_mty_pre]
      have h_wk_stored : C.WellKindedTy (LMonoTy.subst S mty_pre) :=
        CmdType.init_nondet_WellKindedTy C Env S xty v1 mty_pre v2 h_pp
          (h_mty_pre ▸ h_postprocess) h_wk_in hS_rigid hS_abs_env
      exact CmdHasType'.init_nondet _ x (LTy.forAll [] (LMonoTy.subst S mty_pre))
        (LMonoTy.subst S mty_pre) [] md _ h_find_none_subst h_tyslen h_rac h_wk_stored h_out_equiv
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
      have h_find_subst := Lambda.TContext.subst_find_some Env.context S x (.forAll [] mty_x) h_find
      rw [LTy.subst_forAll_nil] at h_find_subst
      obtain ⟨mty_infer, h_ety_eq, h_hta⟩ := CmdType.inferType_HasTypeA C Env _
        (.set x (.det expr) md) expr _ _ heq h_wf h_fwf h_resolved
      have h_ctx_infer : TContext.Equiv (T := CoreLParams) Env_infer.context Env.context :=
        CmdType.inferType_preserves_context C Env Env_infer
          (.set x (.det expr) md) expr e' ety heq h_wf h_ne h_fwf
      have h_ctx_unify := CmdType.unifyTypes_preserves_context Env_infer Env'
        [(.forAll [] mty_x, ety)] h_unify
      have h_ctx : TContext.Equiv (T := CoreLParams) Env'.context Env.context := by
        rw [h_ctx_unify]; exact h_ctx_infer
      have h_unify_eq : LMonoTy.subst S mty_infer = LMonoTy.subst S mty_x := by
        have h_base : LMonoTy.subst Env'.stateSubstInfo.subst mty_infer =
            LMonoTy.subst Env'.stateSubstInfo.subst mty_x := by
          rw [h_ety_eq] at h_unify
          exact (CmdType.unifyTypes_eq Env_infer Env' mty_x mty_infer h_unify).symm
        calc LMonoTy.subst S mty_infer
            = LMonoTy.subst S (LMonoTy.subst Env'.stateSubstInfo.subst mty_infer) :=
              (LMonoTy.subst_absorbs S _ mty_infer hS_abs).symm
          _ = LMonoTy.subst S (LMonoTy.subst Env'.stateSubstInfo.subst mty_x) := by rw [h_base]
          _ = LMonoTy.subst S mty_x := LMonoTy.subst_absorbs S _ mty_x hS_abs
      have h_hta_subst := applySubst_typeCheck S h_hta
      simp at h_hta_subst
      rw [h_unify_eq] at h_hta_subst
      simp only [Core.Statement.Cmd.subst]
      exact CmdHasType'.set_det _ x (LMonoTy.subst S mty_x) _ md _
        h_find_subst h_hta_subst (h_ctx.subst S)
    | nondet =>
      simp at h
      cases h
      obtain ⟨mty, h_find_subst⟩ := set_nondet_sound Env x xty S h_lookup h_mono
      exact CmdHasType'.set_nondet _ x mty md _ h_find_subst (TContext.Equiv.refl _)
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
      (.assert label e md) e e' ety S heq h_bool h_wf h_fwf h_ne h_resolved
    exact CmdHasType'.assert _ label _ md _ h_hta (h_ctx.subst S)
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
      (.assume label e md) e e' ety S heq h_bool h_wf h_fwf h_ne h_resolved
    exact CmdHasType'.assume _ label _ md _ h_hta (h_ctx.subst S)
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
      (.cover label e md) e e' ety S heq h_bool h_wf h_fwf h_ne h_resolved
    exact CmdHasType'.cover _ label _ md _ h_hta (h_ctx.subst S)

/--
Annotated soundness of the command typechecker (fixed final-substitution
corollary): if `Cmd.typeCheck` succeeds, the output command satisfies
`CmdHasTypeA` between the substituted contexts, grounding type variables at
`Env'.stateSubstInfo.subst`. The `S := Env'.stateSubstInfo.subst` instance of
`Cmd.typeCheck_annotated_sound_gen`.
-/
theorem Cmd.typeCheck_annotated_sound (C : LContext CoreLParams) (Env : TEnv Unit)
    (cmd cmd' : Cmd Expression) (Env' : TEnv Unit)
    (h : Imperative.Cmd.typeCheck C Env cmd = .ok (cmd', Env'))
    (h_wf : TEnvWF (T := CoreLParams) Env)
    (h_fwf : FactoryWF C.functions)
    (h_ne : Env.context.types ≠ [])
    (h_mono : ContextMono Env.context)
    (h_base : BaseTypesWK C)
    (h_wk : Subst.RangeWellKinded (fun n => C.knownTypes[n]?) Env.stateSubstInfo.subst)
    (h_rigid_inv : ∀ v, v ∈ C.rigidTypeVars →
      LMonoTy.subst Env.stateSubstInfo.subst (.ftvar v) = .ftvar v)
    (h_resolved : TContext.AliasesResolved Env.context) :
    CmdHasTypeA C (TContext.subst Env.context Env'.stateSubstInfo.subst)
      (Core.Statement.Cmd.subst Env'.stateSubstInfo.subst cmd')
      (TContext.subst Env'.context Env'.stateSubstInfo.subst) := by
  have h_rigid' : ∀ v, v ∈ C.rigidTypeVars →
      LMonoTy.subst Env'.stateSubstInfo.subst (.ftvar v) = .ftvar v :=
    Core.Cmd.typeCheck_preserves_rigid_inv C Env cmd cmd' Env' h h_rigid_inv
  exact Cmd.typeCheck_annotated_sound_gen C Env cmd cmd' Env' h h_wf h_fwf h_ne h_mono h_resolved
    h_base h_wk Env'.stateSubstInfo.subst (Subst.absorbs_refl _ Env'.stateSubstInfo.isWF)
    Env'.stateSubstInfo.isWF h_rigid'

end TypeSpec
end Core
