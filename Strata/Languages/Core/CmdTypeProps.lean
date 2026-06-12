/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Core.CmdType
import all Strata.Languages.Core.CmdType
import all Strata.DL.Lambda.LTy
import all Strata.DL.Lambda.LExprTypeEnv
import all Strata.DL.Lambda.LExprTypeSpec
import all Strata.DL.Lambda.LExprResolveProps
public import Strata.DL.Imperative.CmdType
import all Strata.DL.Imperative.CmdType
import Strata.Util.Tactics

/-! ## Soundness helper lemmas for the Core command typechecker

Properties of the `CmdType` typechecker definitions (`lookup`, `preprocess`,
`inferType`, `unifyTypes`, etc.), used to prove command-typechecker soundness in
`CmdTypeSpecProps`.
-/

namespace Core
open Lambda Imperative LExpr
open Std (ToFormat Format format)
open Strata (DiagnosticModel FileRange)

public section

namespace CmdType

/-- `CmdType.freeVars` agrees with `HasVarsPure.getVars` on membership. -/
theorem freeVars_eq_getVars (e : LExpr CoreLParams.mono) (x : CoreIdent) :
    x ∈ CmdType.freeVars e ↔ x ∈ HasVarsPure.getVars (P := Expression) e := by
  simp only [CmdType.freeVars, HasVarsPure.getVars, Imperative.HasVarsPure.getVars]
  have h_eq : (LExpr.freeVars e).map (fun (i, _) => i) = LExpr.getVars e :=
    LExpr.freeVars_map_fst_eq_getVars e
  rw [h_eq]

/-- `CmdType.lookup` returning `none` is equivalent to `find?` on the context. -/
theorem lookup_none_iff_find_none (Env : TEnv Unit) (x : CoreIdent) :
    CmdType.lookup Env x = none ↔ Env.context.types.find? x = none := by
  simp [CmdType.lookup]

/-- `CmdType.lookup` returning `some ty` is equivalent to `find?` on the context. -/
theorem lookup_some_iff_find_some (Env : TEnv Unit) (x : CoreIdent) (ty : LTy) :
    CmdType.lookup Env x = some ty ↔ Env.context.types.find? x = some ty := by
  simp [CmdType.lookup]

/-- `isBoolType` returning `true` implies the type is `forAll [] .bool`. -/
theorem isBoolType_eq (ty : LTy) :
    CmdType.isBoolType ty = true → ty = .forAll [] .bool := by
  unfold CmdType.isBoolType LMonoTy.bool
  intro h
  split at h <;> simp_all

/-- `CmdType.update` does not change the substitution state. -/
theorem update_preserves_subst (Env : TEnv Unit) (x : CoreIdent) (ty : LTy) :
    (CmdType.update Env x ty).stateSubstInfo = Env.stateSubstInfo := by
  simp [CmdType.update]
  exact TEnv.addInNewestContext_stateSubstInfo (T := CoreLParams) Env [(x, ty)]

/-- Substitution on the output context of `update` inserts the substituted type. -/
theorem update_subst_context (Env : TEnv Unit) (x : CoreIdent) (ty : LTy) (S : Subst)
    (h_fresh : Env.context.types.find? x = none) :
    TContext.subst (CmdType.update Env x ty).context S =
      { TContext.subst Env.context S with
        types := (TContext.subst Env.context S).types.insert x (LTy.subst S ty) } := by
  simp [CmdType.update]
  exact TEnv.addInNewestContext_singleton_subst_context (T := CoreLParams) Env x ty S h_fresh

/-- `preprocess` always produces a monomorphic type (`forAll [] mty`). -/
theorem preprocess_mono (C : LContext CoreLParams) (Env : TEnv Unit)
    (ty ty' : LTy) (Env' : TEnv Unit)
    (h : CmdType.preprocess C Env ty = .ok (ty', Env')) :
    ∃ mty, ty' = .forAll [] mty := by
  simp [CmdType.preprocess, Bind.bind, Except.bind, Except.mapError] at h
  elim_err h
  simp only [Except.ok.injEq, Prod.mk.injEq, pure, Except.pure] at h
  exact ⟨_, h.1.symm⟩

/-- `preprocess` preserves `stateSubstInfo` (only modifies `genEnv`). -/
theorem preprocess_preserves_stateSubstInfo (C : LContext CoreLParams) (Env : TEnv Unit)
    (ty ty' : LTy) (Env' : TEnv Unit)
    (h : CmdType.preprocess C Env ty = .ok (ty', Env')) :
    Env'.stateSubstInfo = Env.stateSubstInfo := by
  simp [CmdType.preprocess, Bind.bind, Except.bind, Except.mapError] at h
  elim_err h
  rename_i v hiwc; obtain ⟨mty, Env_iwc⟩ := v
  simp only [Except.ok.injEq, Prod.mk.injEq, pure, Except.pure] at h
  rw [← h.2]
  elim_err hiwc
  cases hiwc
  rename_i hiwc
  exact LTy_instantiateWithCheck_preserves_stateSubstInfo ty C Env mty Env_iwc hiwc

/-- `preprocess` produces a monotype satisfying `AnnotCompat` with `openFull xty`. -/
theorem preprocess_isInstance (C : LContext CoreLParams) (Env Env' : TEnv Unit)
    (xty : LTy) (mty_pre : LMonoTy)
    (h : CmdType.preprocess C Env xty = .ok (.forAll [] mty_pre, Env'))
    (h_aw : TContext.AliasesWF Env.context) :
    ∃ tys, tys.length = (LTy.boundVars xty).length ∧
      AnnotCompat Env.context.aliases (LTy.openFull xty tys) mty_pre := by
  simp only [CmdType.preprocess, Bind.bind, Except.bind, Except.mapError] at h
  elim_err h
  rename_i v hiwc; obtain ⟨mty, Env_iwc⟩ := v
  elim_err hiwc
  cases hiwc
  rename_i hiwc'
  simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
  obtain ⟨h_fst, h_snd⟩ := h
  obtain ⟨tys, h_len, h_ae⟩ :=
    Lambda.LExpr.LTy_instantiateWithCheck_isInstance xty C Env mty Env_iwc hiwc' h_aw
  refine ⟨tys, h_len, ?_⟩
  have h_mty_pre : mty_pre = LMonoTy.subst Env_iwc.stateSubstInfo.subst mty := by
    have h_inj := LTy.forAll.inj h_fst; exact h_inj.2.symm
  rw [h_mty_pre]
  exact AnnotCompat_subst Env_iwc.stateSubstInfo.subst
    (⟨[], by unfold LMonoTy.subst; simp [Subst.hasEmptyScopes, Map.isEmpty]; exact h_ae⟩) h_aw

/-- After the unification substitution `S` is applied, `preprocess`'s output satisfies
    `RigidAnnotCompat`. Requires that `S` is identity on rigid vars and absorbs
    `Env'`'s substitution. See `Cmd.typeCheck_sound` for the full rigid-var-identity
    invariant (establishment and preservation). -/
theorem preprocess_isInstance_rigidAnnotCompat (C : LContext CoreLParams) (Env Env' : TEnv Unit)
    (S : Subst) (xty : LTy) (mty_pre : LMonoTy)
    (h : CmdType.preprocess C Env xty = .ok (.forAll [] mty_pre, Env'))
    (h_wf : TEnvWF (T := CoreLParams) Env)
    (h_rigid : ∀ v, v ∈ C.rigidTypeVars → LMonoTy.subst S (.ftvar v) = .ftvar v)
    (h_absorbs : Subst.absorbs S Env.stateSubstInfo.subst) :
    ∃ tys, tys.length = (LTy.boundVars xty).length ∧
      RigidAnnotCompat Env.context.aliases C.rigidTypeVars
        (LTy.openFull xty tys) (LMonoTy.subst S mty_pre) := by
  simp only [CmdType.preprocess, Bind.bind, Except.bind, Except.mapError] at h
  elim_err h
  rename_i v hiwc; obtain ⟨mty, Env_iwc⟩ := v
  elim_err hiwc
  cases hiwc
  rename_i hiwc'
  simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
  obtain ⟨h_fst, h_snd⟩ := h
  have h_mty_pre : mty_pre = LMonoTy.subst Env_iwc.stateSubstInfo.subst mty := by
    have h_inj := LTy.forAll.inj h_fst; exact h_inj.2.symm
  -- instantiateWithCheck preserves stateSubstInfo (only changes genEnv).
  have h_iwc_subst : Env_iwc.stateSubstInfo = Env.stateSubstInfo :=
    LTy_instantiateWithCheck_preserves_stateSubstInfo xty C Env mty Env_iwc hiwc'
  obtain ⟨tys, h_len, h_ae⟩ :=
    Lambda.LExpr.LTy_instantiateWithCheck_isInstance xty C Env mty Env_iwc hiwc' h_wf.aliasesWF
  refine ⟨tys, h_len, ?_⟩
  -- Collapse: subst S (subst Env_iwc.subst mty) = subst S mty, since
  -- Env_iwc.subst = Env.subst (by h_iwc_subst) and S absorbs Env.subst (by h_absorbs).
  rw [h_mty_pre, congrArg (·.subst) h_iwc_subst,
    LMonoTy.subst_absorbs S Env.stateSubstInfo.subst mty h_absorbs]
  exact RigidAnnotCompat_subst S (.of_aliasEquiv h_ae) h_wf.aliasesWF h_rigid

/-- `postprocess` on a mono type applies the current substitution and preserves the environment. -/
theorem postprocess_result (C : LContext CoreLParams) (Env Env' : TEnv Unit)
    (mty : LMonoTy) (ty' : LTy)
    (h : CmdType.postprocess C Env (.forAll [] mty) = .ok (ty', Env')) :
    ty' = .forAll [] (LMonoTy.subst Env.stateSubstInfo.subst mty) ∧
    Env' = Env := by
  simp only [CmdType.postprocess, LTy.isMonoType, LTy.toMonoType] at h
  elim_err h
  simp only [Except.ok.injEq, Prod.mk.injEq] at h
  exact ⟨h.1.symm, h.2.symm⟩

/-- After unification, both sides of a mono constraint are equal under the result substitution. -/
theorem unifyTypes_eq (Env Env' : TEnv Unit)
    (xmty emty : LMonoTy)
    (h : CmdType.unifyTypes Env [(.forAll [] xmty, .forAll [] emty)] = .ok Env') :
    LMonoTy.subst Env'.stateSubstInfo.subst xmty =
      LMonoTy.subst Env'.stateSubstInfo.subst emty := by
  simp [CmdType.unifyTypes, CmdType.canonicalizeConstraints, LTy.isMonoType, LTy.boundVars,
    LTy.toMonoType, Bind.bind, Except.bind, Except.mapError, pure, Except.pure] at h
  elim_err h
  rename_i S hS
  simp only [Except.ok.injEq] at h
  subst h
  split at hS <;> try contradiction
  rename_i h_unify
  cases hS
  simp [TEnv.updateSubst]
  exact Constraints.unify_sound [(xmty, emty)] Env.stateSubstInfo S h_unify (xmty, emty) (.head _)

/-- `unifyTypes` does not change the context. -/
theorem unifyTypes_preserves_context (Env Env' : TEnv Unit)
    (constraints : List (LTy × LTy))
    (h : CmdType.unifyTypes Env constraints = .ok Env') :
    Env'.context = Env.context := by
  simp [CmdType.unifyTypes, Bind.bind, Except.bind, Except.mapError, pure, Except.pure] at h
  elim_errs h
  simp only [Except.ok.injEq] at h
  subst h
  simp [TEnv.updateSubst, TEnv.context]

/-- The result substitution of `unifyTypes` absorbs the input substitution. -/
theorem unifyTypes_absorbs (Env Env' : TEnv Unit)
    (constraints : List (LTy × LTy))
    (h : CmdType.unifyTypes Env constraints = .ok Env') :
    Subst.absorbs Env'.stateSubstInfo.subst Env.stateSubstInfo.subst := by
  simp [CmdType.unifyTypes, Bind.bind, Except.bind, Except.mapError, pure, Except.pure] at h
  elim_errs h
  rename_i _ cs _ _ S hS
  simp only [Except.ok.injEq] at h
  subst h
  simp [TEnv.updateSubst]
  have hS' : Constraints.unify cs Env.stateSubstInfo = .ok S := by
    revert hS; cases Constraints.unify cs Env.stateSubstInfo <;> simp
  exact Constraints.unify_absorbs cs Env.stateSubstInfo S hS'

/--
Decomposition of `inferType` success: if `inferType` returns `.ok`, then
`LExpr.resolve` succeeded on the same `Env` and `e`, and the outputs relate as expected.
-/
theorem inferType_decompose (C : LContext CoreLParams) (Env : TEnv Unit)
    (c : Cmd Expression) (e e' : LExpr CoreLParams.mono) (ety : LTy) (Env' : TEnv Unit)
    (h : CmdType.inferType C Env c e = .ok (e', ety, Env')) :
    ∃ ea : LExprT CoreLParams.mono,
      LExpr.resolve C Env e = .ok (ea, Env') ∧
      e' = ea.unresolved ∧
      ety = .forAll [] ea.toLMonoTy := by
  simp only [CmdType.inferType, Bind.bind, Except.bind, Except.mapError] at h
  elim_errs h
  · rename_i v h_resolve
    obtain ⟨ea, Env_r⟩ := v
    simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨h_e', h_ety, h_env'⟩ := h
    subst h_e' h_ety h_env'
    have h_res : LExpr.resolve C Env e = .ok (ea, Env_r) := by
      revert h_resolve
      cases h_r : LExpr.resolve C Env e <;> simp
    exact ⟨ea, h_res, rfl, rfl⟩

/-- `inferType` produces a substitution that absorbs the input substitution.
    Follows from `resolveAux_properties.absorbs`. -/
theorem inferType_absorbs (C : LContext CoreLParams) (Env Env' : TEnv Unit)
    (c : Cmd Expression) (e e' : LExpr CoreLParams.mono) (ety : LTy)
    (h : CmdType.inferType C Env c e = .ok (e', ety, Env'))
    (h_wf : TEnvWF (T := CoreLParams) Env)
    (h_fwf : FactoryWF C.functions) :
    Subst.absorbs Env'.stateSubstInfo.subst Env.stateSubstInfo.subst := by
  obtain ⟨ea, h_resolve, _, _⟩ := inferType_decompose C Env c e e' ety Env' h
  unfold LExpr.resolve at h_resolve
  simp only [Bind.bind, Except.bind] at h_resolve
  generalize h_init : (if Env.context.types.isEmpty = true then
      Env.updateContext { types := [[]], aliases := Env.context.aliases }
    else Env) = Env0 at h_resolve
  match h_res : resolveAux C Env0 e with
  | .error _ => simp [h_res] at h_resolve
  | .ok (et, Env_out) =>
    simp [h_res] at h_resolve
    obtain ⟨_, h_env'⟩ := h_resolve
    subst h_env'
    have h_envwf0 : TEnvWF (T := CoreLParams) Env0 :=
      h_init ▸ Lambda.TEnvWF_resolve_init (T := CoreLParams) Env h_wf
    have h_ne0 : Env0.context.types ≠ [] := by
      subst h_init; split
      · exact List.cons_ne_nil _ _
      · rename_i h_not_empty; intro h_abs; simp_all; contradiction
    have h_props := resolveAux_properties e et C Env0 Env_out h_res h_ne0
      h_envwf0.aliasesWF h_fwf h_envwf0.substFreshForGen h_envwf0.ctxFreshForGen
      h_envwf0.boundVarsFresh
    have h_subst_eq : Env0.stateSubstInfo = Env.stateSubstInfo := by
      subst h_init; split <;> simp [TEnv.updateContext]
    have h_abs := h_props.absorbs
    rw [congrArg (·.subst) h_subst_eq] at h_abs
    exact h_abs

/-- The `checkAnnotCompat` success implies all rigid vars are identity under the
    current substitution. This is the direct computational content of the check. -/
theorem checkAnnotCompat_rigid (C : LContext CoreLParams) (Env : TEnv Unit)
    (h : CmdType.checkAnnotCompat C Env = .ok ()) :
    ∀ v, v ∈ C.rigidTypeVars → LMonoTy.subst Env.stateSubstInfo.subst (.ftvar v) = .ftvar v := by
  intro v hv
  simp only [CmdType.checkAnnotCompat] at h
  split at h
  · rename_i h_empty
    cases C.rigidTypeVars <;> grind
  · rename_i h_not_empty
    split at h
    · contradiction
    · rename_i h_find_none
      have h_pred := List.find?_eq_none.mp h_find_none v hv
      simp only [bne, Bool.not_eq_true', beq_eq_false_iff_ne, ne_eq, Decidable.not_not] at h_pred
      exact h_pred

/--
`inferType` success implies all free vars of `e` are in `Env.context.knownVars`.
-/
theorem inferType_fvars_in_knownVars (C : LContext CoreLParams) (Env : TEnv Unit)
    (c : Cmd Expression) (e e' : LExpr CoreLParams.mono) (ety : LTy) (Env' : TEnv Unit)
    (h : CmdType.inferType C Env c e = .ok (e', ety, Env')) :
    ∀ x ∈ LExpr.freeVars e, x.1 ∈ TContext.knownVars Env.context := by
  simp only [CmdType.inferType, Bind.bind, Except.bind, Except.mapError] at h
  elim_err h
  rename_i h_fvc
  have h_fvc_ok : Env.freeVarCheck e (Std.format "[" ++ Std.format c ++ Std.format "]") = .ok () := by
    revert h_fvc
    cases h_r : Env.freeVarCheck e (Std.format "[" ++ Std.format c ++ Std.format "]") with
    | error => simp
    | ok v => simp
  exact TEnv.freeVarCheck_implies_fvars_in_knownVars Env e _ h_fvc_ok

/-- `preprocess` does not change the context. -/
theorem preprocess_preserves_context (C : LContext CoreLParams) (Env : TEnv Unit)
    (ty : LTy) (ty' : LTy) (Env' : TEnv Unit)
    (h : CmdType.preprocess C Env ty = .ok (ty', Env')) :
    Env'.context = Env.context := by
  simp only [CmdType.preprocess, Bind.bind, Except.bind, Except.mapError] at h
  elim_err h
  rename_i v h_iwc
  obtain ⟨mty, Env1⟩ := v
  simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
  obtain ⟨_, h2⟩ := h; subst h2
  have h_iwc' : LTy.instantiateWithCheck ty C Env = .ok (mty, Env1) := by
    revert h_iwc; cases LTy.instantiateWithCheck ty C Env <;> simp
  exact LTy_instantiateWithCheck_context' ty C Env mty Env1 h_iwc'

/-- `preprocess` preserves well-formedness of the type environment. -/
theorem preprocess_preserves_TEnvWF (C : LContext CoreLParams) (Env : TEnv Unit)
    (ty : LTy) (ty' : LTy) (Env' : TEnv Unit)
    (h : CmdType.preprocess C Env ty = .ok (ty', Env'))
    (h_wf : TEnvWF (T := CoreLParams) Env) :
    TEnvWF (T := CoreLParams) Env' := by
  simp only [CmdType.preprocess, Bind.bind, Except.bind, Except.mapError] at h
  split at h
  · simp at h
  · rename_i v h_iwc
    obtain ⟨mty, Env1⟩ := v
    simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨_, h2⟩ := h; subst h2
    have h_iwc' : LTy.instantiateWithCheck ty C Env = .ok (mty, Env1) := by
      revert h_iwc; cases LTy.instantiateWithCheck ty C Env <;> simp
    exact LTy_instantiateWithCheck_TEnvWF ty C Env mty Env1 h_iwc' h_wf

/-- `inferType` does not change the context. -/
theorem inferType_preserves_context (C : LContext CoreLParams) (Env Env' : TEnv Unit)
    (c : Cmd Expression) (e e' : LExpr CoreLParams.mono) (ety : LTy)
    (h : CmdType.inferType C Env c e = .ok (e', ety, Env'))
    (h_wf : TEnvWF (T := CoreLParams) Env)
    (h_ne : Env.context.types ≠ [])
    (h_fwf : FactoryWF C.functions) :
    Env'.context = Env.context := by
  obtain ⟨ea, h_resolve, _, _⟩ := inferType_decompose C Env c e e' ety Env' h
  have h_ws : WellScoped e Env.context := inferType_fvars_in_knownVars C Env c e e' ety Env' h
  exact resolve_preserves_context e ea C Env Env' h_resolve h_wf h_ne h_fwf

/--
`inferType` success implies `HasType` holds universally over absorbing substitutions.
-/
theorem inferType_HasType (C : LContext CoreLParams) (Env Env' : TEnv Unit)
    (c : Cmd Expression) (e e' : LExpr CoreLParams.mono) (ety : LTy)
    (h : CmdType.inferType C Env c e = .ok (e', ety, Env'))
    (h_wf : TEnvWF (T := CoreLParams) Env)
    (h_fwf : FactoryWF C.functions) :
    ∃ mty, ety = .forAll [] mty ∧
      (∀ S, Subst.absorbs S Env'.stateSubstInfo.subst → SubstWF S →
        Subst.polyKeysFresh (T := CoreLParams) S Env.context →
        HasType (T := CoreLParams) C (TContext.subst Env.context S) e
          (.forAll [] (LMonoTy.subst S mty))) := by
  obtain ⟨ea, h_resolve, _, h_ety⟩ := inferType_decompose C Env c e e' ety Env' h
  have h_ws : WellScoped e Env.context := inferType_fvars_in_knownVars C Env c e e' ety Env' h
  have ⟨h_ht, _, _⟩ := resolve_HasType_core e ea C Env Env' h_resolve h_wf h_fwf h_ws
  exact ⟨ea.toLMonoTy, h_ety, h_ht⟩


end CmdType

/-- `Cmd.typeCheck` preserves the rigid-var-identity invariant.
    See `Cmd.typeCheck_sound` for the full invariant. -/
theorem Cmd.typeCheck_preserves_rigid_inv (C : LContext CoreLParams) (Env : TEnv Unit)
    (cmd cmd' : Cmd Expression) (Env' : TEnv Unit)
    (h : Imperative.Cmd.typeCheck C Env cmd = .ok (cmd', Env'))
    (h_rigid_inv : ∀ v, v ∈ C.rigidTypeVars →
      LMonoTy.subst Env.stateSubstInfo.subst (.ftvar v) = .ftvar v) :
    ∀ v, v ∈ C.rigidTypeVars →
      LMonoTy.subst Env'.stateSubstInfo.subst (.ftvar v) = .ftvar v := by
  cases cmd with
  | init x xty e md =>
    simp only [Cmd.typeCheck, Bind.bind, Except.bind] at h
    elim_err h; rename_i h_lookup
    split at h
    · -- det
      elim_err h; elim_err h; rename_i v1 h_preprocess
      elim_err h; elim_err h; rename_i Env_unified h_unify
      elim_err h; rename_i _u h_check
      elim_err h; rename_i v3 h_postprocess; cases h
      simp only [TypeContext.update, TypeContext.checkAnnotCompat, TypeContext.preprocess,
        TypeContext.postprocess] at *
      rw [CmdType.update_preserves_subst,
        (CmdType.postprocess_result C Env_unified v3.snd _  v3.fst
          (by rw [← (CmdType.preprocess_mono C Env xty v1.fst v1.snd h_preprocess).choose_spec]
              exact h_postprocess)).2]
      exact CmdType.checkAnnotCompat_rigid C Env_unified h_check
    · -- nondet
      elim_err h; rename_i v1 h_preprocess
      elim_err h; rename_i v2 h_postprocess; cases h
      simp only [TypeContext.update, TypeContext.preprocess, TypeContext.postprocess] at *
      rw [CmdType.update_preserves_subst,
        (CmdType.postprocess_result C v1.snd v2.snd _ v2.fst
          (by rw [← (CmdType.preprocess_mono C Env xty v1.fst v1.snd h_preprocess).choose_spec]
              exact h_postprocess)).2,
        congrArg (·.subst) (CmdType.preprocess_preserves_stateSubstInfo C Env xty v1.fst v1.snd h_preprocess)]
      exact h_rigid_inv
  | set x e md =>
    simp only [Cmd.typeCheck, Bind.bind, Except.bind] at h
    elim_err h; rename_i xty h_lookup
    cases e with
    | det expr =>
      simp only [] at h
      elim_err h; elim_err h; rename_i Env_unified h_unify
      elim_err h; rename_i _u h_check; cases h
      simp only [TypeContext.checkAnnotCompat] at *
      exact CmdType.checkAnnotCompat_rigid C Env' h_check
    | nondet => simp at h; cases h; exact h_rigid_inv
  | assert label e md =>
    simp only [Cmd.typeCheck, Bind.bind, Except.bind] at h
    elim_err h; rename_i v h_infer
    elim_err h; rename_i _u h_check
    elim_err h; cases h
    simp only [TypeContext.checkAnnotCompat] at *
    exact CmdType.checkAnnotCompat_rigid C v.2.snd h_check
  | assume label e md =>
    simp only [Cmd.typeCheck, Bind.bind, Except.bind] at h
    elim_err h; rename_i v h_infer
    elim_err h; rename_i _u h_check
    elim_err h; cases h
    simp only [TypeContext.checkAnnotCompat] at *
    exact CmdType.checkAnnotCompat_rigid C v.2.snd h_check
  | cover label e md =>
    simp only [Cmd.typeCheck, Bind.bind, Except.bind] at h
    elim_err h; rename_i v h_infer
    elim_err h; rename_i _u h_check
    elim_err h; cases h
    simp only [TypeContext.checkAnnotCompat] at *
    exact CmdType.checkAnnotCompat_rigid C v.2.snd h_check

end
end Core
