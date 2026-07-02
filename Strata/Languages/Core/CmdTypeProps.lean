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

/-- `update` keeps the type-scope non-empty (it pushes onto the newest scope). -/
theorem update_types_ne (Env : TEnv Unit) (x : CoreIdent) (ty : LTy) :
    (CmdType.update Env x ty).context.types ≠ [] := by
  simp only [CmdType.update, TEnv.addInNewestContext, TEnv.updateContext, TEnv.context,
    Maps.addInNewest, Maps.push]
  exact List.cons_ne_nil _ _

/-- `update` with a monomorphic binding preserves `ContextMono`: the new type
    `forAll [] mty` has empty `boundVars`, and old bindings keep their types. -/
theorem update_ContextMono (Env : TEnv Unit) (x : CoreIdent) (mty : LMonoTy)
    (h_mono : ∀ y ty, Env.context.types.find? y = some ty → LTy.boundVars ty = []) :
    ∀ y ty, (CmdType.update Env x (.forAll [] mty)).context.types.find? y = some ty →
      LTy.boundVars ty = [] := by
  intro y ty h_find
  simp only [CmdType.update, TEnv.addInNewestContext, TEnv.updateContext, TEnv.context] at h_find
  rcases Maps.find?_addInNewest_single Env.genEnv.context.types x (.forAll [] mty) y with
    ⟨h_new, _⟩ | h_old
  · rw [h_new] at h_find; injection h_find with h_find; subst h_find; simp [LTy.boundVars]
  · rw [h_old] at h_find
    exact h_mono y ty (by simpa only [TEnv.context] using h_find)

/-- `update` with a gen-fresh monomorphic binding preserves `TEnvWF`. Direct
    application of `TEnvWF.of_addInNewestContext_singleton` (`update = addInNewestContext`). -/
theorem update_TEnvWF (Env : TEnv Unit) (x : CoreIdent) (mty : LMonoTy)
    (h_wf : TEnvWF (T := CoreLParams) Env)
    (h_fresh : ∀ v, v ∈ LMonoTy.freeVars mty →
      ∀ n, n ≥ Env.genEnv.genState.tyGen → v ≠ TState.tyPrefix ++ toString n) :
    TEnvWF (T := CoreLParams) (CmdType.update Env x (.forAll [] mty)) :=
  Lambda.LExpr.TEnvWF.of_addInNewestContext_singleton (T := CoreLParams) Env x mty h_wf h_fresh

/-- `update` only grows the *newest* `types` scope, so popping it recovers the
    input stack tail. Structural — no well-scoping assumption. -/
theorem update_types_pop (Env : TEnv Unit) (x : CoreIdent) (ty : LTy) :
    Maps.pop (CmdType.update Env x ty).context.types = Maps.pop Env.context.types := by
  simp only [CmdType.update, TEnv.addInNewestContext, TEnv.updateContext, TEnv.context,
    Maps.addInNewest, Maps.push, Maps.pop]

/-- `update` leaves the alias list unchanged (it only touches `types`). -/
theorem update_aliases (Env : TEnv Unit) (x : CoreIdent) (ty : LTy) :
    (CmdType.update Env x ty).context.aliases = Env.context.aliases := by
  simp only [CmdType.update, TEnv.addInNewestContext, TEnv.updateContext, TEnv.context]

/-- `update` does not change the generator counter (only context bindings). -/
theorem update_tyGen (Env : TEnv Unit) (x : CoreIdent) (ty : LTy) :
    (CmdType.update Env x ty).genEnv.genState.tyGen = Env.genEnv.genState.tyGen := by
  simp only [CmdType.update, TEnv.addInNewestContext, TEnv.updateContext]

/-- Substitution on the output context of `update` inserts the substituted type. -/
theorem update_subst_context (Env : TEnv Unit) (x : CoreIdent) (ty : LTy) (S : Subst)
    (h_fresh : Env.context.types.find? x = none) :
    TContext.subst (CmdType.update Env x ty).context S =
      { TContext.subst Env.context S with
        types := (TContext.subst Env.context S).types.insert x (LTy.subst S ty) } := by
  simp [CmdType.update]
  exact TEnv.addInNewestContext_singleton_subst_context (T := CoreLParams) Env x ty S h_fresh

/-- Decompose a successful `preprocess` into the underlying `instantiateWithCheck` step.
    `preprocess` rejects polymorphic annotations (`boundVars != []`), then instantiates and
    substitutes; on success the input is monomorphic and the result is `forAll []` of the
    instantiated, substituted monotype. The guard is peeled here so the downstream lemmas
    need not know about it. (The free-var-rigid check lives in `postprocess`, post-unification.) -/
theorem preprocess_decompose (C : LContext CoreLParams) (Env : TEnv Unit)
    (ty ty' : LTy) (Env' : TEnv Unit)
    (h : CmdType.preprocess C Env ty = .ok (ty', Env')) :
    ∃ mty, ty.boundVars = [] ∧
      LTy.instantiateWithCheck ty C Env = .ok (mty, Env') ∧
      ty' = .forAll [] (LMonoTy.subst Env'.stateSubstInfo.subst mty) := by
  simp only [CmdType.preprocess, Bind.bind, Except.bind, Except.mapError] at h
  -- Polymorphic guard: `boundVars != []` ⟹ error. Success is the `else` (isFalse) branch.
  split at h
  · simp only [reduceCtorEq] at h
  · rename_i h_bv
    rw [Bool.not_eq_true, bne_eq_false_iff_eq] at h_bv
    -- Collapse the guard's else (`pure ()`) so the next match is `instantiateWithCheck`.
    simp only [pure, Except.pure] at h
    -- `instantiateWithCheck` step.
    split at h
    · simp only [reduceCtorEq] at h
    · rename_i v h_iwc
      obtain ⟨mty, Env_iwc⟩ := v
      simp only [Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨h_fst, h_snd⟩ := h
      have h_iwc' : LTy.instantiateWithCheck ty C Env = .ok (mty, Env_iwc) := by
        revert h_iwc; cases LTy.instantiateWithCheck ty C Env <;> simp
      subst h_snd
      exact ⟨mty, h_bv, h_iwc', h_fst.symm⟩

/-- `preprocess` always produces a monomorphic type (`forAll [] mty`). -/
theorem preprocess_mono (C : LContext CoreLParams) (Env : TEnv Unit)
    (ty ty' : LTy) (Env' : TEnv Unit)
    (h : CmdType.preprocess C Env ty = .ok (ty', Env')) :
    ∃ mty, ty' = .forAll [] mty := by
  obtain ⟨mty, _, _, h_eq⟩ := preprocess_decompose C Env ty ty' Env' h
  exact ⟨_, h_eq⟩

/-- `preprocess` preserves `stateSubstInfo` (only modifies `genEnv`). -/
theorem preprocess_preserves_stateSubstInfo (C : LContext CoreLParams) (Env : TEnv Unit)
    (ty ty' : LTy) (Env' : TEnv Unit)
    (h : CmdType.preprocess C Env ty = .ok (ty', Env')) :
    Env'.stateSubstInfo = Env.stateSubstInfo := by
  obtain ⟨mty, _, h_iwc, _⟩ := preprocess_decompose C Env ty ty' Env' h
  exact LTy_instantiateWithCheck_preserves_stateSubstInfo ty C Env mty Env' h_iwc

/-- `preprocess` produces a monotype satisfying `AnnotCompat` with `openFull xty`. -/
theorem preprocess_isInstance (C : LContext CoreLParams) (Env Env' : TEnv Unit)
    (xty : LTy) (mty_pre : LMonoTy)
    (h : CmdType.preprocess C Env xty = .ok (.forAll [] mty_pre, Env'))
    (h_aw : TContext.AliasesWF Env.context) :
    ∃ tys, tys.length = (LTy.boundVars xty).length ∧
      AnnotCompat Env.context.aliases (LTy.openFull xty tys) mty_pre := by
  obtain ⟨mty, _, h_iwc, h_eq⟩ := preprocess_decompose C Env xty (.forAll [] mty_pre) Env' h
  obtain ⟨tys, h_len, h_ae⟩ :=
    Lambda.LExpr.LTy_instantiateWithCheck_isInstance xty C Env mty Env' h_iwc h_aw
  refine ⟨tys, h_len, ?_⟩
  have h_mty_pre : mty_pre = LMonoTy.subst Env'.stateSubstInfo.subst mty :=
    (LTy.forAll.inj h_eq).2
  rw [h_mty_pre]
  exact AnnotCompat_subst Env'.stateSubstInfo.subst
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
  obtain ⟨mty, _, h_iwc, h_eq⟩ := preprocess_decompose C Env xty (.forAll [] mty_pre) Env' h
  have h_mty_pre : mty_pre = LMonoTy.subst Env'.stateSubstInfo.subst mty :=
    (LTy.forAll.inj h_eq).2
  -- instantiateWithCheck preserves stateSubstInfo (only changes genEnv).
  have h_iwc_subst : Env'.stateSubstInfo = Env.stateSubstInfo :=
    LTy_instantiateWithCheck_preserves_stateSubstInfo xty C Env mty Env' h_iwc
  obtain ⟨tys, h_len, h_ae⟩ :=
    Lambda.LExpr.LTy_instantiateWithCheck_isInstance xty C Env mty Env' h_iwc h_wf.aliasesWF
  refine ⟨tys, h_len, ?_⟩
  -- Collapse: subst S (subst Env'.subst mty) = subst S mty, since
  -- Env'.subst = Env.subst (by h_iwc_subst) and S absorbs Env.subst (by h_absorbs).
  rw [h_mty_pre, congrArg (·.subst) h_iwc_subst,
    LMonoTy.subst_absorbs S Env.stateSubstInfo.subst mty h_absorbs]
  exact RigidAnnotCompat_subst S (.of_aliasEquiv h_ae) h_wf.aliasesWF h_rigid

/-- `postprocess` on a mono type applies the current substitution and preserves the environment. -/
theorem postprocess_result (C : LContext CoreLParams) (Env Env' : TEnv Unit)
    (mty : LMonoTy) (ty' : LTy)
    (h : CmdType.postprocess C Env (.forAll [] mty) = .ok (ty', Env')) :
    ty' = .forAll [] (LMonoTy.subst Env.stateSubstInfo.subst mty) ∧
    Env' = Env := by
  simp only [CmdType.postprocess, LTy.isMonoType, LTy.toMonoType, Bind.bind, Except.bind,
    pure, Except.pure] at h
  -- `isMonoType` true branch, then the stray-var guard: only the `else` (no stray) succeeds.
  split at h
  · split at h
    · exact absurd h (by simp)
    · simp only [Except.ok.injEq, Prod.mk.injEq] at h
      exact ⟨h.1.symm, h.2.symm⟩
  · exact absurd h (by simp)

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

/-- `unifyTypes` on a single monomorphic constraint preserves `TEnvWF`, provided
    the constraint's free type variables are gen-fresh for the input generator
    state. `unifyTypes` runs `Constraints.unify [(xmty, emty)] Env.subst` then
    `updateSubst`, so this is a direct application of `TEnvWF.of_unify_updateSubst`
    with the constraint freshness assembled from the two sides. -/
theorem unifyTypes_TEnvWF (Env Env' : TEnv Unit) (xmty emty : LMonoTy)
    (h : CmdType.unifyTypes Env [(.forAll [] xmty, .forAll [] emty)] = .ok Env')
    (h_wf : TEnvWF (T := CoreLParams) Env)
    (h_xmty : ∀ v, v ∈ LMonoTy.freeVars xmty →
      ∀ n, n ≥ Env.genEnv.genState.tyGen → v ≠ TState.tyPrefix ++ toString n)
    (h_emty : ∀ v, v ∈ LMonoTy.freeVars emty →
      ∀ n, n ≥ Env.genEnv.genState.tyGen → v ≠ TState.tyPrefix ++ toString n) :
    TEnvWF (T := CoreLParams) Env' := by
  simp [CmdType.unifyTypes, CmdType.canonicalizeConstraints, LTy.isMonoType,
    LTy.boundVars, LTy.toMonoType, Bind.bind, Except.bind, Except.mapError, pure,
    Except.pure] at h
  elim_err h
  rename_i S hS
  simp only [Except.ok.injEq] at h
  subst h
  have h_unify : Constraints.unify [(xmty, emty)] Env.stateSubstInfo = .ok S := by
    revert hS; cases Constraints.unify [(xmty, emty)] Env.stateSubstInfo <;> simp
  have h_cs_fresh : ∀ v, v ∈ Constraints.freeVars [(xmty, emty)] →
      ∀ n, n ≥ Env.genEnv.genState.tyGen → v ≠ TState.tyPrefix ++ toString n := by
    intro v hv n hn
    simp only [Constraints.freeVars, Constraint.freeVars, List.append_nil,
      List.mem_append] at hv
    cases hv with
    | inl h_x => exact h_xmty v h_x n hn
    | inr h_e => exact h_emty v h_e n hn
  exact Lambda.LExpr.TEnvWF.of_unify_updateSubst h_wf h_unify h_cs_fresh

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

/-- `unifyTypes` does not change the generator state (only `updateSubst`, which
    touches `stateSubstInfo` alone). -/
theorem unifyTypes_preserves_genState (Env Env' : TEnv Unit)
    (constraints : List (LTy × LTy))
    (h : CmdType.unifyTypes Env constraints = .ok Env') :
    Env'.genEnv.genState = Env.genEnv.genState := by
  simp [CmdType.unifyTypes, Bind.bind, Except.bind, Except.mapError, pure, Except.pure] at h
  elim_errs h
  simp only [Except.ok.injEq] at h
  subst h
  simp [TEnv.updateSubst]

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
  obtain ⟨mty, _, h_iwc, _⟩ := preprocess_decompose C Env ty ty' Env' h
  exact LTy_instantiateWithCheck_context' ty C Env mty Env' h_iwc

/-- `preprocess` is gen-counter monotone (it runs `instantiateWithCheck`, which
    only allocates fresh names). -/
theorem preprocess_genState_mono (C : LContext CoreLParams) (Env : TEnv Unit)
    (ty : LTy) (ty' : LTy) (Env' : TEnv Unit)
    (h : CmdType.preprocess C Env ty = .ok (ty', Env')) :
    Env'.genEnv.genState.tyGen ≥ Env.genEnv.genState.tyGen := by
  obtain ⟨mty, _, h_iwc, _⟩ := preprocess_decompose C Env ty ty' Env' h
  exact LTy_instantiateWithCheck_tyGen_mono ty C Env mty Env' h_iwc

/-- `preprocess` preserves well-formedness of the type environment. -/
theorem preprocess_preserves_TEnvWF (C : LContext CoreLParams) (Env : TEnv Unit)
    (ty : LTy) (ty' : LTy) (Env' : TEnv Unit)
    (h : CmdType.preprocess C Env ty = .ok (ty', Env'))
    (h_wf : TEnvWF (T := CoreLParams) Env) :
    TEnvWF (T := CoreLParams) Env' := by
  obtain ⟨mty, _, h_iwc, _⟩ := preprocess_decompose C Env ty ty' Env' h
  exact LTy_instantiateWithCheck_TEnvWF ty C Env mty Env' h_iwc h_wf

/-- The free variables of `preprocess`'s output type are gen-fresh for the output
    generator state. The output type is `subst Env'.subst mty_inst` where `mty_inst`
    is the `instantiateWithCheck` result; `LTy_instantiateWithCheck_freeVars_fresh`
    gives that `mty_inst` is gen-fresh and `Env'`'s `TEnvWF` gives that its
    substitution is gen-fresh, so `freeVars_subst_genFresh` composes them. Consumed
    by `Cmd.typeCheck_preserves` to supply the unify-constraint freshness side
    condition for the `init.det` case. -/
theorem preprocess_output_fresh (C : LContext CoreLParams) (Env : TEnv Unit)
    (ty : LTy) (mty : LMonoTy) (Env' : TEnv Unit)
    (h : CmdType.preprocess C Env ty = .ok (.forAll [] mty, Env'))
    (h_wf : TEnvWF (T := CoreLParams) Env) :
    ∀ v, v ∈ LMonoTy.freeVars mty →
      ∀ n, n ≥ Env'.genEnv.genState.tyGen → v ≠ TState.tyPrefix ++ toString n := by
  obtain ⟨mty_inst, _, h_iwc', h_eq⟩ := preprocess_decompose C Env ty (.forAll [] mty) Env' h
  -- `mty = subst Env'.subst mty_inst`.
  simp only [LTy.forAll.injEq] at h_eq
  obtain ⟨_, h_mty⟩ := h_eq
  have h_envwf' : TEnvWF (T := CoreLParams) Env' :=
    LTy_instantiateWithCheck_TEnvWF ty C Env mty_inst Env' h_iwc' h_wf
  have h_inst_fresh := Lambda.LExpr.LTy_instantiateWithCheck_freeVars_fresh
    ty C Env mty_inst Env' h_iwc'
  rw [h_mty]
  exact Lambda.LExpr.freeVars_subst_genFresh Env'.stateSubstInfo mty_inst
    Env'.genEnv.genState h_envwf'.substFreshForGen h_inst_fresh

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

/-- `inferType` preserves `TEnvWF`. It runs `freeVarCheck` (no env change) then
    `LExpr.resolve`, so `resolve_TEnvWF` applies. -/
theorem inferType_TEnvWF (C : LContext CoreLParams) (Env Env' : TEnv Unit)
    (c : Cmd Expression) (e e' : LExpr CoreLParams.mono) (ety : LTy)
    (h : CmdType.inferType C Env c e = .ok (e', ety, Env'))
    (h_wf : TEnvWF (T := CoreLParams) Env)
    (h_fwf : FactoryWF C.functions) :
    TEnvWF (T := CoreLParams) Env' := by
  obtain ⟨ea, h_resolve, _, _⟩ := inferType_decompose C Env c e e' ety Env' h
  exact Lambda.resolve_TEnvWF e ea C Env Env' h_resolve h_wf h_fwf

/-- `inferType` never decreases the generator counter. Follows from
    `resolveAux_properties.genState_mono` (and `resolve`'s `Env0` step, which only
    rewrites the context, leaving the generator untouched). -/
theorem inferType_genState_mono (C : LContext CoreLParams) (Env Env' : TEnv Unit)
    (c : Cmd Expression) (e e' : LExpr CoreLParams.mono) (ety : LTy)
    (h : CmdType.inferType C Env c e = .ok (e', ety, Env'))
    (h_wf : TEnvWF (T := CoreLParams) Env)
    (h_fwf : FactoryWF C.functions) :
    Env'.genEnv.genState.tyGen ≥ Env.genEnv.genState.tyGen := by
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
    have h_gen_eq : Env0.genEnv.genState = Env.genEnv.genState := by
      subst h_init; split <;> simp [TEnv.updateContext]
    rw [← h_gen_eq]; exact h_props.genState_mono

/-- The free variables of `inferType`'s output type are gen-fresh for the output
    generator state. The output type is `subst Env'.subst (et.toLMonoTy)` where
    `et` is the raw resolve result; `resolveAux_properties.preserves.2` gives that
    the raw type is gen-fresh and `Env'`'s `TEnvWF` gives that its substitution is
    gen-fresh, so `freeVars_subst_genFresh` composes them. Consumed by
    `Cmd.typeCheck_preserves` to supply the unify-constraint freshness side
    condition of `TEnvWF.of_unify_updateSubst`. -/
theorem inferType_output_fresh (C : LContext CoreLParams) (Env Env' : TEnv Unit)
    (c : Cmd Expression) (e e' : LExpr CoreLParams.mono) (ety : LTy)
    (h : CmdType.inferType C Env c e = .ok (e', ety, Env'))
    (h_wf : TEnvWF (T := CoreLParams) Env)
    (h_fwf : FactoryWF C.functions) :
    ∃ mty, ety = .forAll [] mty ∧
      ∀ v, v ∈ LMonoTy.freeVars mty →
        ∀ n, n ≥ Env'.genEnv.genState.tyGen → v ≠ TState.tyPrefix ++ toString n := by
  obtain ⟨ea, h_resolve, _, h_ety⟩ := inferType_decompose C Env c e e' ety Env' h
  refine ⟨ea.toLMonoTy, h_ety, ?_⟩
  unfold LExpr.resolve at h_resolve
  simp only [Bind.bind, Except.bind] at h_resolve
  generalize h_init : (if Env.context.types.isEmpty = true then
      Env.updateContext { types := [[]], aliases := Env.context.aliases }
    else Env) = Env0 at h_resolve
  match h_res : resolveAux C Env0 e with
  | .error _ => simp [h_res] at h_resolve
  | .ok (et, Env_out) =>
    simp [h_res] at h_resolve
    obtain ⟨h_ea, h_env'⟩ := h_resolve
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
    have h_envwf_out : TEnvWF (T := CoreLParams) Env_out :=
      Lambda.resolveAux_TEnvWF e et C Env0 Env_out h_res h_envwf0 h_ne0 h_fwf
    -- `ea = applySubstT et Env_out.subst`, so `ea.toLMonoTy = subst Env_out.subst et.toLMonoTy`.
    rw [← h_ea, Lambda.LExpr.applySubstT_toLMonoTy]
    exact Lambda.LExpr.freeVars_subst_genFresh Env_out.stateSubstInfo et.toLMonoTy
      Env_out.genEnv.genState h_envwf_out.substFreshForGen h_props.preserves.2

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
