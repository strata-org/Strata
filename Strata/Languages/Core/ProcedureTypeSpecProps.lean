/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

import Strata.Languages.Core.ProcedureTypeSpec
import all Strata.Languages.Core.ProcedureType
import all Strata.Languages.Core.Procedure
import all Strata.Languages.Core.ProgramWF
import all Strata.Languages.Core.StatementTypeSpecProps
import all Strata.Languages.Core.FunctionTypeSpecProps
import all Strata.Languages.Core.CommandTypeSpecProps
import all Strata.Languages.Core.CmdTypeSpecProps
import all Strata.DL.Lambda.LExprTypeEnv

set_option linter.unusedVariables false

/-! ## Soundness of the Procedure Typechecker

Relates the executable procedure typechecker `Core.Procedure.typeCheck` to the
declarative relation `ProcHasType'` from `ProcedureTypeSpec.lean`. Procedure-level
analogue of `FunctionTypeSpecProps.lean` / `StatementTypeSpecProps.lean`.

* **Annotated** `Procedure.typeCheck_annotated_sound`: success ⇒ the OUTPUT
  procedure `proc'` satisfies `ProcHasTypeA` at the body type-scope `Env'.context`.
* **Polymorphic** `Procedure.typeCheck_sound`: success ⇒ the INPUT procedure
  `proc` satisfies `ProcHasType` in the ambient `Env.context`. Currently `sorry`.

The body obligation delegates to the already-proved statement soundness theorems
(`Statement.typeCheck_{annotated_sound,sound}`) plus a context bridge.
-/

namespace Core
namespace TypeSpec

open Lambda LExpr Imperative
open Core.Statement

/-! ### Procedure-entry well-formedness preservation

Lemmas showing the body-typing environment `envForBody` inside `Procedure.typeCheck`
is well-formed, built by composing the per-step preservation primitives across
`setupInputEnv` / `typeCheckConditions` / etc. These discharge the WF hypotheses of
`Statement.typeCheck_{sound,annotated_sound}` when it is invoked on the procedure body. -/

/-- `TEnvWF` is preserved through `typeCheckConditions.go`. -/
theorem typeCheckConditions_go_TEnvWF (C : Core.Expression.TyContext) (procName : CoreIdent)
    (conds : List (CoreLabel × Core.Procedure.Check)) (acc : Array Expression.Expr)
    (Env : Core.Expression.TyEnv) (res : Array Expression.Expr × Core.Expression.TyEnv)
    (h : Core.Procedure.typeCheckConditions.go C procName conds acc Env = .ok res)
    (h_wf : TEnvWF (T := CoreLParams) Env)
    (h_fwf : FactoryWF C.functions) :
    TEnvWF (T := CoreLParams) res.2 := by
  induction conds generalizing acc Env with
  | nil =>
    simp only [Core.Procedure.typeCheckConditions.go] at h
    cases h; exact h_wf
  | cons pair rest ih =>
    obtain ⟨name, condition⟩ := pair
    simp only [Core.Procedure.typeCheckConditions.go, Bind.bind, Except.bind,
      Except.mapError] at h
    cases h_res : Lambda.LExpr.resolve C Env condition.expr with
    | error e => rw [h_res] at h; simp only [reduceCtorEq] at h
    | ok v_res =>
      obtain ⟨annotatedExpr, newEnv⟩ := v_res
      rw [h_res] at h
      simp only at h
      split at h
      · simp only [reduceCtorEq] at h
      · have h_newwf : TEnvWF (T := CoreLParams) newEnv :=
          Lambda.resolve_TEnvWF condition.expr annotatedExpr C Env newEnv h_res h_wf h_fwf
        exact ih (acc.push annotatedExpr.unresolved) newEnv h h_newwf

/-- `resolve` preserves the full context when the input context is nonempty (the
    empty-init guard is a no-op). -/
theorem resolve_context_eq_of_ne (C : Core.Expression.TyContext) (Env Env' : Core.Expression.TyEnv)
    (e : Expression.Expr) (et : LExprT CoreLParams.mono)
    (h : Lambda.LExpr.resolve C Env e = .ok (et, Env'))
    (h_wf : TEnvWF (T := CoreLParams) Env)
    (h_ne : Env.context.types ≠ [])
    (h_fwf : FactoryWF C.functions) :
    Env'.context = Env.context := by
  unfold LExpr.resolve at h
  simp only [Bind.bind, Except.bind] at h
  have h_not_empty : Env.context.types.isEmpty = false := by
    cases hx : Env.context.types with
    | nil => exact absurd hx h_ne
    | cons _ _ => rfl
  rw [h_not_empty] at h
  simp only [Bool.false_eq_true, if_false] at h
  cases h_res : resolveAux C Env e with
  | error _ => rw [h_res] at h; simp only [reduceCtorEq] at h
  | ok v =>
    obtain ⟨et', Env_out⟩ := v
    rw [h_res] at h
    simp only [Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨_, h_env⟩ := h
    subst h_env
    exact (resolveAux_properties e et' C Env Env_out h_res h_ne
      h_wf.aliasesWF h_fwf h_wf.substFreshForGen h_wf.ctxFreshForGen h_wf.boundVarsFresh).context

/-- `typeCheckConditions.go` preserves the whole context (hence `types ≠ []`, `ContextMono`,
    `AliasesResolved`). -/
theorem typeCheckConditions_go_context (C : Core.Expression.TyContext) (procName : CoreIdent)
    (conds : List (CoreLabel × Core.Procedure.Check)) (acc : Array Expression.Expr)
    (Env : Core.Expression.TyEnv) (res : Array Expression.Expr × Core.Expression.TyEnv)
    (h : Core.Procedure.typeCheckConditions.go C procName conds acc Env = .ok res)
    (h_wf : TEnvWF (T := CoreLParams) Env)
    (h_ne : Env.context.types ≠ [])
    (h_fwf : FactoryWF C.functions) :
    res.2.context = Env.context := by
  induction conds generalizing acc Env with
  | nil =>
    simp only [Core.Procedure.typeCheckConditions.go] at h
    cases h; rfl
  | cons pair rest ih =>
    obtain ⟨name, condition⟩ := pair
    simp only [Core.Procedure.typeCheckConditions.go, Bind.bind, Except.bind,
      Except.mapError] at h
    cases h_res : Lambda.LExpr.resolve C Env condition.expr with
    | error e => rw [h_res] at h; simp only [reduceCtorEq] at h
    | ok v_res =>
      obtain ⟨annotatedExpr, newEnv⟩ := v_res
      rw [h_res] at h
      simp only at h
      split at h
      · simp only [reduceCtorEq] at h
      · have h_ctx : newEnv.context = Env.context :=
          resolve_context_eq_of_ne C Env newEnv condition.expr annotatedExpr h_res h_wf h_ne h_fwf
        have h_newwf : TEnvWF (T := CoreLParams) newEnv :=
          Lambda.resolve_TEnvWF condition.expr annotatedExpr C Env newEnv h_res h_wf h_fwf
        have h_newne : newEnv.context.types ≠ [] := by rw [h_ctx]; exact h_ne
        have h_rec := ih (acc.push annotatedExpr.unresolved) newEnv h h_newwf h_newne
        rw [h_rec, h_ctx]

/-- Top-level wrapper: `typeCheckConditions` preserves `TEnvWF`. -/
theorem typeCheckConditions_TEnvWF (C : Core.Expression.TyContext) (Env : Core.Expression.TyEnv)
    (conditions : ListMap CoreLabel Core.Procedure.Check) (procName : CoreIdent)
    (res : Array Expression.Expr × Core.Expression.TyEnv)
    (h : Core.Procedure.typeCheckConditions C Env conditions procName = .ok res)
    (h_wf : TEnvWF (T := CoreLParams) Env)
    (h_fwf : FactoryWF C.functions) :
    TEnvWF (T := CoreLParams) res.2 := by
  simp only [Core.Procedure.typeCheckConditions] at h
  exact typeCheckConditions_go_TEnvWF C procName conditions #[] Env res h h_wf h_fwf

/-- Top-level wrapper: `typeCheckConditions` preserves the whole context. -/
theorem typeCheckConditions_context (C : Core.Expression.TyContext) (Env : Core.Expression.TyEnv)
    (conditions : ListMap CoreLabel Core.Procedure.Check) (procName : CoreIdent)
    (res : Array Expression.Expr × Core.Expression.TyEnv)
    (h : Core.Procedure.typeCheckConditions C Env conditions procName = .ok res)
    (h_wf : TEnvWF (T := CoreLParams) Env)
    (h_ne : Env.context.types ≠ [])
    (h_fwf : FactoryWF C.functions) :
    res.2.context = Env.context := by
  simp only [Core.Procedure.typeCheckConditions] at h
  exact typeCheckConditions_go_context C procName conditions #[] Env res h h_wf h_ne h_fwf

/-- `setupInputEnv` preserves `TEnvWF`. -/
theorem setupInputEnv_TEnvWF (C : Core.Expression.TyContext) (Env : Core.Expression.TyEnv)
    (proc : Procedure) (fr : Strata.FileRange)
    (res : @Lambda.LMonoTySignature Unit × Core.Expression.TyEnv × Lambda.Subst)
    (h : Core.Procedure.setupInputEnv C Env proc fr = .ok res)
    (h_wf : TEnvWF (T := CoreLParams) Env) :
    TEnvWF (T := CoreLParams) res.2.1 := by
  simp only [Core.Procedure.setupInputEnv, Bind.bind, Except.bind, Except.mapError, pure,
    Except.pure] at h
  cases h_inst : Lambda.LMonoTySignature.instantiateWithSubst C Env.pushEmptyContext
      proc.header.typeArgs proc.header.inputs with
  | error e => rw [h_inst] at h; simp only [reduceCtorEq] at h
  | ok v =>
    obtain ⟨inp_mty_sig, Env₁, tyArgSubst⟩ := v
    rw [h_inst] at h
    simp only [Except.ok.injEq] at h
    subst h
    have h_push_wf : TEnvWF (T := CoreLParams) Env.pushEmptyContext :=
      TEnvWF.of_pushEmptyContext (T := CoreLParams) Env h_wf
    have h_inst_wf : TEnvWF (T := CoreLParams) Env₁ :=
      instantiateWithSubst_preserves_wf C Env.pushEmptyContext proc.header.typeArgs
        proc.header.inputs (inp_mty_sig, Env₁, tyArgSubst) h_inst h_push_wf
    have h_fresh := instantiateWithSubst_values_fresh C Env.pushEmptyContext proc.header.typeArgs
      proc.header.inputs (inp_mty_sig, Env₁, tyArgSubst) h_inst
    show TEnvWF (T := CoreLParams) (Env₁.addInNewestContext (Lambda.LMonoTySignature.toTrivialLTy inp_mty_sig))
    have h_eq : Lambda.LMonoTySignature.toTrivialLTy inp_mty_sig
        = inp_mty_sig.map (fun p => (p.1, LTy.forAll [] p.2)) := rfl
    rw [h_eq]
    exact TEnvWF.of_addInNewestContext_mono (T := CoreLParams) Env₁ inp_mty_sig h_inst_wf
      (fun p hp v hv n hn => h_fresh p.2 (by
        rw [ListMap.values_eq_map_snd]; exact List.mem_map_of_mem hp) v hv n hn)


/-- `setupInputEnv` preserves `AliasesResolved`: it only pushes an empty scope,
    instantiates (which preserves `.context`), and adds bindings in the newest scope. -/
theorem setupInputEnv_AliasesResolved (C : Core.Expression.TyContext) (Env : Core.Expression.TyEnv)
    (proc : Procedure) (fr : Strata.FileRange)
    (res : @Lambda.LMonoTySignature Unit × Core.Expression.TyEnv × Lambda.Subst)
    (h : Core.Procedure.setupInputEnv C Env proc fr = .ok res)
    (h_resolved : TContext.AliasesResolved Env.context) :
    TContext.AliasesResolved res.2.1.context := by
  simp only [Core.Procedure.setupInputEnv, Bind.bind, Except.bind, Except.mapError, pure,
    Except.pure] at h
  cases h_inst : Lambda.LMonoTySignature.instantiateWithSubst C Env.pushEmptyContext
      proc.header.typeArgs proc.header.inputs with
  | error e => rw [h_inst] at h; simp only [reduceCtorEq] at h
  | ok v =>
    obtain ⟨inp_mty_sig, Env₁, tyArgSubst⟩ := v
    rw [h_inst] at h
    simp only [Except.ok.injEq] at h
    subst h
    have h_push_resolved : TContext.AliasesResolved Env.pushEmptyContext.context :=
      TContext.AliasesResolved.of_pushEmptyContext (T := CoreLParams) Env h_resolved
    have h_ctx : Env₁.context = Env.pushEmptyContext.context :=
      instantiateWithSubst_preserves_context C Env.pushEmptyContext proc.header.typeArgs
        proc.header.inputs (inp_mty_sig, Env₁, tyArgSubst) h_inst
    have h_inst_resolved : TContext.AliasesResolved Env₁.context := by
      rw [h_ctx]; exact h_push_resolved
    show TContext.AliasesResolved
      (Env₁.addInNewestContext (Lambda.LMonoTySignature.toTrivialLTy inp_mty_sig)).context
    exact TContext.AliasesResolved.of_addInNewestContext (T := CoreLParams) Env₁
      (Lambda.LMonoTySignature.toTrivialLTy inp_mty_sig) h_inst_resolved

/-! ### Body-env WF cluster (postEnv_wf / procBodyEnv_wf) and
    the alias/nonempty preservation lemmas they and `noUndeclaredVars` rely on. -/

mutual
theorem LMonoTy_resolveAliases_env_local (mty : LMonoTy) (Env : Core.Expression.TyEnv)
    (mty' : LMonoTy) (Env' : Core.Expression.TyEnv)
    (h : LMonoTy.resolveAliases mty Env = .ok (mty', Env')) : Env' = Env := by
  match mty with
  | .ftvar _ =>
    simp only [LMonoTy.resolveAliases, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
    exact h.2.symm
  | .bitvec _ =>
    simp only [LMonoTy.resolveAliases, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
    exact h.2.symm
  | .tcons name args =>
    simp [LMonoTy.resolveAliases, Bind.bind, Except.bind] at h
    elim_err h
    rename_i v1 h_args
    obtain ⟨args', Env1⟩ := v1; simp at h h_args
    simp only [LMonoTy.tconsAliasSimple] at h
    split at h <;>
      (simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
       rw [← h.2]
       exact LMonoTys_resolveAliases_env_local args Env args' Env1 h_args)

/-- `LMonoTys.resolveAliases` leaves the environment unchanged. -/
theorem LMonoTys_resolveAliases_env_local (mtys : LMonoTys) (Env : Core.Expression.TyEnv)
    (mtys' : LMonoTys) (Env' : Core.Expression.TyEnv)
    (h : LMonoTys.resolveAliases mtys Env = .ok (mtys', Env')) : Env' = Env := by
  match mtys with
  | [] =>
    simp only [LMonoTys.resolveAliases, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
    exact h.2.symm
  | mty :: mrest =>
    simp [LMonoTys.resolveAliases, Bind.bind, Except.bind] at h
    elim_err h
    rename_i v1 h_hd
    obtain ⟨mty', Env1⟩ := v1; simp at h h_hd
    elim_err h
    rename_i v2 h_tl
    obtain ⟨mrest', Env2⟩ := v2
    simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
    rw [← h.2]
    rw [LMonoTys_resolveAliases_env_local mrest Env1 mrest' Env2 h_tl,
        LMonoTy_resolveAliases_env_local mty Env mty' Env1 h_hd]
end

/-- `addInNewestContext` keeps the type-scope stack non-empty. -/
theorem addInNewestContext_types_ne (Env : Core.Expression.TyEnv) (m : Map CoreLParams.Identifier LTy)
    (h : Env.context.types ≠ []) :
    (Env.addInNewestContext m).context.types ≠ [] := by
  simp only [TEnv.addInNewestContext, TEnv.updateContext, TEnv.context, Maps.addInNewest,
    Maps.push, Maps.pop]
  cases hx : Env.context.types with
  | nil => exact absurd hx h
  | cons a rest => simp

/-- `setupInputEnv` yields a nonempty `context.types`: it pushes an empty scope
    (making types a cons), instantiates (context unchanged), and adds bindings in
    the newest scope (preserves nonemptiness). -/
theorem setupInputEnv_types_ne (C : Core.Expression.TyContext) (Env : Core.Expression.TyEnv)
    (proc : Procedure) (fr : Strata.FileRange)
    (res : @Lambda.LMonoTySignature Unit × Core.Expression.TyEnv × Lambda.Subst)
    (h : Core.Procedure.setupInputEnv C Env proc fr = .ok res) :
    res.2.1.context.types ≠ [] := by
  simp only [Core.Procedure.setupInputEnv, Bind.bind, Except.bind, Except.mapError, pure,
    Except.pure] at h
  cases h_inst : Lambda.LMonoTySignature.instantiateWithSubst C Env.pushEmptyContext
      proc.header.typeArgs proc.header.inputs with
  | error e => rw [h_inst] at h; simp only [reduceCtorEq] at h
  | ok v =>
    obtain ⟨inp_mty_sig, Env₁, tyArgSubst⟩ := v
    rw [h_inst] at h
    simp only [Except.ok.injEq] at h
    subst h
    have h_ctx : Env₁.context = Env.pushEmptyContext.context :=
      instantiateWithSubst_preserves_context C Env.pushEmptyContext proc.header.typeArgs
        proc.header.inputs (inp_mty_sig, Env₁, tyArgSubst) h_inst
    have h_push_ne : Env.pushEmptyContext.context.types ≠ [] := by
      simp only [TEnv.pushEmptyContext, TEnv.updateContext, TEnv.context, Maps.push]
      exact List.cons_ne_nil _ _
    have h_env1_ne : Env₁.context.types ≠ [] := by rw [h_ctx]; exact h_push_ne
    show (Env₁.addInNewestContext (Lambda.LMonoTySignature.toTrivialLTy inp_mty_sig)).context.types ≠ []
    exact addInNewestContext_types_ne Env₁ _ h_env1_ne

/-- `typeCheckConditions` preserves `AliasesWF`. -/
theorem typeCheckConditions_AliasesWF (C : Core.Expression.TyContext) (Env : Core.Expression.TyEnv)
    (conditions : ListMap CoreLabel Core.Procedure.Check) (procName : CoreIdent)
    (res : Array Expression.Expr × Core.Expression.TyEnv)
    (h : Core.Procedure.typeCheckConditions C Env conditions procName = .ok res)
    (h_wf : TEnvWF (T := CoreLParams) Env)
    (h_ne : Env.context.types ≠ [])
    (h_fwf : FactoryWF C.functions) :
    TContext.AliasesWF res.2.context := by
  have h_ctx : res.2.context = Env.context :=
    typeCheckConditions_context C Env conditions procName res h h_wf h_ne h_fwf
  rw [h_ctx]
  exact h_wf.aliasesWF

/-- `AliasesWF` is preserved through `setupInputEnv` (aliases unchanged from `Env`). -/
theorem setupInputEnv_AliasesWF (C : Core.Expression.TyContext) (Env : Core.Expression.TyEnv)
    (proc : Procedure) (fr : Strata.FileRange)
    (res : @Lambda.LMonoTySignature Unit × Core.Expression.TyEnv × Lambda.Subst)
    (h : Core.Procedure.setupInputEnv C Env proc fr = .ok res)
    (h_wf : TEnvWF (T := CoreLParams) Env) :
    TContext.AliasesWF res.2.1.context := by
  simp only [Core.Procedure.setupInputEnv, Bind.bind, Except.bind, Except.mapError, pure,
    Except.pure] at h
  cases h_inst : Lambda.LMonoTySignature.instantiateWithSubst C Env.pushEmptyContext
      proc.header.typeArgs proc.header.inputs with
  | error e => rw [h_inst] at h; simp only [reduceCtorEq] at h
  | ok v =>
    obtain ⟨inp_mty_sig, Env₁, tyArgSubst⟩ := v
    rw [h_inst] at h
    simp only [Except.ok.injEq] at h
    subst h
    have h_push_aw : TContext.AliasesWF Env.pushEmptyContext.context :=
      (TEnvWF.of_pushEmptyContext (T := CoreLParams) Env h_wf).aliasesWF
    have h_ctx : Env₁.context = Env.pushEmptyContext.context :=
      instantiateWithSubst_preserves_context C Env.pushEmptyContext proc.header.typeArgs
        proc.header.inputs (inp_mty_sig, Env₁, tyArgSubst) h_inst
    have h_inst_aw : TContext.AliasesWF Env₁.context := by
      rw [h_ctx]; exact h_push_aw
    show TContext.AliasesWF
      (Env₁.addInNewestContext (Lambda.LMonoTySignature.toTrivialLTy inp_mty_sig)).context
    have h_aliases : (Env₁.addInNewestContext
        (Lambda.LMonoTySignature.toTrivialLTy inp_mty_sig)).context.aliases
        = Env₁.context.aliases := rfl
    simp only [TContext.AliasesWF, h_aliases]
    exact h_inst_aw

/-- `AliasesWF` at the pre-condition-checked env (`v_pre.2`), the form the `noUndeclaredVars`
    call site needs. -/
theorem pre_env_AliasesWF
    (C : Core.Expression.TyContext) (Env : Core.Expression.TyEnv)
    (proc : Procedure) (fr : Strata.FileRange)
    (v_setup : @Lambda.LMonoTySignature Unit × Core.Expression.TyEnv × Lambda.Subst)
    (v_pre : Array Expression.Expr × Core.Expression.TyEnv)
    (h_setup : Core.Procedure.setupInputEnv C Env proc fr = .ok v_setup)
    (h_pre : Core.Procedure.typeCheckConditions C v_setup.2.fst
      proc.spec.preconditions proc.header.name = .ok v_pre)
    (h_wf : TEnvWF (T := CoreLParams) Env)
    (h_fwf : FactoryWF C.functions) :
    TContext.AliasesWF v_pre.snd.context :=
  typeCheckConditions_AliasesWF C v_setup.2.fst proc.spec.preconditions proc.header.name v_pre h_pre
    (setupInputEnv_TEnvWF C Env proc fr v_setup h_setup h_wf)
    (setupInputEnv_types_ne C Env proc fr v_setup h_setup)
    h_fwf


/-- Both facts from a successful `checkTypeArgsWF`: typeArgs are `Nodup`, and every free
    var of the input/output signature is declared in `typeArgs`. -/
theorem checkTypeArgsWF_props (proc : Procedure) (fr : Strata.FileRange) (v : Unit)
    (h : proc.checkTypeArgsWF fr = .ok v) :
    proc.header.typeArgs.Nodup ∧
    (∀ x, x ∈ (LMonoTys.freeVars proc.header.inputs.values ++
               LMonoTys.freeVars proc.header.outputs.values) → x ∈ proc.header.typeArgs) ∧
    (∀ ta, ta ∈ proc.header.typeArgs →
      ¬ Lambda.TState.tyPrefix.toList.isPrefixOf ta.toList) := by
  unfold Procedure.checkTypeArgsWF at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  split at h
  · simp at h
  · rename_i h_nodup
    split at h
    · simp at h
    · rename_i h_genpfx
      split at h
      · simp at h
      · rename_i h_undecl
        have h_nd : proc.header.typeArgs.Nodup := by
          simp only [Bool.not_eq_true, Bool.not_eq_false', decide_eq_true_eq] at h_nodup
          exact h_nodup
        refine ⟨h_nd, ?_, ?_⟩
        · have h_empty : (LMonoTys.freeVars proc.header.inputs.values ++
              LMonoTys.freeVars proc.header.outputs.values).eraseDups.filter
              (fun y => decide ¬ y ∈ proc.header.typeArgs) = [] := by
            simp only [Bool.not_eq_true, Bool.not_eq_false', List.isEmpty_iff] at h_undecl
            exact h_undecl
          intro x hx
          have h_all := List.filter_eq_nil_iff.mp h_empty
          have h_mem_ed : x ∈ (LMonoTys.freeVars proc.header.inputs.values ++
              LMonoTys.freeVars proc.header.outputs.values).eraseDups :=
            List.mem_eraseDups.mpr hx
          have h_dec := h_all x h_mem_ed
          simpa using h_dec
        · -- No typeArg carries the reserved gen prefix (from the `genPrefixArgs` guard).
          have h_empty : proc.header.typeArgs.filter
              (fun ta => Lambda.TState.tyPrefix.toList.isPrefixOf ta.toList) = [] := by
            simp only [Bool.not_eq_true, Bool.not_eq_false', List.isEmpty_iff] at h_genpfx
            exact h_genpfx
          intro ta hta
          have h_all := List.filter_eq_nil_iff.mp h_empty ta hta
          simpa using h_all


/-! ### Freshness lemmas for `postEnv_wf`'s two `of_addInNewestContext_mono` obligations. -/

/-- A list is a prefix of itself appended with anything. -/
private theorem list_isPrefixOf_append_left {α} [BEq α] [LawfulBEq α] (xs ys : List α) :
    xs.isPrefixOf (xs ++ ys) = true := by
  induction xs with
  | nil => simp [List.isPrefixOf]
  | cons a rest ih =>
    simp only [List.cons_append, List.isPrefixOf, beq_self_eq_true, Bool.true_and]; exact ih

/-- A name that is not gen-prefixed cannot equal any `tyPrefix ++ toString n`. -/
private theorem not_prefix_ne_gen (ta : String)
    (h : ¬ Lambda.TState.tyPrefix.toList.isPrefixOf ta.toList) :
    ∀ n : Nat, ta ≠ Lambda.TState.tyPrefix ++ toString n := by
  intro n heq
  apply h
  rw [heq, String.toList_append]
  exact list_isPrefixOf_append_left _ _

/-- Shape and freshness of `setupInputEnv`'s substitution: it is a single scope mapping
    the type args to distinct, gen-fresh, gen-prefixed fresh variables. -/
theorem setupInputEnv_shape_fresh
    (C : Core.Expression.TyContext) (Env : Core.Expression.TyEnv)
    (proc : Procedure) (fr : Strata.FileRange)
    (v_setup : @Lambda.LMonoTySignature Unit × Core.Expression.TyEnv × Lambda.Subst)
    (h_setup : Core.Procedure.setupInputEnv C Env proc fr = .ok v_setup) :
    ∃ freshtvs : List TyIdentifier,
      freshtvs.length = proc.header.typeArgs.length ∧
      v_setup.2.snd = [proc.header.typeArgs.zip (freshtvs.map LMonoTy.ftvar)] ∧
      (∀ tv, tv ∈ freshtvs →
        ∀ n, n ≥ v_setup.2.fst.genEnv.genState.tyGen → tv ≠ TState.tyPrefix ++ toString n) ∧
      freshtvs.Nodup ∧
      (∀ tv, tv ∈ freshtvs → ∃ k : Nat, tv = TState.tyPrefix ++ toString k) := by
  simp only [Core.Procedure.setupInputEnv, Bind.bind, Except.bind, Except.mapError, pure,
    Except.pure] at h_setup
  cases h_inst : Lambda.LMonoTySignature.instantiateWithSubst C Env.pushEmptyContext
      proc.header.typeArgs proc.header.inputs with
  | error e => rw [h_inst] at h_setup; simp only [reduceCtorEq] at h_setup
  | ok v =>
    obtain ⟨inp_mty_sig, Env₁, tyArgSubst⟩ := v
    rw [h_inst] at h_setup
    simp only [Except.ok.injEq] at h_setup
    subst h_setup
    simp only [Lambda.LMonoTySignature.instantiateWithSubst, Bind.bind, Except.bind] at h_inst
    elim_err h_inst with v_env h_env; obtain ⟨mtys, Env_e, S⟩ := v_env
    elim_err h_inst with v_go h_go; obtain ⟨newtys, Env₂⟩ := v_go
    simp only [Except.ok.injEq, Prod.mk.injEq] at h_inst
    obtain ⟨h_sig, h_env2, h_S2⟩ := h_inst
    obtain ⟨freshtvs, genEnv', h_gen, _, h_S, _, h_genEnv⟩ :=
      instantiateEnvWithSubst_decompose proc.header.typeArgs (ListMap.values proc.header.inputs)
        Env.pushEmptyContext (mtys, Env_e, S) h_env
    simp only at h_S h_genEnv
    refine ⟨freshtvs, ?_len, ?_shape, ?_fresh, ?_nodup, ?_gennamed⟩
    case _nodup =>
      exact genTyVars_nodup _ _ _ _ h_gen
    case _gennamed =>
      intro tv h_tv
      obtain ⟨k, _, h_k⟩ := TGenEnv.genTyVars_is_genName _ _ _ _ h_gen tv h_tv
      exact ⟨k, h_k⟩
    case _len =>
      exact TGenEnv.genTyVars_length proc.header.typeArgs.length Env.pushEmptyContext.genEnv
        freshtvs genEnv' h_gen
    case _shape =>
      show tyArgSubst = _
      rw [← h_S2]; exact h_S
    case _fresh =>
      show ∀ tv, tv ∈ freshtvs →
        ∀ n, n ≥ (inp_mty_sig, Env₁.addInNewestContext
          (Lambda.LMonoTySignature.toTrivialLTy inp_mty_sig), tyArgSubst).2.1.genEnv.genState.tyGen →
          tv ≠ TState.tyPrefix ++ toString n
      intro tv h_tv n hn
      have h_gen_add : (Env₁.addInNewestContext
          (Lambda.LMonoTySignature.toTrivialLTy inp_mty_sig)).genEnv.genState = Env₁.genEnv.genState := rfl
      have h_env1_eq : Env₁ = Env₂ := by rw [← h_env2]
      have h_go_mono : Env₂.genEnv.genState.tyGen ≥ Env_e.genEnv.genState.tyGen :=
        instantiateWithSubst_go_genState_mono C _ Env_e (newtys, Env₂) h_go
      have h_ene_gen : Env_e.genEnv = genEnv' := h_genEnv
      have h_gf : ∀ tv', tv' ∈ freshtvs →
          ∀ m, m ≥ genEnv'.genState.tyGen → tv' ≠ TState.tyPrefix ++ toString m :=
        genTyVars_genFresh' (T := CoreLParams) proc.header.typeArgs.length Env.pushEmptyContext.genEnv
          freshtvs genEnv' h_gen
      simp only [h_gen_add] at hn
      have h_n_gen : n ≥ genEnv'.genState.tyGen := by
        rw [h_env1_eq] at hn
        rw [h_ene_gen] at h_go_mono
        omega
      exact h_gf tv h_tv n h_n_gen

/-- `typeCheckConditions.go` never decreases the gen counter. -/
theorem typeCheckConditions_go_genState_mono
    (C : Core.Expression.TyContext) (procName : CoreIdent)
    (conds : List (CoreLabel × Core.Procedure.Check)) (acc : Array Expression.Expr)
    (Env : Core.Expression.TyEnv) (res : Array Expression.Expr × Core.Expression.TyEnv)
    (h : Core.Procedure.typeCheckConditions.go C procName conds acc Env = .ok res)
    (h_wf : TEnvWF (T := CoreLParams) Env)
    (h_ne : Env.context.types ≠ [])
    (h_fwf : FactoryWF C.functions) :
    res.2.genEnv.genState.tyGen ≥ Env.genEnv.genState.tyGen := by
  induction conds generalizing acc Env with
  | nil =>
    simp only [Core.Procedure.typeCheckConditions.go] at h
    cases h; exact Nat.le_refl _
  | cons pair rest ih =>
    obtain ⟨name, condition⟩ := pair
    simp only [Core.Procedure.typeCheckConditions.go, Bind.bind, Except.bind,
      Except.mapError] at h
    cases h_res : Lambda.LExpr.resolve C Env condition.expr with
    | error e => rw [h_res] at h; simp only [reduceCtorEq] at h
    | ok v_res =>
      obtain ⟨annotatedExpr, newEnv⟩ := v_res
      rw [h_res] at h
      simp only at h
      split at h
      · simp only [reduceCtorEq] at h
      · have h_step : newEnv.genEnv.genState.tyGen ≥ Env.genEnv.genState.tyGen :=
          resolve_genState_mono C Env newEnv condition.expr annotatedExpr h_res h_wf h_fwf
        have h_ctx : newEnv.context = Env.context :=
          resolve_context_eq_of_ne C Env newEnv condition.expr annotatedExpr h_res h_wf h_ne h_fwf
        have h_newwf : TEnvWF (T := CoreLParams) newEnv :=
          Lambda.resolve_TEnvWF condition.expr annotatedExpr C Env newEnv h_res h_wf h_fwf
        have h_newne : newEnv.context.types ≠ [] := by rw [h_ctx]; exact h_ne
        have h_rec := ih (acc.push annotatedExpr.unresolved) newEnv h h_newwf h_newne
        omega

/-- `typeCheckConditions` never decreases the gen counter. -/
theorem typeCheckConditions_genState_mono
    (C : Core.Expression.TyContext) (Env : Core.Expression.TyEnv)
    (conditions : ListMap CoreLabel Core.Procedure.Check) (procName : CoreIdent)
    (res : Array Expression.Expr × Core.Expression.TyEnv)
    (h : Core.Procedure.typeCheckConditions C Env conditions procName = .ok res)
    (h_wf : TEnvWF (T := CoreLParams) Env)
    (h_ne : Env.context.types ≠ [])
    (h_fwf : FactoryWF C.functions) :
    res.2.genEnv.genState.tyGen ≥ Env.genEnv.genState.tyGen := by
  simp only [Core.Procedure.typeCheckConditions] at h
  exact typeCheckConditions_go_genState_mono C procName conditions #[] Env res h h_wf h_ne h_fwf

/-- `List.map LMonoTy.ftvar` is injective (ftvar is a constructor). -/
private theorem map_ftvar_inj : ∀ (xs ys : List TyIdentifier),
    List.map LMonoTy.ftvar xs = List.map LMonoTy.ftvar ys → xs = ys := by
  intro xs
  induction xs with
  | nil => intro ys h; cases ys with | nil => rfl | cons b bs => simp at h
  | cons a as ih =>
    intro ys h
    cases ys with
    | nil => simp at h
    | cons b bs =>
      simp only [List.map_cons, List.cons.injEq, LMonoTy.ftvar.injEq] at h
      obtain ⟨h1, h2⟩ := h
      rw [h1, ih bs h2]

/-- The `instantiateWithSubst.go` loop, applied to `forAll []`-wrapped monotypes,
    does not grow free variables (each output is `resolveAliases` of the input mono
    type, which is non-growing under `AliasesWF`). -/
private theorem go_freeVars_subset (C : LContext CoreLParams) (mtys : LMonoTys) :
    ∀ (Env : TEnv Unit) (newtys : LMonoTys) (Env_out : TEnv Unit),
      LMonoTySignature.instantiateWithSubst.go C Env
          (mtys.map (fun m => LTy.forAll [] m)) = .ok (newtys, Env_out) →
      TContext.AliasesWF Env.context →
      ∀ w, w ∈ LMonoTys.freeVars newtys → w ∈ LMonoTys.freeVars mtys := by
  induction mtys with
  | nil =>
    intro Env newtys Env_out h _ w hw
    simp only [List.map_nil, LMonoTySignature.instantiateWithSubst.go,
      Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨h1, _⟩ := h; subst h1
    simp only [LMonoTys.freeVars, List.not_mem_nil] at hw
  | cons m mrest ih =>
    intro Env newtys Env_out h h_aw w hw
    simp only [List.map_cons, LMonoTySignature.instantiateWithSubst.go,
      Bind.bind, Except.bind] at h
    elim_err h with v1 h_iwc; obtain ⟨mt, Env_mid⟩ := v1
    elim_err h with v2 h_rest; obtain ⟨mtrest, Env_end⟩ := v2
    simp only [Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨h_nt, _⟩ := h; subst h_nt
    rw [LMonoTys.freeVars_of_cons] at hw
    rw [LMonoTys.freeVars_of_cons, List.mem_append]
    rw [List.mem_append] at hw
    cases hw with
    | inl hw_hd =>
      obtain ⟨Env'', h_ra⟩ :=
        instantiateWithCheck_forAll_nil_resolveAliases m C Env Env_mid mt h_iwc
      left
      exact LMonoTy_resolveAliases_freeVars_subset (T := CoreLParams) m Env mt Env'' h_ra h_aw w hw_hd
    | inr hw_tl =>
      right
      have h_ctx : Env_mid.context = Env.context :=
        LTy_instantiateWithCheck_context' (LTy.forAll [] m) C Env mt Env_mid h_iwc
      exact ih Env_mid mtrest Env_end h_rest (h_ctx ▸ h_aw) w hw_tl

/-- If `sig.values` is closed under `typeArgs`, then every free var of the
    `instantiateWithSubst` output values is in `freshtvs`. -/
private theorem instantiateWithSubst_values_freeVars_closed
    (C : LContext CoreLParams) (Env : TEnv Unit)
    (typeArgs freshtvs : List TyIdentifier) (sig : @LMonoTySignature Unit)
    (inp_mty_sig : @LMonoTySignature Unit) (Env₂ : TEnv Unit) (S : Subst)
    (h : LMonoTySignature.instantiateWithSubst C Env typeArgs sig
        = .ok (inp_mty_sig, Env₂, S))
    (h_aw : TContext.AliasesWF Env.context)
    (h_len : freshtvs.length = typeArgs.length)
    (h_S : S = [typeArgs.zip (freshtvs.map LMonoTy.ftvar)])
    (h_closed : ∀ x, x ∈ LMonoTys.freeVars (ListMap.values sig) → x ∈ typeArgs) :
    ∀ w, w ∈ LMonoTys.freeVars (ListMap.values inp_mty_sig) → w ∈ freshtvs := by
  intro w hw
  simp only [LMonoTySignature.instantiateWithSubst, Bind.bind, Except.bind] at h
  elim_err h with v_env h_env; obtain ⟨mtys, Env_e, S'⟩ := v_env
  elim_err h with v_go h_go; obtain ⟨newtys, Env₂'⟩ := v_go
  simp only [Except.ok.injEq, Prod.mk.injEq] at h
  obtain ⟨h_sig, h_env2, h_S'⟩ := h
  have h_sub : ListMap.values inp_mty_sig ⊆ newtys := by
    rw [← h_sig, ListMap.values_eq_map_snd]
    exact (List.map_snd_zip_sublist (ListMap.keys sig) newtys).subset
  have hw_new : w ∈ LMonoTys.freeVars newtys := by
    obtain ⟨elt, h_elt, h_v⟩ := LMonoTys.freeVars_exists hw
    exact LMonoTys.freeVars_mem_subset (h_sub h_elt) h_v
  obtain ⟨freshtvs', genEnv', h_gen, h_mtys, h_S'eq, h_ctx, _⟩ :=
    instantiateEnvWithSubst_decompose typeArgs (ListMap.values sig) Env (mtys, Env_e, S') h_env
  simp only at h_mtys h_S'eq h_ctx
  have h_aw_e : TContext.AliasesWF Env_e.context := h_ctx ▸ h_aw
  have h_go' : LMonoTySignature.instantiateWithSubst.go C Env_e
      (mtys.map (fun m => LTy.forAll [] m)) = .ok (newtys, Env₂') := h_go
  have hw_mtys : w ∈ LMonoTys.freeVars mtys :=
    go_freeVars_subset C mtys Env_e newtys Env₂' h_go' h_aw_e w hw_new
  -- `freshtvs' = freshtvs` since the two substitution scopes agree and `map ftvar` is injective.
  have h_flen' : freshtvs'.length = typeArgs.length :=
    TGenEnv.genTyVars_length typeArgs.length Env.genEnv freshtvs' genEnv' h_gen
  have h_zip_eq : typeArgs.zip (List.map LMonoTy.ftvar freshtvs')
      = typeArgs.zip (List.map LMonoTy.ftvar freshtvs) := by
    have h_cons : [typeArgs.zip (List.map LMonoTy.ftvar freshtvs')]
        = [typeArgs.zip (List.map LMonoTy.ftvar freshtvs)] := by
      rw [← h_S'eq, h_S', h_S]
    exact List.head_eq_of_cons_eq h_cons
  have h_map_eq : List.map LMonoTy.ftvar freshtvs' = List.map LMonoTy.ftvar freshtvs := by
    have e1 : List.map Prod.snd (typeArgs.zip (List.map LMonoTy.ftvar freshtvs'))
        = List.map LMonoTy.ftvar freshtvs' :=
      List.map_snd_zip (by rw [List.length_map]; exact Nat.le_of_eq h_flen')
    have e2 : List.map Prod.snd (typeArgs.zip (List.map LMonoTy.ftvar freshtvs))
        = List.map LMonoTy.ftvar freshtvs :=
      List.map_snd_zip (by rw [List.length_map]; exact Nat.le_of_eq h_len)
    rw [← e1, ← e2, h_zip_eq]
  have h_fresh_eq : freshtvs' = freshtvs := map_ftvar_inj freshtvs' freshtvs h_map_eq
  subst h_fresh_eq
  rw [h_mtys] at hw_mtys
  exact LMonoTys.freeVars_subst_closed typeArgs freshtvs' h_flen'
    (ListMap.values sig) h_closed w hw_mtys


/-- Setup-level closedness: from `setupInputEnv = ok v_setup` with `S`-shape
    `[typeArgs.zip (freshtvs.map ftvar)]` and inputs closed under `typeArgs`, the
    input signature `v_setup.fst`'s free vars all land in `freshtvs`. -/
private theorem setupInputEnv_values_closed
    (C : Core.Expression.TyContext) (Env : Core.Expression.TyEnv)
    (proc : Procedure) (fr : Strata.FileRange)
    (v_setup : @Lambda.LMonoTySignature Unit × Core.Expression.TyEnv × Lambda.Subst)
    (freshtvs : List TyIdentifier)
    (h_setup : Core.Procedure.setupInputEnv C Env proc fr = .ok v_setup)
    (h_wf : TEnvWF (T := CoreLParams) Env)
    (h_len : freshtvs.length = proc.header.typeArgs.length)
    (h_S : v_setup.2.snd = [proc.header.typeArgs.zip (freshtvs.map LMonoTy.ftvar)])
    (h_closed : ∀ x, x ∈ LMonoTys.freeVars (ListMap.values proc.header.inputs) →
      x ∈ proc.header.typeArgs) :
    ∀ w, w ∈ LMonoTys.freeVars (ListMap.values v_setup.fst) → w ∈ freshtvs := by
  simp only [Core.Procedure.setupInputEnv, Bind.bind, Except.bind, Except.mapError, pure,
    Except.pure] at h_setup
  cases h_inst : Lambda.LMonoTySignature.instantiateWithSubst C Env.pushEmptyContext
      proc.header.typeArgs proc.header.inputs with
  | error e => rw [h_inst] at h_setup; simp only [reduceCtorEq] at h_setup
  | ok v =>
    obtain ⟨inp_mty_sig, Env₁, tyArgSubst⟩ := v
    rw [h_inst] at h_setup
    simp only [Except.ok.injEq] at h_setup
    subst h_setup
    have h_push_aw : TContext.AliasesWF Env.pushEmptyContext.context :=
      (TEnvWF.of_pushEmptyContext (T := CoreLParams) Env h_wf).aliasesWF
    exact instantiateWithSubst_values_freeVars_closed C Env.pushEmptyContext
      proc.header.typeArgs freshtvs proc.header.inputs inp_mty_sig Env₁ tyArgSubst
      h_inst h_push_aw h_len h_S h_closed

/-- The resolved-substituted output signature values are gen-fresh for the output state. -/
theorem output_sig_values_fresh
    (C : Core.Expression.TyContext) (Env : Core.Expression.TyEnv)
    (proc : Procedure) (fr : Strata.FileRange)
    (v_setup : @Lambda.LMonoTySignature Unit × Core.Expression.TyEnv × Lambda.Subst)
    (v_pre : Array Expression.Expr × Core.Expression.TyEnv)
    (v_out : Lambda.LMonoTys × Core.Expression.TyEnv)
    (h_ta : proc.checkTypeArgsWF fr = .ok ())
    (h_setup : Core.Procedure.setupInputEnv C Env proc fr = .ok v_setup)
    (h_pre : Core.Procedure.typeCheckConditions C v_setup.2.1 proc.spec.preconditions
      proc.header.name = .ok v_pre)
    (h_ra : Lambda.LMonoTys.resolveAliases
      (proc.header.outputs.values.map (Lambda.LMonoTy.subst v_setup.2.2)) v_pre.2 = .ok v_out)
    (h_wf : TEnvWF (T := CoreLParams) Env)
    (h_fwf : FactoryWF C.functions)
    (h_aw : TContext.AliasesWF v_pre.2.context) :
    ∀ p ∈ proc.header.outputs.keys.zip v_out.1, ∀ v ∈ LMonoTy.freeVars p.2,
      ∀ n, n ≥ v_out.2.genEnv.genState.tyGen → v ≠ TState.tyPrefix ++ toString n := by
  obtain ⟨freshtvs, h_len, h_S, h_fresh_setup, _, _⟩ :=
    setupInputEnv_shape_fresh C Env proc fr v_setup h_setup
  have h_vout_env : v_out.2 = v_pre.2 :=
    LMonoTys_resolveAliases_env_local _ v_pre.2 v_out.1 v_out.2 h_ra
  have h_ta_props := checkTypeArgsWF_props proc fr () h_ta
  intro p hp v hv n hn
  have hp_snd : p.2 ∈ v_out.1 := (List.of_mem_zip hp).2
  -- Every free var of an output value is a fresh var (`freeVars ⊆ freshtvs`).
  have h_v_fresh : v ∈ freshtvs := by
    have hw_list : v ∈ LMonoTys.freeVars v_out.1 := LMonoTys.freeVars_mem_subset hp_snd hv
    have hw_pre : v ∈ LMonoTys.freeVars
        (List.map (LMonoTy.subst v_setup.2.snd) (ListMap.values proc.header.outputs)) :=
      LMonoTys_resolveAliases_freeVars_subset (T := CoreLParams)
        (List.map (LMonoTy.subst v_setup.2.snd) (ListMap.values proc.header.outputs))
        v_pre.2 v_out.1 v_out.2 h_ra h_aw v hw_list
    rw [← LMonoTys_subst_eq_map, h_S] at hw_pre
    have h_out_closed : ∀ tv, tv ∈ LMonoTys.freeVars (ListMap.values proc.header.outputs) →
        tv ∈ proc.header.typeArgs := fun tv htv => h_ta_props.2.1 tv (List.mem_append_right _ htv)
    exact LMonoTys.freeVars_subst_closed proc.header.typeArgs freshtvs h_len
      (ListMap.values proc.header.outputs) h_out_closed v hw_pre
  have h_setup_wf : TEnvWF (T := CoreLParams) v_setup.2.1 :=
    setupInputEnv_TEnvWF C Env proc fr v_setup h_setup h_wf
  have h_setup_ne : v_setup.2.1.context.types ≠ [] :=
    setupInputEnv_types_ne C Env proc fr v_setup h_setup
  have h_gen_pre : v_pre.2.genEnv.genState.tyGen ≥ v_setup.2.1.genEnv.genState.tyGen :=
    typeCheckConditions_genState_mono C v_setup.2.1 proc.spec.preconditions proc.header.name v_pre
      h_pre h_setup_wf h_setup_ne h_fwf
  have h_n_setup : n ≥ v_setup.2.1.genEnv.genState.tyGen := by
    rw [h_vout_env] at hn; omega
  exact h_fresh_setup v h_v_fresh n h_n_setup

/-! ### Old-inout binding freshness -/

theorem oldInout_bindings_fresh
    (C : Core.Expression.TyContext) (Env : Core.Expression.TyEnv)
    (proc : Procedure) (fr : Strata.FileRange)
    (v_setup : @Lambda.LMonoTySignature Unit × Core.Expression.TyEnv × Lambda.Subst)
    (v_pre : Array Expression.Expr × Core.Expression.TyEnv)
    (v_out : Lambda.LMonoTys × Core.Expression.TyEnv)
    (envWithOutputs : Core.Expression.TyEnv)
    (h_ta : proc.checkTypeArgsWF fr = .ok ())
    (h_setup : Core.Procedure.setupInputEnv C Env proc fr = .ok v_setup)
    (h_pre : Core.Procedure.typeCheckConditions C v_setup.2.1 proc.spec.preconditions
      proc.header.name = .ok v_pre)
    (h_ra : Lambda.LMonoTys.resolveAliases
      (proc.header.outputs.values.map (Lambda.LMonoTy.subst v_setup.2.2)) v_pre.2 = .ok v_out)
    (h_wf : TEnvWF (T := CoreLParams) Env)
    (h_fwf : FactoryWF C.functions)
    (h_gen : envWithOutputs.genEnv.genState.tyGen ≥ v_setup.2.1.genEnv.genState.tyGen) :
    ∀ p ∈ (v_setup.1.filter (fun x => (ListMap.keys proc.header.outputs).contains x.1)).map
        (fun (x : CoreIdent × LMonoTy) => (CoreIdent.mkOld x.1.name, x.2)),
      ∀ v ∈ LMonoTy.freeVars p.2,
      ∀ n, n ≥ envWithOutputs.genEnv.genState.tyGen → v ≠ TState.tyPrefix ++ toString n := by
  obtain ⟨freshtvs, h_len, h_S, h_fresh_setup, _, _⟩ :=
    setupInputEnv_shape_fresh C Env proc fr v_setup h_setup
  have h_ta_props := checkTypeArgsWF_props proc fr () h_ta
  intro p hp v hv n hn
  rw [List.mem_map] at hp
  obtain ⟨x, hx_mem, hx_eq⟩ := hp
  have hp2 : p.2 = x.2 := by rw [← hx_eq]
  rw [hp2] at hv
  have hx_setup := (List.mem_filter.mp hx_mem).1
  have hx2_val : x.2 ∈ ListMap.values v_setup.1 := by
    rw [ListMap.values_eq_map_snd, List.mem_map]
    exact ⟨x, hx_setup, rfl⟩
  have h_v_fresh : v ∈ freshtvs :=
    setupInputEnv_values_closed C Env proc fr v_setup freshtvs h_setup h_wf h_len h_S
      (fun tv htv => h_ta_props.2.1 tv (List.mem_append_left _ htv)) v
      (LMonoTys.freeVars_mem_subset hx2_val hv)
  exact h_fresh_setup v h_v_fresh n (by omega)

/-- The body environment after adding outputs and old-inout bindings (`E4`) is well-formed:
    `TEnvWF`, non-empty type-scope, and `AliasesResolved`. -/
theorem postEnv_wf (C : Core.Expression.TyContext) (Env : Core.Expression.TyEnv)
    (proc : Procedure) (fr : Strata.FileRange)
    (v_setup : @Lambda.LMonoTySignature Unit × Core.Expression.TyEnv × Lambda.Subst)
    (v_pre : Array Expression.Expr × Core.Expression.TyEnv)
    (v_out : Lambda.LMonoTys × Core.Expression.TyEnv)
    (h_ta : proc.checkTypeArgsWF fr = .ok ())
    (h_setup : Core.Procedure.setupInputEnv C Env proc fr = .ok v_setup)
    (h_pre : Core.Procedure.typeCheckConditions C v_setup.2.1 proc.spec.preconditions
      proc.header.name = .ok v_pre)
    (h_ra : Lambda.LMonoTys.resolveAliases
      (proc.header.outputs.values.map (Lambda.LMonoTy.subst v_setup.2.2)) v_pre.2 = .ok v_out)
    (h_wf : TEnvWF (T := CoreLParams) Env)
    (h_fwf : FactoryWF C.functions)
    (h_resolved : TContext.AliasesResolved Env.context) :
    let out_mty_sig : @Lambda.LMonoTySignature Unit := proc.header.outputs.keys.zip v_out.1
    let out_lty_sig := Lambda.LMonoTySignature.toTrivialLTy out_mty_sig
    let envWithOutputs := Lambda.TEnv.addInNewestContext (T := CoreLParams) v_out.2 out_lty_sig
    let oldInoutBindings : List (CoreIdent × Lambda.LTy) :=
      (v_setup.1.filter fun (id, _) => (ListMap.keys proc.header.outputs).contains id).map
        fun (id, ty) => (CoreIdent.mkOld id.name, .forAll [] ty)
    let E4 := Lambda.TEnv.addInNewestContext (T := CoreLParams) envWithOutputs oldInoutBindings
    TEnvWF (T := CoreLParams) E4 ∧
    E4.context.types ≠ [] ∧
    TContext.AliasesResolved E4.context := by
  intro out_mty_sig out_lty_sig envWithOutputs oldInoutBindings E4
  have h_vout_env : v_out.2 = v_pre.2 :=
    LMonoTys_resolveAliases_env_local _ v_pre.2 v_out.1 v_out.2 h_ra
  have h_setup_wf : TEnvWF (T := CoreLParams) v_setup.2.1 :=
    setupInputEnv_TEnvWF C Env proc fr v_setup h_setup h_wf
  have h_setup_res : TContext.AliasesResolved v_setup.2.1.context :=
    setupInputEnv_AliasesResolved C Env proc fr v_setup h_setup h_resolved
  have h_setup_ne : v_setup.2.1.context.types ≠ [] :=
    setupInputEnv_types_ne C Env proc fr v_setup h_setup
  have h_pre_wf : TEnvWF (T := CoreLParams) v_pre.2 :=
    typeCheckConditions_TEnvWF C v_setup.2.1 proc.spec.preconditions proc.header.name v_pre h_pre
      h_setup_wf h_fwf
  have h_pre_ctx : v_pre.2.context = v_setup.2.1.context :=
    typeCheckConditions_context C v_setup.2.1 proc.spec.preconditions proc.header.name v_pre h_pre
      h_setup_wf h_setup_ne h_fwf
  have h_pre_res : TContext.AliasesResolved v_pre.2.context := by rw [h_pre_ctx]; exact h_setup_res
  have h_pre_ne : v_pre.2.context.types ≠ [] := by rw [h_pre_ctx]; exact h_setup_ne
  refine ⟨?_tenvwf, ?_types_ne, ?_resolved⟩
  case _tenvwf =>
    show TEnvWF (T := CoreLParams) E4
    -- `envWithOutputs = addInNewestContext v_out.2 (toTrivialLTy out_mty_sig)`, and the bindings
    -- are all `.forAll [] _`, so `of_addInNewestContext_mono` applies.
    have h_out_eq : out_lty_sig = out_mty_sig.map (fun p => (p.1, LTy.forAll [] p.2)) := rfl
    have h_envWithOutputs_wf : TEnvWF (T := CoreLParams) envWithOutputs := by
      show TEnvWF (T := CoreLParams) (Lambda.TEnv.addInNewestContext (T := CoreLParams) v_out.2 out_lty_sig)
      rw [h_out_eq]
      refine TEnvWF.of_addInNewestContext_mono (T := CoreLParams) v_out.2 out_mty_sig
        (by rw [h_vout_env]; exact h_pre_wf) ?_out_fresh
      case _out_fresh =>
        -- Free vars of the resolved-substituted output types are the setup fresh vars
        -- (< setup gen ≤ v_out.2 gen), so never `$__tyN` for N ≥ v_out.2 gen.
        have h_aw : TContext.AliasesWF v_pre.2.context :=
          pre_env_AliasesWF C Env proc fr v_setup v_pre h_setup h_pre h_wf h_fwf
        exact output_sig_values_fresh C Env proc fr v_setup v_pre v_out h_ta h_setup h_pre h_ra h_wf h_fwf h_aw
    -- `E4 = addInNewestContext envWithOutputs oldInoutBindings`, and `oldInoutBindings` is
    -- already in `.forAll [] ty` shape, so `of_addInNewestContext_mono` applies again.
    have h_old_eq : oldInoutBindings =
        ((v_setup.1.filter fun (id, _) => (ListMap.keys proc.header.outputs).contains id).map
          fun (id, ty) => (CoreIdent.mkOld id.name, ty)).map
          (fun p => (p.1, LTy.forAll [] p.2)) := by
      simp only [oldInoutBindings, List.map_map]
      rfl
    show TEnvWF (T := CoreLParams)
      (Lambda.TEnv.addInNewestContext (T := CoreLParams) envWithOutputs oldInoutBindings)
    rw [h_old_eq]
    refine TEnvWF.of_addInNewestContext_mono (T := CoreLParams) envWithOutputs _
      h_envWithOutputs_wf ?_old_fresh
    case _old_fresh =>
      -- Old-binding types are the instantiated input signature values, whose free vars are the
      -- setup fresh vars (< setup gen ≤ envWithOutputs gen).
      have h_gen : envWithOutputs.genEnv.genState.tyGen ≥ v_setup.2.1.genEnv.genState.tyGen := by
        have h_eq : envWithOutputs.genEnv.genState.tyGen = v_out.2.genEnv.genState.tyGen := rfl
        rw [h_eq, h_vout_env]
        exact typeCheckConditions_genState_mono C v_setup.2.1 proc.spec.preconditions proc.header.name
          v_pre h_pre h_setup_wf h_setup_ne h_fwf
      exact oldInout_bindings_fresh C Env proc fr v_setup v_pre v_out envWithOutputs h_ta h_setup h_pre h_ra
        h_wf h_fwf h_gen
  case _types_ne =>
    -- addInNewest ×2 preserves types ≠ []; v_out.2 = v_pre.2 nonempty.
    show E4.context.types ≠ []
    apply addInNewestContext_types_ne
    apply addInNewestContext_types_ne
    rw [h_vout_env]; exact h_pre_ne
  case _resolved =>
    -- aliases unchanged by both addInNewest steps; v_out.2 = v_pre.2 resolved.
    show TContext.AliasesResolved E4.context
    apply TContext.AliasesResolved.of_addInNewestContext
    apply TContext.AliasesResolved.of_addInNewestContext
    rw [h_vout_env]; exact h_pre_res

/-- After postconditions and the type-argument unify/`updateSubst`, the body environment stays
    well-formed: `TEnvWF`, non-empty type-scope, `ContextMono`, and `AliasesResolved`. -/
theorem procBodyEnv_wf (C : Core.Expression.TyContext) (E4 : Core.Expression.TyEnv)
    (proc : Procedure)
    (v_post : Array Expression.Expr × Core.Expression.TyEnv)
    (tyArgConstraints : Lambda.Constraints) (S : Lambda.SubstInfo)
    (h_post : Core.Procedure.typeCheckConditions C E4 proc.spec.postconditions
      proc.header.name = .ok v_post)
    (h_unify : Lambda.Constraints.unify tyArgConstraints v_post.2.stateSubstInfo = .ok S)
    (h_cs_fresh : ∀ v, v ∈ Lambda.Constraints.freeVars tyArgConstraints →
      ∀ n, n ≥ v_post.2.genEnv.genState.tyGen → v ≠ Lambda.TState.tyPrefix ++ toString n)
    (h_E4_wf : TEnvWF (T := CoreLParams) E4)
    (h_E4_ne : E4.context.types ≠ [])
    (h_E4_mono : ContextMono E4.context)
    (h_E4_res : TContext.AliasesResolved E4.context)
    (h_fwf : FactoryWF C.functions) :
    TEnvWF (T := CoreLParams) (v_post.2.updateSubst S) ∧
    (v_post.2.updateSubst S).context.types ≠ [] ∧
    ContextMono (v_post.2.updateSubst S).context ∧
    TContext.AliasesResolved (v_post.2.updateSubst S).context := by
  have h_post_ctx : v_post.2.context = E4.context :=
    typeCheckConditions_context C E4 proc.spec.postconditions proc.header.name v_post h_post
      h_E4_wf h_E4_ne h_fwf
  have h_post_wf : TEnvWF (T := CoreLParams) v_post.2 :=
    typeCheckConditions_TEnvWF C E4 proc.spec.postconditions proc.header.name v_post h_post
      h_E4_wf h_fwf
  have h_us_ctx : (v_post.2.updateSubst S).context = v_post.2.context := rfl
  refine ⟨?_tenvwf, ?_types_ne, ?_mono, ?_resolved⟩
  case _tenvwf =>
    exact TEnvWF.of_unify_updateSubst h_post_wf h_unify h_cs_fresh
  case _types_ne =>
    rw [h_us_ctx, h_post_ctx]; exact h_E4_ne
  case _mono =>
    intro x ty h_find
    rw [h_us_ctx, h_post_ctx] at h_find
    exact h_E4_mono x ty h_find
  case _resolved =>
    show TContext.AliasesResolved (v_post.2.updateSubst S).context
    rw [h_us_ctx, h_post_ctx]; exact h_E4_res

/-! ### `ContextMono` of the body env, chained from `ContextMono Env.context`. -/

/-- `addInNewestContext` with a single `forAll []` binding preserves `ContextMono`. -/
theorem addInNewestContext_single_ContextMono (Env : Core.Expression.TyEnv)
    (x : CoreIdent) (mty : LMonoTy) (h_mono : ContextMono Env.context) :
    ContextMono (Env.addInNewestContext (T := CoreLParams) [(x, .forAll [] mty)]).context := by
  intro y ty h_find
  simp only [TEnv.addInNewestContext, TEnv.updateContext, TEnv.context] at h_find
  rcases Maps.find?_addInNewest_single Env.genEnv.context.types x (.forAll [] mty) y with
    ⟨h_new, _⟩ | h_old
  · rw [h_new] at h_find; injection h_find with h_find; subst h_find
    simp [LTy.boundVars]
  · rw [h_old] at h_find
    exact h_mono y ty h_find

/-- `addInNewestContext` with a full `forAll []`-map preserves `ContextMono`. -/
theorem addInNewestContext_ContextMono (Env : Core.Expression.TyEnv)
    (pairs : List (CoreIdent × LMonoTy)) (h_mono : ContextMono Env.context) :
    ContextMono (Env.addInNewestContext (T := CoreLParams)
      (pairs.map (fun p => (p.1, LTy.forAll [] p.2)))).context := by
  induction pairs generalizing Env with
  | nil =>
    intro y ty h_find
    simp only [List.map_nil] at h_find
    rw [TEnv.addInNewestContext_nil_find? (T := CoreLParams)] at h_find
    exact h_mono y ty h_find
  | cons b rest ih =>
    simp only [List.map_cons]
    rw [TEnv.addInNewestContext_cons_eq]
    exact ih (Env.addInNewestContext (T := CoreLParams) [(b.1, LTy.forAll [] b.2)])
      (addInNewestContext_single_ContextMono Env b.1 b.2 h_mono)

/-- `addInNewestContext` with a `toTrivialLTy` map preserves `ContextMono`. -/
theorem addInNewestContext_toTrivial_ContextMono (Env : Core.Expression.TyEnv)
    (sig : @Lambda.LMonoTySignature Unit) (h_mono : ContextMono Env.context) :
    ContextMono (Env.addInNewestContext (T := CoreLParams)
      (Lambda.LMonoTySignature.toTrivialLTy sig)).context := by
  have h_eq : Lambda.LMonoTySignature.toTrivialLTy sig
      = sig.map (fun p => (p.1, LTy.forAll [] p.2)) := rfl
  rw [h_eq]
  exact addInNewestContext_ContextMono Env sig h_mono

/-- `setupInputEnv` preserves `ContextMono`. -/
theorem setupInputEnv_ContextMono (C : Core.Expression.TyContext) (Env : Core.Expression.TyEnv)
    (proc : Procedure) (fr : Strata.FileRange)
    (res : @Lambda.LMonoTySignature Unit × Core.Expression.TyEnv × Lambda.Subst)
    (h : Core.Procedure.setupInputEnv C Env proc fr = .ok res)
    (h_mono : ContextMono Env.context) :
    ContextMono res.2.1.context := by
  simp only [Core.Procedure.setupInputEnv, Bind.bind, Except.bind, Except.mapError, pure,
    Except.pure] at h
  cases h_inst : Lambda.LMonoTySignature.instantiateWithSubst C Env.pushEmptyContext
      proc.header.typeArgs proc.header.inputs with
  | error e => rw [h_inst] at h; simp only [reduceCtorEq] at h
  | ok v =>
    obtain ⟨inp_mty_sig, Env₁, tyArgSubst⟩ := v
    rw [h_inst] at h
    simp only [Except.ok.injEq] at h
    subst h
    have h_push_mono : ContextMono Env.pushEmptyContext.context :=
      pushEmptyContext_ContextMono Env h_mono
    have h_ctx : Env₁.context = Env.pushEmptyContext.context :=
      instantiateWithSubst_preserves_context C Env.pushEmptyContext proc.header.typeArgs
        proc.header.inputs (inp_mty_sig, Env₁, tyArgSubst) h_inst
    have h_inst_mono : ContextMono Env₁.context := by rw [h_ctx]; exact h_push_mono
    show ContextMono (Env₁.addInNewestContext (Lambda.LMonoTySignature.toTrivialLTy inp_mty_sig)).context
    exact addInNewestContext_toTrivial_ContextMono Env₁ inp_mty_sig h_inst_mono

/-- `ContextMono` of the postcondition env `E4`, chained from `ContextMono Env.context`. -/
theorem E4_ContextMono (C : Core.Expression.TyContext) (Env : Core.Expression.TyEnv)
    (proc : Procedure) (fr : Strata.FileRange)
    (v_setup : @Lambda.LMonoTySignature Unit × Core.Expression.TyEnv × Lambda.Subst)
    (v_pre : Array Expression.Expr × Core.Expression.TyEnv)
    (v_out : Lambda.LMonoTys × Core.Expression.TyEnv)
    (h_setup : Core.Procedure.setupInputEnv C Env proc fr = .ok v_setup)
    (h_pre : Core.Procedure.typeCheckConditions C v_setup.2.1 proc.spec.preconditions
      proc.header.name = .ok v_pre)
    (h_ra : Lambda.LMonoTys.resolveAliases
      (proc.header.outputs.values.map (Lambda.LMonoTy.subst v_setup.2.2)) v_pre.2 = .ok v_out)
    (h_wf : TEnvWF (T := CoreLParams) Env)
    (h_fwf : FactoryWF C.functions)
    (h_mono : ContextMono Env.context) :
    ContextMono
      (Lambda.TEnv.addInNewestContext (T := CoreLParams)
        (Lambda.TEnv.addInNewestContext (T := CoreLParams) v_out.snd
          (@Lambda.LMonoTySignature.toTrivialLTy Unit
            ((ListMap.keys proc.header.outputs).zip v_out.fst)))
        (List.map (fun x => (CoreIdent.mkOld x.fst.name, LTy.forAll [] x.snd))
          (v_setup.1.filter (fun x => (ListMap.keys proc.header.outputs).contains x.fst)))).context := by
  have h_vout_env : v_out.2 = v_pre.2 :=
    LMonoTys_resolveAliases_env_local _ v_pre.2 v_out.1 v_out.2 h_ra
  have h_setup_ne : v_setup.2.1.context.types ≠ [] :=
    setupInputEnv_types_ne C Env proc fr v_setup h_setup
  have h_setup_wf : TEnvWF (T := CoreLParams) v_setup.2.1 :=
    setupInputEnv_TEnvWF C Env proc fr v_setup h_setup h_wf
  have h_pre_ctx : v_pre.2.context = v_setup.2.1.context :=
    typeCheckConditions_context C v_setup.2.1 proc.spec.preconditions proc.header.name v_pre h_pre
      h_setup_wf h_setup_ne h_fwf
  have h_setup_mono : ContextMono v_setup.2.1.context :=
    setupInputEnv_ContextMono C Env proc fr v_setup h_setup h_mono
  have h_vout_mono : ContextMono v_out.2.context := by
    rw [h_vout_env, h_pre_ctx]; exact h_setup_mono
  have h_out_mono : ContextMono
      (Lambda.TEnv.addInNewestContext (T := CoreLParams) v_out.2
        (@Lambda.LMonoTySignature.toTrivialLTy Unit
          ((ListMap.keys proc.header.outputs).zip v_out.fst))).context :=
    addInNewestContext_toTrivial_ContextMono v_out.2 _ h_vout_mono
  have h_old_eq : (List.map (fun x : CoreIdent × LMonoTy => (CoreIdent.mkOld x.fst.name, LTy.forAll [] x.snd))
      (v_setup.1.filter (fun x => (ListMap.keys proc.header.outputs).contains x.fst)))
      = (List.map (fun x : CoreIdent × LMonoTy => (CoreIdent.mkOld x.fst.name, x.snd))
          (v_setup.1.filter (fun x => (ListMap.keys proc.header.outputs).contains x.fst))).map
            (fun p => (p.1, LTy.forAll [] p.2)) := by
    rw [List.map_map]; rfl
  rw [h_old_eq]
  exact addInNewestContext_ContextMono _ _ h_out_mono

/-- freeVars of the `tyArgConstraints` list `l.map (ftvar ·.1, ·.2)`: each element
    contributes its LHS var (`kv.1`) and the freeVars of its RHS (`kv.2`). -/
theorem tyArgConstraints_freeVars_mem (l : List (TyIdentifier × LMonoTy)) (v : TyIdentifier)
    (h : v ∈ Lambda.Constraints.freeVars (List.map (fun x => (LMonoTy.ftvar x.fst, x.snd)) l)) :
    (∃ kv, kv ∈ l ∧ v = kv.1) ∨ (∃ kv, kv ∈ l ∧ v ∈ LMonoTy.freeVars kv.2) := by
  induction l with
  | nil => simp only [List.map_nil, Lambda.Constraints.freeVars] at h; exact absurd h (List.not_mem_nil)
  | cons a rest ih =>
    simp only [List.map_cons, Lambda.Constraints.freeVars, Lambda.Constraint.freeVars,
      LMonoTy.freeVars, List.mem_append] at h
    rcases h with (h_lhs | h_rhs) | h_rest
    · left
      refine ⟨a, List.mem_cons_self, ?_⟩
      simp only [List.mem_singleton] at h_lhs; exact h_lhs
    · right; exact ⟨a, List.mem_cons_self, h_rhs⟩
    · rcases ih h_rest with ⟨kv, h_mem, h_eq⟩ | ⟨kv, h_mem, h_mem2⟩
      · exact Or.inl ⟨kv, List.mem_cons_of_mem _ h_mem, h_eq⟩
      · exact Or.inr ⟨kv, List.mem_cons_of_mem _ h_mem, h_mem2⟩

/-- The free vars of the body's `tyArgConstraints` are gen-fresh at the postcondition
    env's generator counter. -/
theorem procBody_cs_fresh (C : Core.Expression.TyContext) (Env : Core.Expression.TyEnv)
    (proc : Procedure) (fr : Strata.FileRange)
    (v_setup : @Lambda.LMonoTySignature Unit × Core.Expression.TyEnv × Lambda.Subst)
    (v_pre : Array Expression.Expr × Core.Expression.TyEnv)
    (v_out : Lambda.LMonoTys × Core.Expression.TyEnv)
    (v_post : Array Expression.Expr × Core.Expression.TyEnv)
    (h_ta : proc.checkTypeArgsWF fr = .ok ())
    (h_setup : Core.Procedure.setupInputEnv C Env proc fr = .ok v_setup)
    (h_pre : Core.Procedure.typeCheckConditions C v_setup.2.1 proc.spec.preconditions
      proc.header.name = .ok v_pre)
    (h_ra : Lambda.LMonoTys.resolveAliases
      (proc.header.outputs.values.map (Lambda.LMonoTy.subst v_setup.2.2)) v_pre.2 = .ok v_out)
    (h_post : Core.Procedure.typeCheckConditions C
      (Lambda.TEnv.addInNewestContext (T := CoreLParams)
        (Lambda.TEnv.addInNewestContext (T := CoreLParams) v_out.snd
          (@Lambda.LMonoTySignature.toTrivialLTy Unit
            ((ListMap.keys proc.header.outputs).zip v_out.fst)))
        (List.map (fun x => (CoreIdent.mkOld x.fst.name, LTy.forAll [] x.snd))
          (v_setup.1.filter (fun x => (ListMap.keys proc.header.outputs).contains x.fst))))
      proc.spec.postconditions proc.header.name = .ok v_post)
    (h_wf : TEnvWF (T := CoreLParams) Env)
    (h_fwf : FactoryWF C.functions)
    (h_resolved : TContext.AliasesResolved Env.context) :
    ∀ v, v ∈ Lambda.Constraints.freeVars
        (List.map (fun x => (LMonoTy.ftvar x.fst, x.snd)) (List.flatten v_setup.2.snd)) →
      ∀ n, n ≥ v_post.2.genEnv.genState.tyGen → v ≠ Lambda.TState.tyPrefix ++ toString n := by
  have h_penv := postEnv_wf C Env proc fr v_setup v_pre v_out h_ta h_setup h_pre h_ra
    h_wf h_fwf h_resolved
  obtain ⟨freshtvs, h_len, h_shape, h_fresh_setup, _, _⟩ :=
    setupInputEnv_shape_fresh C Env proc fr v_setup h_setup
  have h_flat : List.flatten v_setup.2.snd = proc.header.typeArgs.zip (freshtvs.map LMonoTy.ftvar) := by
    rw [h_shape]; simp only [List.flatten_cons, List.flatten_nil, List.append_nil]
  have h_ta_props := checkTypeArgsWF_props proc fr () h_ta
  intro v hv n hn
  have h_setup_wf : TEnvWF (T := CoreLParams) v_setup.2.1 :=
    setupInputEnv_TEnvWF C Env proc fr v_setup h_setup h_wf
  have h_setup_ne : v_setup.2.1.context.types ≠ [] :=
    setupInputEnv_types_ne C Env proc fr v_setup h_setup
  have h_gen_pre : v_pre.2.genEnv.genState.tyGen ≥ v_setup.2.1.genEnv.genState.tyGen :=
    typeCheckConditions_genState_mono C v_setup.2.1 proc.spec.preconditions proc.header.name v_pre
      h_pre h_setup_wf h_setup_ne h_fwf
  have h_vout_env : v_out.2 = v_pre.2 :=
    LMonoTys_resolveAliases_env_local _ v_pre.2 v_out.1 v_out.2 h_ra
  have h_E4_gen : (Lambda.TEnv.addInNewestContext (T := CoreLParams)
      (Lambda.TEnv.addInNewestContext (T := CoreLParams) v_out.snd
        (@Lambda.LMonoTySignature.toTrivialLTy Unit
          ((ListMap.keys proc.header.outputs).zip v_out.fst)))
      (List.map (fun x => (CoreIdent.mkOld x.fst.name, LTy.forAll [] x.snd))
        (v_setup.1.filter (fun x => (ListMap.keys proc.header.outputs).contains x.fst)))).genEnv.genState.tyGen
      = v_out.2.genEnv.genState.tyGen := rfl
  have h_gen_post : v_post.2.genEnv.genState.tyGen ≥ v_out.2.genEnv.genState.tyGen := by
    have h_mono := typeCheckConditions_genState_mono C _ proc.spec.postconditions proc.header.name v_post
      h_post h_penv.1 h_penv.2.1 h_fwf
    rw [h_E4_gen] at h_mono; exact h_mono
  have h_n_setup : n ≥ v_setup.2.1.genEnv.genState.tyGen := by
    rw [h_vout_env] at h_gen_post; omega
  rcases tyArgConstraints_freeVars_mem _ v hv with ⟨kv, h_mem, h_eq⟩ | ⟨kv, h_mem, h_mem2⟩
  · rw [h_flat] at h_mem
    have h_kv1_ta : kv.1 ∈ proc.header.typeArgs := (List.of_mem_zip h_mem).1
    rw [h_eq]
    exact not_prefix_ne_gen kv.1 (h_ta_props.2.2 kv.1 h_kv1_ta) n
  · rw [h_flat] at h_mem
    have h_kv2 : kv.2 ∈ freshtvs.map LMonoTy.ftvar := (List.of_mem_zip h_mem).2
    obtain ⟨fresh, h_fresh_mem, h_fresh_eq⟩ := List.mem_map.mp h_kv2
    rw [← h_fresh_eq] at h_mem2
    simp only [LMonoTy.freeVars, List.mem_singleton] at h_mem2
    rw [h_mem2]
    exact h_fresh_setup fresh h_fresh_mem n h_n_setup

/-! ### Annotated soundness (about the output `proc'`)

Field lemmas feeding `Procedure.typeCheck_annotated_sound`. -/

/-- `setupInputEnv`, on success, returns a signature whose keys are a sublist of
    `proc.header.inputs.keys` (it is `proc.header.inputs.keys.zip newtys`). -/
theorem setupInputEnv_keys_sublist (C : Core.Expression.TyContext) (Env : Core.Expression.TyEnv)
    (proc : Procedure) (fr : Strata.FileRange) (sig : @Lambda.LMonoTySignature Unit)
    (Env2 : Core.Expression.TyEnv) (S : Lambda.Subst)
    (h : Core.Procedure.setupInputEnv C Env proc fr = .ok (sig, Env2, S)) :
    (sig.map Prod.fst).Sublist (ListMap.keys proc.header.inputs) := by
  simp only [Core.Procedure.setupInputEnv, Lambda.LMonoTySignature.instantiateWithSubst,
    bind, Except.bind, Except.mapError, pure, Except.pure] at h
  elim_err h
  rename_i v1 hv1
  cases h
  elim_err hv1
  rename_i v2 hv2
  cases hv1
  elim_err hv2
  rename_i v3 hv3
  elim_err hv2
  rename_i v4 hv4
  cases hv2
  simp only []
  exact List.map_fst_zip_sublist _ _

/-- Annotated `inputsNodup`: the output procedure's input names are distinct. -/
theorem Procedure.typeCheck_inputsNodup (C : LContext CoreLParams) (Env : TEnv Unit)
    (P : Program) (proc proc' : Procedure) (Env' : TEnv Unit) (md : MetaData Expression)
    (h : Procedure.typeCheck C Env P proc md = .ok (proc', Env')) :
    proc'.header.inputs.keys.Nodup := by
  simp only [Procedure.typeCheck, Procedure.checkNoDuplicates, bind, Except.bind,
    pure, Except.pure] at h
  split at h
  · simp at h
  rename_i h_in_guard
  have h_nodup : (ListMap.keys proc.header.inputs).Nodup := by
    split at h_in_guard
    · simp at h_in_guard
    · rename_i h_no
      simpa using h_no
  elim_err h
  elim_err h
  elim_err h
  rename_i v_setup h_setup
  elim_err h
  elim_err h
  elim_err h
  split at h
  · rename_i ss h_body
    elim_err h
    split at h
    · simp at h
    elim_err h
    injection h with h_pair
    injection h_pair with h_proc _
    subst h_proc
    simp only [ListMap.keys_eq_map_fst, List.map_map]
    have h_ml := List.map_congr_left (l := v_setup.fst)
      (f := (Prod.fst ∘ fun x : CoreIdent × LMonoTy =>
        (x.fst, LMonoTy.subst
          [List.filterMap (fun x => match x.snd with
            | LMonoTy.ftvar fresh => some (fresh, LMonoTy.ftvar x.fst)
            | x => none) (List.flatten v_setup.2.snd)] x.snd)))
      (g := Prod.fst) (fun p _ => rfl)
    have h_sub := setupInputEnv_keys_sublist C Env proc
      ((getFileRange md).getD Strata.FileRange.unknown)
      v_setup.fst v_setup.2.fst v_setup.2.snd (by rw [← h_setup])
    have h_res := h_sub.nodup h_nodup
    rw [← h_ml] at h_res
    exact h_res
  · simp at h

/-- Annotated `outputsNodup`: the output procedure's return names are distinct. -/
theorem Procedure.typeCheck_outputsNodup (C : LContext CoreLParams) (Env : TEnv Unit)
    (P : Program) (proc proc' : Procedure) (Env' : TEnv Unit) (md : MetaData Expression)
    (h : Procedure.typeCheck C Env P proc md = .ok (proc', Env')) :
    proc'.header.outputs.keys.Nodup := by
  simp only [Procedure.typeCheck, Procedure.checkNoDuplicates, bind, Except.bind,
    pure, Except.pure] at h
  split at h
  · simp at h
  rename_i h_in_guard
  have h_nodup : (ListMap.keys proc.header.outputs).Nodup := by
    split at h_in_guard
    · simp at h_in_guard
    rename_i h_in_no
    split at h_in_guard
    · simp at h_in_guard
    · rename_i h_out_no
      simpa using h_out_no
  elim_err h
  elim_err h
  elim_err h
  rename_i v_setup h_setup
  elim_err h
  elim_err h
  rename_i v_out h_out
  elim_err h
  split at h
  · rename_i ss h_body
    elim_err h
    split at h
    · simp at h
    elim_err h
    injection h with h_pair
    injection h_pair with h_proc _
    subst h_proc
    simp only [ListMap.keys_eq_map_fst, List.map_map]
    have h_ml := List.map_congr_left
      (l := (List.map Prod.fst proc.header.outputs).zip v_out.fst)
      (f := (Prod.fst ∘ fun x : CoreIdent × LMonoTy =>
        (x.fst, LMonoTy.subst
          [List.filterMap (fun x => match x.snd with
            | LMonoTy.ftvar fresh => some (fresh, LMonoTy.ftvar x.fst)
            | x => none) (List.flatten v_setup.2.snd)] x.snd)))
      (g := Prod.fst) (fun p _ => rfl)
    have h_sub := List.map_fst_zip_sublist (List.map Prod.fst proc.header.outputs) v_out.fst
    have h_nodup' : (List.map Prod.fst proc.header.outputs).Nodup := by
      rw [← ListMap.keys_eq_map_fst]; exact h_nodup
    have h_res := h_sub.nodup h_nodup'
    rw [← h_ml] at h_res
    exact h_res
  · simp at h

/-- Annotated `typeArgsNodup`. `Procedure.typeCheck` preserves `proc'.typeArgs =
    proc.header.typeArgs`, so this follows from the `checkTypeArgsWF` guard's
    `Nodup` check on the input. -/
theorem Procedure.typeCheck_typeArgsNodup (C : LContext CoreLParams) (Env : TEnv Unit)
    (P : Program) (proc proc' : Procedure) (Env' : TEnv Unit) (md : MetaData Expression)
    (h : Procedure.typeCheck C Env P proc md = .ok (proc', Env')) :
    proc'.header.typeArgs.Nodup := by
  simp only [Procedure.typeCheck, bind, Except.bind] at h
  elim_err h
  elim_err h with h_ta
  elim_err h
  elim_err h
  elim_err h
  elim_err h
  elim_err h
  split at h
  · elim_err h
    elim_err h
    split at h
    · simp at h
    elim_err h
    elim_err h
    cases h
    exact (checkTypeArgsWF_props proc _ _ h_ta).1
  · simp at h

/-- The fresh→user `filterMap` over `typeArgs.zip (freshtvs.map ftvar)` equals
    `(freshtvs.zip typeArgs).map (·.1, ftvar ·.2)`. -/
theorem userSubst_filterMap_eq (typeArgs freshtvs : List TyIdentifier)
    (h_len : freshtvs.length = typeArgs.length) :
    List.filterMap (fun x => match x.snd with
        | LMonoTy.ftvar fresh => some (fresh, LMonoTy.ftvar x.fst) | _ => none)
      (typeArgs.zip (freshtvs.map LMonoTy.ftvar))
      = (freshtvs.zip typeArgs).map (fun x => (x.1, LMonoTy.ftvar x.2)) := by
  induction typeArgs generalizing freshtvs with
  | nil => cases freshtvs <;> simp_all
  | cons a rest ih =>
    cases freshtvs with
    | nil => simp at h_len
    | cons f frest =>
      simp only [List.map_cons, List.zip_cons_cons, List.filterMap_cons, List.map_cons]
      rw [ih frest (by simpa using h_len)]

/-- Applying the fresh→user renaming to a monotype whose free vars are all fresh yields a monotype
    whose free vars are all declared type args. -/
theorem freeVars_userSubst_mem_typeArgs
    (typeArgs freshtvs : List TyIdentifier) (mty : LMonoTy)
    (h_len : freshtvs.length = typeArgs.length)
    (h_closed : ∀ v, v ∈ mty.freeVars → v ∈ freshtvs) :
    ∀ v, v ∈ LMonoTy.freeVars (LMonoTy.subst
        [List.filterMap (fun x => match x.snd with
            | LMonoTy.ftvar fresh => some (fresh, LMonoTy.ftvar x.fst) | _ => none)
          (typeArgs.zip (freshtvs.map LMonoTy.ftvar))] mty) →
      v ∈ typeArgs := by
  intro v hv
  rw [userSubst_filterMap_eq typeArgs freshtvs h_len] at hv
  have h_cov : freshtvs.length ≤ typeArgs.length := Nat.le_of_eq h_len
  have h_sub := freeVars_rename_subset freshtvs typeArgs mty h_cov h_closed v hv
  have e1 : ∀ (I T : List TyIdentifier), (I.zip T).map Prod.snd = T.take I.length := by
    intro I
    induction I with
    | nil => simp
    | cons a rest ih =>
      intro T; cases T with
      | nil => simp
      | cons t trest => simp only [List.zip_cons_cons, List.map_cons, List.length_cons, List.take_succ_cons, ih]
  rw [e1 freshtvs typeArgs] at h_sub
  exact List.mem_of_mem_take h_sub

/-- Shape of `setupInputEnv`: the substitution is a single scope mapping type args to fresh vars,
    and every input-signature value's free vars are gen-fresh. -/
theorem setupInputEnv_shape (C : Core.Expression.TyContext) (Env : Core.Expression.TyEnv)
    (proc : Procedure) (fr : Strata.FileRange)
    (v_setup : @Lambda.LMonoTySignature Unit × Core.Expression.TyEnv × Lambda.Subst)
    (h : Core.Procedure.setupInputEnv C Env proc fr = .ok v_setup) :
    ∃ freshtvs : List TyIdentifier,
      freshtvs.length = proc.header.typeArgs.length ∧
      v_setup.2.snd = [proc.header.typeArgs.zip (freshtvs.map LMonoTy.ftvar)] ∧
      (∀ mt, mt ∈ ListMap.values v_setup.fst →
        ∀ x, x ∈ LMonoTy.freeVars mt →
          ∀ n, n ≥ v_setup.2.fst.genEnv.genState.tyGen →
            x ≠ TState.tyPrefix ++ toString n) := by
  simp only [Core.Procedure.setupInputEnv, Bind.bind, Except.bind, Except.mapError, pure,
    Except.pure] at h
  cases h_inst : Lambda.LMonoTySignature.instantiateWithSubst C Env.pushEmptyContext
      proc.header.typeArgs proc.header.inputs with
  | error e => rw [h_inst] at h; simp only [reduceCtorEq] at h
  | ok v =>
    obtain ⟨inp_mty_sig, Env₁, tyArgSubst⟩ := v
    rw [h_inst] at h
    simp only [Except.ok.injEq] at h
    subst h
    have h_fresh := instantiateWithSubst_values_fresh C Env.pushEmptyContext
      proc.header.typeArgs proc.header.inputs (inp_mty_sig, Env₁, tyArgSubst) h_inst
    simp only [Lambda.LMonoTySignature.instantiateWithSubst, Bind.bind, Except.bind] at h_inst
    elim_err h_inst with v_env h_env; obtain ⟨mtys, Env_e, S⟩ := v_env
    elim_err h_inst with v_go h_go; obtain ⟨newtys, Env₂⟩ := v_go
    simp only [Except.ok.injEq, Prod.mk.injEq] at h_inst
    obtain ⟨h_sig, h_env2, h_S2⟩ := h_inst
    obtain ⟨freshtvs, genEnv', h_gen, _, h_S, _, _⟩ :=
      instantiateEnvWithSubst_decompose proc.header.typeArgs (ListMap.values proc.header.inputs)
        Env.pushEmptyContext (mtys, Env_e, S) h_env
    simp only at h_S
    refine ⟨freshtvs, ?_, ?_, ?_⟩
    · exact TGenEnv.genTyVars_length proc.header.typeArgs.length Env.pushEmptyContext.genEnv
        freshtvs genEnv' h_gen
    · show tyArgSubst = _
      rw [← h_S2]; exact h_S
    · show ∀ mt, mt ∈ ListMap.values inp_mty_sig → _
      exact h_fresh

/-- Every free type variable in a type-checked procedure's signature is declared in `typeArgs`
    (the `noUndeclaredVars` field of `ProcHasType'`). -/
theorem Procedure.typeCheck_noUndeclaredVars (C : LContext CoreLParams) (Env : TEnv Unit)
    (P : Program) (proc proc' : Procedure) (Env' : TEnv Unit) (md : MetaData Expression)
    (h : Procedure.typeCheck C Env P proc md = .ok (proc', Env'))
    (h_wf : TEnvWF (T := CoreLParams) Env)
    (h_fwf : FactoryWF C.functions) :
    ∀ v, v ∈ LMonoTys.freeVars proc'.header.inputs.values ++
             LMonoTys.freeVars proc'.header.outputs.values →
         v ∈ proc'.header.typeArgs := by
  simp only [Procedure.typeCheck, bind, Except.bind] at h
  elim_err h
  elim_err h with h_ta
  elim_err h
  elim_err h with h_setup
  rename_i v_setup
  elim_err h with h_pre
  rename_i v_pre
  elim_err h with h_ra_out
  rename_i v_out
  elim_err h with h_post
  split at h
  · elim_err h
    elim_err h
    split at h
    · simp at h
    elim_err h
    elim_err h with h_body
    cases h
    obtain ⟨freshtvs, h_len, h_S, _⟩ := setupInputEnv_shape C Env proc _ v_setup h_setup
    have h_flat : List.flatten v_setup.2.snd
        = proc.header.typeArgs.zip (freshtvs.map LMonoTy.ftvar) := by
      rw [h_S]; simp only [List.flatten_cons, List.flatten_nil, List.append_nil]
    have h_ta_props := checkTypeArgsWF_props proc _ _ h_ta
    intro v hv
    simp only [ListMap.values_eq_map_snd, List.map_map] at hv
    rw [List.mem_append] at hv
    show v ∈ proc.header.typeArgs
    rw [h_flat] at hv
    cases hv with
    | inl hv_in =>
      -- Inputs case: the setup input values are closed under `freshtvs` (instantiate outputs
      -- resolve non-growing under AliasesWF; inputs are closed under `typeArgs`).
      have h_in_closed : ∀ x, x ∈ LMonoTys.freeVars (ListMap.values proc.header.inputs) →
          x ∈ proc.header.typeArgs := by
        intro x hx
        exact h_ta_props.2.1 x (List.mem_append_left _ hx)
      have h_vals_closed : ∀ w, w ∈ LMonoTys.freeVars (ListMap.values v_setup.fst) →
          w ∈ freshtvs :=
        setupInputEnv_values_closed C Env proc _ v_setup freshtvs h_setup h_wf h_len h_S
          h_in_closed
      obtain ⟨elt, h_elt_mem, h_v_elt⟩ := LMonoTys.freeVars_exists hv_in
      simp only [List.mem_map, Function.comp_apply] at h_elt_mem
      obtain ⟨p, hp_mem, hp_eq⟩ := h_elt_mem
      subst hp_eq
      have hp_snd_mem : p.snd ∈ ListMap.values v_setup.fst := by
        rw [ListMap.values_eq_map_snd]; exact List.mem_map_of_mem hp_mem
      have h_closed_elt : ∀ w, w ∈ LMonoTy.freeVars p.snd → w ∈ freshtvs := by
        intro w hw
        exact h_vals_closed w (LMonoTys.freeVars_mem_subset hp_snd_mem hw)
      exact freeVars_userSubst_mem_typeArgs proc.header.typeArgs freshtvs p.snd h_len
        h_closed_elt v h_v_elt
    | inr hv_out =>
      -- Outputs case.
      obtain ⟨elt, h_elt_mem, h_v_elt⟩ := LMonoTys.freeVars_exists hv_out
      simp only [List.mem_map, Function.comp_apply] at h_elt_mem
      obtain ⟨p, hp_mem, hp_eq⟩ := h_elt_mem
      have hp_snd : p.snd ∈ v_out.fst := (List.of_mem_zip hp_mem).2
      subst hp_eq
      have h_closed_elt : ∀ w, w ∈ LMonoTy.freeVars p.snd → w ∈ freshtvs := by
        intro w hw
        have hw_list : w ∈ LMonoTys.freeVars v_out.fst :=
          LMonoTys.freeVars_mem_subset hp_snd hw
        have h_ra := Lambda.Except.mapError_ok_h' h_ra_out
        -- `resolveAliases` does not grow free vars, needing `AliasesWF` of the pre-conditions env
        -- (which transports from `h_wf` since the pre-loop and setup preserve the alias list).
        have h_aw : TContext.AliasesWF v_pre.snd.context :=
          pre_env_AliasesWF C Env proc _ v_setup v_pre h_setup h_pre h_wf h_fwf
        have hw_pre : w ∈ LMonoTys.freeVars
            (List.map (LMonoTy.subst v_setup.2.snd) (ListMap.values proc.header.outputs)) :=
          LMonoTys_resolveAliases_freeVars_subset (T := CoreLParams)
            (List.map (LMonoTy.subst v_setup.2.snd) (ListMap.values proc.header.outputs))
            v_pre.snd v_out.fst v_out.snd h_ra h_aw w hw_list
        rw [← LMonoTys_subst_eq_map, h_S] at hw_pre
        have h_out_closed : ∀ tv, tv ∈ LMonoTys.freeVars (ListMap.values proc.header.outputs) →
            tv ∈ proc.header.typeArgs := by
          intro tv htv
          exact h_ta_props.2.1 tv (List.mem_append_right _ htv)
        exact LMonoTys.freeVars_subst_closed proc.header.typeArgs freshtvs h_len
          (ListMap.values proc.header.outputs) h_out_closed w hw_pre
      exact freeVars_userSubst_mem_typeArgs proc.header.typeArgs freshtvs p.snd h_len
        h_closed_elt v h_v_elt
  · simp at h


/-! ### Annotated `modRights` and its supporting infrastructure

`Statement.subst`/`Statement.typeCheck` preserve a body's modified/defined
variables, so the `checkModificationRights` guard (checked on the *input* body)
transports to the output `proc'.body`. -/

mutual
/-- `Statement.subst` preserves a statement's `modifiedVars`. -/
theorem subst_modifiedVars (S : Subst) (s : Statement) :
    Stmt.modifiedVars (Statement.subst S s) = Stmt.modifiedVars s := by
  cases s with
  | cmd c =>
    cases c with
    | cmd cc =>
      cases cc <;>
        simp only [Statement.subst, Command.subst, Cmd.subst, Stmt.modifiedVars,
          HasVarsImp.modifiedVars, Command.modifiedVars, Cmd.modifiedVars]
    | call pname args md =>
      simp only [Statement.subst, Command.subst, Stmt.modifiedVars,
        HasVarsImp.modifiedVars, Command.modifiedVars, CallArg.getLhs]
      induction args with
      | nil => rfl
      | cons a rest ih => cases a <;> simp_all
  | block label bss md =>
    simp only [Statement.subst, Stmt.modifiedVars, Statement.subst_go_nil]
    exact subst_block_modifiedVars S bss
  | ite cond tss ess md =>
    simp only [Statement.subst, Stmt.modifiedVars, Statement.subst_go_nil]
    rw [subst_block_modifiedVars S tss, subst_block_modifiedVars S ess]
  | loop guard measure invariant bss md =>
    simp only [Statement.subst, Stmt.modifiedVars, Statement.subst_go_nil]
    exact subst_block_modifiedVars S bss
  | exit l md => simp [Statement.subst, Stmt.modifiedVars]
  | funcDecl decl md => simp [Statement.subst, Stmt.modifiedVars]
  | typeDecl tc md => simp [Statement.subst, Stmt.modifiedVars]

/-- Block form of `subst_modifiedVars`. -/
theorem subst_block_modifiedVars (S : Subst) (bss : List Statement) :
    Block.modifiedVars (List.map (Statement.subst S) bss) = Block.modifiedVars bss := by
  match bss with
  | [] => rfl
  | s :: rest =>
    simp only [List.map_cons, Block.modifiedVars]
    rw [subst_modifiedVars S s, subst_block_modifiedVars S rest]
end

mutual
/-- `Statement.subst` preserves a statement's `definedVars`. -/
theorem subst_definedVars (S : Subst) (s : Statement) (b : Bool) :
    Stmt.definedVars (Statement.subst S s) b = Stmt.definedVars s b := by
  cases s with
  | cmd c =>
    cases c with
    | cmd cc =>
      cases cc <;>
        simp only [Statement.subst, Command.subst, Cmd.subst, Stmt.definedVars.eq_def,
          HasVarsImp.definedVars, Command.definedVars, Cmd.definedVars]
    | call pname args md =>
      simp only [Statement.subst, Command.subst, Stmt.definedVars.eq_def,
        HasVarsImp.definedVars, Command.definedVars]
  | block label bss md =>
    simp only [Statement.subst, Statement.subst_go_nil]
    cases b <;>
      simp only [Stmt.definedVars.eq_def, if_true, subst_block_definedVars]
  | ite cond tss ess md =>
    simp only [Statement.subst, Statement.subst_go_nil]
    cases b <;>
      simp only [Stmt.definedVars.eq_def, if_true, subst_block_definedVars]
  | loop guard measure invariant bss md =>
    simp only [Statement.subst, Statement.subst_go_nil]
    cases b <;>
      simp only [Stmt.definedVars.eq_def, if_true, subst_block_definedVars]
  | exit l md => simp [Statement.subst]
  | funcDecl decl md => simp [Statement.subst]
  | typeDecl tc md => simp [Statement.subst]

/-- Block form of `subst_definedVars`. -/
theorem subst_block_definedVars (S : Subst) (bss : List Statement) (b : Bool) :
    Block.definedVars (List.map (Statement.subst S) bss) b = Block.definedVars bss b := by
  match bss with
  | [] => rfl
  | s :: rest =>
    rw [List.map_cons, Block.definedVars.eq_2, Block.definedVars.eq_2,
      subst_definedVars S s b, subst_block_definedVars S rest b]
end

/-- `Imperative.Cmd.typeCheck` preserves `modifiedVars` and `definedVars`. -/
theorem cmd_typeCheck_modifiedVars (C : LContext CoreLParams) (Env Env' : TEnv Unit)
    (c c' : Cmd Expression)
    (h : Imperative.Cmd.typeCheck C Env c = .ok (c', Env')) :
    Cmd.modifiedVars c' = Cmd.modifiedVars c ∧
    Cmd.definedVars c' = Cmd.definedVars c := by
  cases c with
  | init x xty e md =>
    simp only [Imperative.Cmd.typeCheck, Bind.bind, Except.bind] at h
    elim_err h; rename_i h1
    split at h
    · elim_err h; rename_i h2
      elim_err h; rename_i v1 h3
      elim_err h; rename_i v2 h4
      elim_err h; rename_i v3 h5
      elim_err h; rename_i v4 h6
      elim_err h; rename_i v5 h7
      cases h
      simp only [Cmd.modifiedVars, Cmd.definedVars, and_self]
    · elim_err h; rename_i v1 h2
      elim_err h; rename_i v2 h3
      cases h
      simp only [Cmd.modifiedVars, Cmd.definedVars, and_self]
  | set x e md =>
    simp only [Imperative.Cmd.typeCheck, Bind.bind, Except.bind] at h
    elim_err h; rename_i h1
    split at h
    · elim_err h; rename_i v1 h2
      elim_err h; rename_i v2 h3
      elim_err h; rename_i v3 h4
      cases h
      simp only [Cmd.modifiedVars, Cmd.definedVars, and_self]
    · cases h
      simp only [Cmd.modifiedVars, Cmd.definedVars, and_self]
  | assert label e md =>
    simp only [Imperative.Cmd.typeCheck, Bind.bind, Except.bind] at h
    elim_err h; rename_i v1 h1
    elim_err h; rename_i v2 h2
    split at h
    · cases h
      exact ⟨rfl, rfl⟩
    · cases h
  | assume label e md =>
    simp only [Imperative.Cmd.typeCheck, Bind.bind, Except.bind] at h
    elim_err h; rename_i v1 h1
    elim_err h; rename_i v2 h2
    split at h
    · cases h
      exact ⟨rfl, rfl⟩
    · cases h
  | cover label e md =>
    simp only [Imperative.Cmd.typeCheck, Bind.bind, Except.bind] at h
    elim_err h; rename_i v1 h1
    elim_err h; rename_i v2 h2
    split at h
    · cases h
      exact ⟨rfl, rfl⟩
    · cases h

/-- `replaceInArgs` (rewriting the input expressions of a call) leaves the LHS variables unchanged. -/
private theorem getLhs_replaceInArgs (args : List (CallArg Expression))
    (es : List Expression.Expr) :
    CallArg.getLhs (CallArg.replaceInArgs args es) = CallArg.getLhs args := by
  simp only [CallArg.replaceInArgs]
  suffices h : ∀ es, CallArg.getLhs (CallArg.replaceInArgs.go args es) = CallArg.getLhs args
    from h es
  induction args with
  | nil => intro es; rfl
  | cons a rest ih =>
    intro es
    match a, es with
    | .inArg _, e :: es =>
      simp only [CallArg.replaceInArgs.go, CallArg.getLhs, List.filterMap_cons]; exact ih es
    | .inArg _, [] =>
      simp only [CallArg.replaceInArgs.go, CallArg.getLhs, List.filterMap_cons]; exact ih []
    | .inoutArg id, e :: es =>
      simp only [CallArg.replaceInArgs.go, CallArg.getLhs, List.filterMap_cons]; congr 1; exact ih es
    | .inoutArg id, [] =>
      simp only [CallArg.replaceInArgs.go, CallArg.getLhs, List.filterMap_cons]; congr 1; exact ih []
    | .outArg id, es =>
      simp only [CallArg.replaceInArgs.go, CallArg.getLhs, List.filterMap_cons]; congr 1; exact ih es

/-- `Statement.typeCheckCmd` preserves `modifiedVars` and `definedVars` (Command level). -/
theorem typeCheckCmd_modifiedVars (C : LContext CoreLParams) (Env Env' : TEnv Unit)
    (P : Program) (cmd cmd' : Command)
    (h : Statement.typeCheckCmd C Env P cmd = .ok (cmd', Env'))
    (h_wf : TEnvWF (T := CoreLParams) Env)
    (h_fwf : FactoryWF C.functions)
    (h_ne : Env.context.types ≠ []) :
    Command.modifiedVars cmd' = Command.modifiedVars cmd ∧
    Command.definedVars cmd' = Command.definedVars cmd := by
  cases cmd with
  | cmd c =>
    simp only [Statement.typeCheckCmd, Bind.bind, Except.bind] at h
    elim_err h; rename_i v h_tc
    obtain ⟨c', Env_inner⟩ := v
    cases h
    obtain ⟨hm, hd⟩ := cmd_typeCheck_modifiedVars C Env Env_inner c c' h_tc
    simp only [Command.modifiedVars, Command.definedVars, hm, hd, and_self]
  | call pname callArgs md =>
    obtain ⟨proc, Env_lhs, v1, v2, v3, v4, _, h_cmd, _, _, _, _, _, _, _⟩ :=
      typeCheckCmd_call_inversion C Env P pname callArgs md cmd' Env' h h_wf h_fwf h_ne
    subst h_cmd
    simp only [Command.modifiedVars, Command.definedVars, getLhs_replaceInArgs, and_self]

/-- `Block.modifiedVars` distributes over list append. -/
theorem block_modifiedVars_append (l1 l2 : List Statement) :
    Block.modifiedVars (l1 ++ l2) = Block.modifiedVars l1 ++ Block.modifiedVars l2 := by
  induction l1 with
  | nil => rfl
  | cons s rest ih =>
    simp only [List.cons_append, Block.modifiedVars.eq_2, ih, List.append_assoc]

/-- `Block.definedVars` distributes over list append. -/
theorem block_definedVars_append (l1 l2 : List Statement) (b : Bool) :
    Block.definedVars (l1 ++ l2) b = Block.definedVars l1 b ++ Block.definedVars l2 b := by
  induction l1 with
  | nil => simp only [List.nil_append, Block.definedVars.eq_1, List.nil_append]
  | cons s rest ih =>
    simp only [List.cons_append, Block.definedVars.eq_2, ih, List.append_assoc]

/-- The vars-preservation conclusion threaded through `typeCheckAux.go`. -/
def VarsPreserved (ss' acc ss : List Statement) : Prop :=
  Block.modifiedVars ss' = Block.modifiedVars acc.reverse ++ Block.modifiedVars ss ∧
  (∀ b, Block.definedVars ss' b = Block.definedVars acc.reverse b ++ Block.definedVars ss b)

/-- `typeCheckAux.go` preserves `modifiedVars`/`definedVars` (modulo the accumulator). -/
theorem typeCheckAux_go_vars (P : Program) (op : Option Procedure)
    (h_closed : CalledProcsClosed P)
    (C : LContext CoreLParams) (Env : TEnv Unit) (ss acc : List Statement) (labels : List String)
    (ss' : List Statement) (Env' : TEnv Unit) (C' : LContext CoreLParams)
    (h_wf : TEnvWF (T := CoreLParams) Env)
    (h_fwf : FactoryWF C.functions)
    (h_ne : Env.context.types ≠ [])
    (h_mono : ContextMono Env.context)
    (h_rigid_inv : ∀ v, v ∈ C.rigidTypeVars →
      LMonoTy.subst Env.stateSubstInfo.subst (.ftvar v) = .ftvar v)
    (h : Statement.typeCheckAux.go P op C Env ss acc labels = .ok (ss', Env', C')) :
    VarsPreserved ss' acc ss := by
  refine (Statement.typeCheckAux.go.induct P op
    (motive1 := fun C Env ss acc labels =>
      ∀ ss' Env' C',
      Statement.typeCheckAux.go P op C Env ss acc labels = .ok (ss', Env', C') →
      TEnvWF (T := CoreLParams) Env → FactoryWF C.functions →
      Env.context.types ≠ [] → ContextMono Env.context →
      (∀ v, v ∈ C.rigidTypeVars →
        LMonoTy.subst Env.stateSubstInfo.subst (.ftvar v) = .ftvar v) →
      VarsPreserved ss' acc ss)
    (motive2 := fun C Env bss acc labels =>
      ∀ ss' Env' C',
      Statement.typeCheckAux.goBlock P op C Env bss acc labels = .ok (ss', Env', C') →
      TEnvWF (T := CoreLParams) Env → FactoryWF C.functions →
      Env.context.types ≠ [] → ContextMono Env.context →
      (∀ v, v ∈ C.rigidTypeVars →
        LMonoTy.subst Env.stateSubstInfo.subst (.ftvar v) = .ftvar v) →
      VarsPreserved ss' acc bss)
    ?case_nil ?case_cmd ?case_block_clash ?case_block ?case_ite ?case_loop
    ?case_exit ?case_funcDecl ?case_typeDecl ?case_goBlock
    C Env ss acc labels) ss' Env' C' h h_wf h_fwf h_ne h_mono h_rigid_inv
  case case_nil =>
    intro C₀ Env₀ acc₀ labels₀ ss'₀ Env'₀ C'₀ h₀ hwf₀ hfwf₀ hne₀ hmono₀ hrigid₀
    simp only [Statement.typeCheckAux.go, Except.ok.injEq, Prod.mk.injEq] at h₀
    obtain ⟨hss, _, _⟩ := h₀
    subst hss
    refine ⟨?_, ?_⟩
    · simp only [Block.modifiedVars, List.append_nil]
    · intro b; simp only [Block.definedVars.eq_1, List.append_nil]
  case case_cmd =>
    intro C₀ Env₀ acc₀ labels₀ srest₀ cmd₀ ih ss'₀ Env'₀ C'₀ h₀ hwf₀ hfwf₀ hne₀ hmono₀ hrigid₀
    simp only [Statement.typeCheckAux.go, Bind.bind, Except.bind] at h₀
    cases h_tc : Statement.typeCheckCmd C₀ Env₀ P cmd₀ with
    | error e => rw [h_tc] at h₀; simp at h₀
    | ok v =>
      obtain ⟨c', Env_mid⟩ := v
      rw [h_tc] at h₀
      simp only at h₀
      obtain ⟨h_wf_mid, h_ne_mid, h_mono_mid, _, h_rigid_mid, _, _, _⟩ :=
        typeCheckCmd_preserves C₀ Env₀ P cmd₀ c' Env_mid h_tc hwf₀ hfwf₀ hne₀ hmono₀ hrigid₀ h_closed
      obtain ⟨hm_cmd, hd_cmd⟩ := typeCheckCmd_modifiedVars C₀ Env₀ Env_mid P cmd₀ c' h_tc hwf₀ hfwf₀ hne₀
      obtain ⟨ih_m, ih_d⟩ := ih (Stmt.cmd c') Env_mid C₀ ss'₀ Env'₀ C'₀ h₀ h_wf_mid hfwf₀ h_ne_mid h_mono_mid h_rigid_mid
      refine ⟨?_, ?_⟩
      · rw [ih_m]
        simp only [List.reverse_cons, block_modifiedVars_append, Block.modifiedVars.eq_2,
          Block.modifiedVars.eq_1, List.append_nil, Stmt.modifiedVars, HasVarsImp.modifiedVars,
          hm_cmd, List.append_assoc]
      · intro b
        rw [ih_d b]
        simp only [List.reverse_cons, block_definedVars_append, Block.definedVars.eq_2,
          Block.definedVars.eq_1, List.append_nil, Stmt.definedVars.eq_def, HasVarsImp.definedVars,
          hd_cmd, List.append_assoc]
  case case_block_clash =>
    intro C₀ Env₀ acc₀ labels₀ srest₀ label₀ bss₀ md₀ h_clash ih_tail ih_block
      ss'₀ Env'₀ C'₀ h_goeq hwf₀ hfwf₀ hne₀ hmono₀ hrigid₀
    rw [Statement.typeCheckAux.go] at h_goeq
    simp only [h_clash, if_true, Bind.bind, Except.bind] at h_goeq
    exact absurd h_goeq (by simp)
  case case_block =>
    intro C₀ Env₀ acc₀ labels₀ srest₀ label₀ bss₀ md₀ h_noclash ih_tail ih_block
      ss'₀ Env'₀ C'₀ h_goeq hwf₀ hfwf₀ hne₀ hmono₀ hrigid₀
    rw [Statement.typeCheckAux.go] at h_goeq
    simp only [h_noclash, if_false, Bool.false_eq_true, Bind.bind, Except.bind] at h_goeq
    cases h_blk : Statement.typeCheckAux.goBlock P op C₀ Env₀ bss₀ [] (label₀ :: labels₀) with
    | error e => rw [h_blk] at h_goeq; simp [pure, Except.pure] at h_goeq
    | ok v =>
      obtain ⟨bss', Env_blk, C_blk⟩ := v
      rw [h_blk] at h_goeq
      simp only [pure, Except.pure] at h_goeq
      obtain ⟨h_head, h_Cblk⟩ :=
        goBlock_eq_GoPreserved P op C₀ Env₀ bss₀ [] (label₀ :: labels₀) bss' Env_blk C_blk
          h_blk hwf₀ hfwf₀ hne₀ hmono₀ hrigid₀ h_closed
      subst h_Cblk
      obtain ⟨hm_blk, hd_blk⟩ := ih_block bss' Env_blk C_blk h_blk hwf₀ hfwf₀ hne₀ hmono₀ hrigid₀
      obtain ⟨ih_m, ih_d⟩ := ih_tail (Stmt.block label₀ bss' md₀) Env_blk C_blk ss'₀ Env'₀ C'₀ h_goeq
        h_head.wf h_head.fwf h_head.ne h_head.mono h_head.rigid_inv
      refine ⟨?_, ?_⟩
      · rw [ih_m]
        simp only [List.reverse_cons, block_modifiedVars_append, Block.modifiedVars.eq_2,
          Block.modifiedVars.eq_1, List.append_nil, Stmt.modifiedVars, List.append_assoc]
        rw [hm_blk]
        simp only [List.reverse_nil, Block.modifiedVars.eq_1, List.nil_append]
      · intro b
        rw [ih_d b]
        simp only [List.reverse_cons, block_definedVars_append, Block.definedVars.eq_2,
          Block.definedVars.eq_1, List.append_nil, List.append_assoc]
        congr 1
        cases b with
        | true => simp only [Stmt.definedVars.eq_def, if_true]
        | false =>
          simp only [Stmt.definedVars.eq_def]
          rw [hd_blk false]
          simp only [List.reverse_nil, Block.definedVars.eq_1, List.nil_append]
  case case_ite =>
    intro C₀ Env₀ acc₀ labels₀ srest₀ cond₀ tss₀ ess₀ md₀ ih_tail ih_branches
      ss'₀ Env'₀ C'₀ h_goeq hwf₀ hfwf₀ hne₀ hmono₀ hrigid₀
    unfold Statement.typeCheckAux.go at h_goeq
    simp only [Bind.bind, Except.bind, tryCatchThe, tryCatch, MonadExcept.tryCatch,
      MonadExceptOf.tryCatch, Except.tryCatch, Except.mapError] at h_goeq
    cases cond₀ with
    | det c =>
      simp only at h_goeq ih_branches
      obtain ⟨ih_then, ih_else⟩ := ih_branches
      cases h_fvc : Env₀.freeVarCheck c (Std.format "[" ++ Std.format (Stmt.ite (ExprOrNondet.det c) tss₀ ess₀ md₀) ++ Std.format "]") with
      | error e => rw [h_fvc] at h_goeq; simp only [reduceCtorEq] at h_goeq
      | ok _ =>
        rw [h_fvc] at h_goeq
        simp only at h_goeq
        cases h_res : LExpr.resolve C₀ Env₀ c with
        | error e => rw [h_res] at h_goeq; simp only [reduceCtorEq] at h_goeq
        | ok vr =>
          obtain ⟨conda, Env_r⟩ := vr
          rw [h_res] at h_goeq
          simp only at h_goeq
          cases h_cac : CmdType.checkAnnotCompat C₀ Env_r with
          | error e => rw [h_cac] at h_goeq; simp only [reduceCtorEq] at h_goeq
          | ok _ =>
            rw [h_cac] at h_goeq
            simp only at h_goeq
            elim_err h_goeq with v heq
            obtain ⟨h_condty, h_blocks⟩ :=
              condty_bool_match_ok conda.toLMonoTy _ _ _ v heq
            have h_rigid_r : ∀ w, w ∈ C₀.rigidTypeVars →
                LMonoTy.subst Env_r.stateSubstInfo.subst (.ftvar w) = .ftvar w :=
              CmdType.checkAnnotCompat_rigid C₀ Env_r h_cac
            have h_res_pres : GoPreserved C₀ C₀ Env₀ Env_r :=
              resolve_GoPreserved C₀ Env₀ Env_r c conda h_res hwf₀ hfwf₀ hne₀ hmono₀ h_rigid_r
            cases h_t : Statement.typeCheckAux.goBlock P op C₀ Env_r tss₀ [] labels₀ with
            | error e => rw [h_t] at h_blocks; simp only [reduceCtorEq] at h_blocks
            | ok vt =>
              obtain ⟨tss', Env_t, C_t⟩ := vt
              rw [h_t] at h_blocks
              simp only at h_blocks
              obtain ⟨h_t_pres, h_Ct⟩ :=
                goBlock_eq_GoPreserved P op C₀ Env_r tss₀ [] labels₀ tss' Env_t C_t h_t
                  h_res_pres.wf h_res_pres.fwf h_res_pres.ne h_res_pres.mono h_res_pres.rigid_inv h_closed
              obtain ⟨hm_t, hd_t⟩ := ih_then Env_r tss' Env_t C_t h_t h_res_pres.wf h_res_pres.fwf
                h_res_pres.ne h_res_pres.mono h_res_pres.rigid_inv
              rw [h_Ct] at h_blocks
              cases h_e : Statement.typeCheckAux.goBlock P op C₀ Env_t ess₀ [] labels₀ with
              | error e => rw [h_e] at h_blocks; simp only [reduceCtorEq] at h_blocks
              | ok ve =>
                obtain ⟨ess', Env_e, C_e⟩ := ve
                rw [h_e] at h_blocks
                simp only [Except.ok.injEq] at h_blocks
                obtain ⟨h_e_pres, h_Ce⟩ :=
                  goBlock_eq_GoPreserved P op C₀ Env_t ess₀ [] labels₀ ess' Env_e C_e h_e
                    h_t_pres.wf h_t_pres.fwf h_t_pres.ne h_t_pres.mono h_t_pres.rigid_inv h_closed
                obtain ⟨hm_e, hd_e⟩ := ih_else Env_t C₀ ess' Env_e C_e h_e h_t_pres.wf h_t_pres.fwf
                  h_t_pres.ne h_t_pres.mono h_t_pres.rigid_inv
                subst h_blocks
                simp only at h_goeq
                rw [h_Ce] at h_goeq
                obtain ⟨ih_m, ih_d⟩ :=
                  ih_tail (Stmt.ite (.det (unresolved conda)) tss' ess' md₀) Env_e C₀
                    ss'₀ Env'₀ C'₀ h_goeq h_e_pres.wf h_e_pres.fwf h_e_pres.ne h_e_pres.mono
                    h_e_pres.rigid_inv
                refine ⟨?_, ?_⟩
                · rw [ih_m]
                  simp only [List.reverse_cons, block_modifiedVars_append, Block.modifiedVars.eq_2,
                    Block.modifiedVars.eq_1, List.append_nil, Stmt.modifiedVars, List.append_assoc]
                  rw [hm_t, hm_e]
                  simp only [List.reverse_nil, Block.modifiedVars.eq_1, List.nil_append]
                · intro b
                  rw [ih_d b]
                  simp only [List.reverse_cons, block_definedVars_append, Block.definedVars.eq_2,
                    Block.definedVars.eq_1, List.append_nil, List.append_assoc]
                  congr 1
                  cases b with
                  | true => simp only [Stmt.definedVars.eq_def, if_true]
                  | false =>
                    simp only [Stmt.definedVars.eq_def]
                    rw [hd_t false, hd_e false]
                    simp only [List.reverse_nil, Block.definedVars.eq_1, List.nil_append]
    | nondet =>
      simp only at h_goeq ih_branches
      obtain ⟨ih_then, ih_else⟩ := ih_branches
      cases h_t : Statement.typeCheckAux.goBlock P op C₀ Env₀ tss₀ [] labels₀ with
      | error e => rw [h_t] at h_goeq; simp only [reduceCtorEq] at h_goeq
      | ok vt =>
        obtain ⟨tss', Env_t, C_t⟩ := vt
        rw [h_t] at h_goeq
        simp only at h_goeq
        cases h_e : Statement.typeCheckAux.goBlock P op C_t Env_t ess₀ [] labels₀ with
        | error e => rw [h_e] at h_goeq; simp only [reduceCtorEq] at h_goeq
        | ok ve =>
          obtain ⟨ess', Env_e, C_e⟩ := ve
          rw [h_e] at h_goeq
          simp only at h_goeq
          obtain ⟨h_t_pres, h_Ct⟩ :=
            goBlock_eq_GoPreserved P op C₀ Env₀ tss₀ [] labels₀ tss' Env_t C_t h_t
              hwf₀ hfwf₀ hne₀ hmono₀ hrigid₀ h_closed
          obtain ⟨hm_t, hd_t⟩ := ih_then tss' Env_t C_t h_t hwf₀ hfwf₀ hne₀ hmono₀ hrigid₀
          rw [h_Ct] at h_e
          obtain ⟨h_e_pres, h_Ce⟩ :=
            goBlock_eq_GoPreserved P op C₀ Env_t ess₀ [] labels₀ ess' Env_e C_e h_e
              h_t_pres.wf h_t_pres.fwf h_t_pres.ne h_t_pres.mono h_t_pres.rigid_inv h_closed
          obtain ⟨hm_e, hd_e⟩ := ih_else Env_t C₀ ess' Env_e C_e h_e h_t_pres.wf h_t_pres.fwf
            h_t_pres.ne h_t_pres.mono h_t_pres.rigid_inv
          rw [h_Ce] at h_goeq
          obtain ⟨ih_m, ih_d⟩ :=
            ih_tail (Stmt.ite .nondet tss' ess' md₀) Env_e C₀ ss'₀ Env'₀ C'₀ h_goeq
              h_e_pres.wf h_e_pres.fwf h_e_pres.ne h_e_pres.mono h_e_pres.rigid_inv
          refine ⟨?_, ?_⟩
          · rw [ih_m]
            simp only [List.reverse_cons, block_modifiedVars_append, Block.modifiedVars.eq_2,
              Block.modifiedVars.eq_1, List.append_nil, Stmt.modifiedVars, List.append_assoc]
            rw [hm_t, hm_e]
            simp only [List.reverse_nil, Block.modifiedVars.eq_1, List.nil_append]
          · intro b
            rw [ih_d b]
            simp only [List.reverse_cons, block_definedVars_append, Block.definedVars.eq_2,
              Block.definedVars.eq_1, List.append_nil, List.append_assoc]
            congr 1
            cases b with
            | true => simp only [Stmt.definedVars.eq_def, if_true]
            | false =>
              simp only [Stmt.definedVars.eq_def]
              rw [hd_t false, hd_e false]
              simp only [List.reverse_nil, Block.definedVars.eq_1, List.nil_append]
  case case_loop =>
    intro C₀ Env₀ acc₀ labels₀ srest₀ guard₀ measure₀ invariant₀ bss₀ md₀ ih_tail ih_body
      ss'₀ Env'₀ C'₀ h_goeq hwf₀ hfwf₀ hne₀ hmono₀ hrigid₀
    unfold Statement.typeCheckAux.go at h_goeq
    simp only [Bind.bind, Except.bind, tryCatchThe, tryCatch, MonadExcept.tryCatch,
      MonadExceptOf.tryCatch, Except.tryCatch, Except.mapError] at h_goeq
    elim_err h_goeq with v heq
    have h_body := trycatch_ok _ _ v heq
    clear heq
    cases guard₀ with
    | det g =>
      simp only at h_body
      elim_err h_body with hfvc_v hfvc_eq
      elim_err h_body with res_v res_eq
      obtain ⟨ga, Env_g⟩ := res_v
      simp only [pure, Except.pure] at h_body
      obtain ⟨h_g_bool, h_body⟩ := guard_bool_if_ok _ _ _ _ h_body
      have h_res_g : LExpr.resolve C₀ Env₀ g = .ok (ga, Env_g) := by
        split at res_eq
        · simp only [reduceCtorEq] at res_eq
        · rename_i w h_rg
          rw [Except.ok.injEq] at res_eq; subst res_eq; exact h_rg
      have h_ctx_g : Env_g.context = Env₀.context :=
        resolve_preserves_context g ga C₀ Env₀ Env_g h_res_g hwf₀ hne₀ hfwf₀
      have h_abs_g : Subst.absorbs Env_g.stateSubstInfo.subst Env₀.stateSubstInfo.subst :=
        resolve_absorbs g ga C₀ Env₀ Env_g h_res_g hwf₀ hne₀ hfwf₀
      have h_wf_g : TEnvWF (T := CoreLParams) Env_g :=
        resolve_TEnvWF g ga C₀ Env₀ Env_g h_res_g hwf₀ hfwf₀
      have h_gen_g : Env_g.genEnv.genState.tyGen ≥ Env₀.genEnv.genState.tyGen :=
        resolve_genState_mono C₀ Env₀ Env_g g ga h_res_g hwf₀ hfwf₀
      have h_ne_g : Env_g.context.types ≠ [] := by rw [h_ctx_g]; exact hne₀
      have h_mono_g : ContextMono Env_g.context := by rw [h_ctx_g]; exact hmono₀
      elim_err h_body with mres mres_eq
      obtain ⟨mtOpt, Env_m⟩ := mres
      elim_err h_body with fres fres_eq
      obtain ⟨it, Env_inv⟩ := fres
      elim_err h_body with cac_v cac_eq
      simp only at fres_eq cac_eq h_body
      obtain ⟨h_ctx_m, h_abs_m, h_wf_m, h_gen_m⟩ :
          Env_m.context = Env_g.context ∧
          Subst.absorbs Env_m.stateSubstInfo.subst Env_g.stateSubstInfo.subst ∧
          TEnvWF (T := CoreLParams) Env_m ∧
          Env_m.genEnv.genState.tyGen ≥ Env_g.genEnv.genState.tyGen := by
        cases measure₀ with
        | none =>
          simp only [Except.ok.injEq, Prod.mk.injEq] at mres_eq
          obtain ⟨_, h_em⟩ := mres_eq
          subst h_em
          exact ⟨rfl, Subst.absorbs_refl _ Env_g.stateSubstInfo.isWF, h_wf_g, Nat.le_refl _⟩
        | some m =>
          simp only at mres_eq
          elim_err mres_eq with mfvc_v mfvc_eq
          elim_err mres_eq with mres_v mres_v_eq
          obtain ⟨ma, Env_ma⟩ := mres_v
          simp only [Except.ok.injEq, Prod.mk.injEq] at mres_eq
          obtain ⟨h_mt, h_em⟩ := mres_eq
          subst h_mt; subst h_em
          have h_res_m : LExpr.resolve C₀ Env_g m = .ok (ma, Env_ma) := by
            split at mres_v_eq
            · simp only [reduceCtorEq] at mres_v_eq
            · rename_i w h_rm
              rw [Except.ok.injEq] at mres_v_eq; subst mres_v_eq; exact h_rm
          exact ⟨resolve_preserves_context m ma C₀ Env_g Env_ma h_res_m h_wf_g h_ne_g hfwf₀,
            resolve_absorbs m ma C₀ Env_g Env_ma h_res_m h_wf_g h_ne_g hfwf₀,
            resolve_TEnvWF m ma C₀ Env_g Env_ma h_res_m h_wf_g hfwf₀,
            resolve_genState_mono C₀ Env_g Env_ma m ma h_res_m h_wf_g hfwf₀⟩
      have h_ne_m : Env_m.context.types ≠ [] := by rw [h_ctx_m]; exact h_ne_g
      have h_mono_m : ContextMono Env_m.context := by rw [h_ctx_m]; exact h_mono_g
      have h_gb : ∃ tb Env_loop C_loop,
          Statement.typeCheckAux.goBlock P op C₀ Env_inv bss₀ [] labels₀ = .ok (tb, Env_loop, C_loop) ∧
          v = (Stmt.loop (ExprOrNondet.det (unresolved ga)) (Option.map unresolved mtOpt)
                (List.map (fun x => (x.fst, unresolved x.snd)) it) tb md₀, Env_loop, C_loop) := by
        split at h_body
        · elim_err h_body with gbv h_gbeq
          obtain ⟨tb, Env_loop, C_loop⟩ := gbv
          rw [Except.ok.injEq] at h_body
          exact ⟨tb, Env_loop, C_loop, h_gbeq, h_body.symm⟩
        · elim_err h_body with gbv h_gbeq
          obtain ⟨tb, Env_loop, C_loop⟩ := gbv
          rw [Except.ok.injEq] at h_body
          exact ⟨tb, Env_loop, C_loop, h_gbeq, h_body.symm⟩
        · simp only [reduceCtorEq] at h_body
      obtain ⟨tb, Env_loop, C_loop, h_gb_eq, h_v⟩ := h_gb
      subst h_v
      obtain ⟨h_ctx_inv, h_abs_inv, h_wf_inv, h_gen_inv, _⟩ :
          Env_inv.context = Env_m.context ∧
          Subst.absorbs Env_inv.stateSubstInfo.subst Env_m.stateSubstInfo.subst ∧
          TEnvWF (T := CoreLParams) Env_inv ∧
          Env_inv.genEnv.genState.tyGen ≥ Env_m.genEnv.genState.tyGen ∧
          (∀ p, p ∈ invariant₀ → ∃ E_in E_out, TEnvWF (T := CoreLParams) E_in ∧
            E_in.context = Env_m.context ∧
            Subst.absorbs Env_inv.stateSubstInfo.subst E_out.stateSubstInfo.subst ∧
            ∃ ia, E_in.freeVarCheck p.2 (Std.format "[" ++
                Std.format (Stmt.loop (ExprOrNondet.det g) measure₀ invariant₀ bss₀ md₀) ++
                Std.format "]") = Except.ok () ∧
              LExpr.resolve C₀ E_in p.2 = Except.ok (ia, E_out) ∧ ia.toLMonoTy = LMonoTy.bool) := by
        refine foldlM_env_threading _ _ ?_ invariant₀ [] Env_m Env_inv it h_wf_m h_ne_m fres_eq
        intro accp E p accp' E' h_wf_E h_ne_E h_stepeq
        elim_err h_stepeq with sfvc_v sfvc_eq
        elim_err h_stepeq with sres_v sres_eq
        obtain ⟨ia, E_ia⟩ := sres_v
        have h_res_p : LExpr.resolve C₀ E p.2 = .ok (ia, E_ia) := by
          split at sres_eq
          · simp only [reduceCtorEq] at sres_eq
          · rename_i w h_rp
            rw [Except.ok.injEq] at sres_eq; subst sres_eq; exact h_rp
        have h_fvc_p : E.freeVarCheck p.2 (Std.format "[" ++
            Std.format (Stmt.loop (ExprOrNondet.det g) measure₀ invariant₀ bss₀ md₀) ++
            Std.format "]") = .ok () := by
          split at sfvc_eq
          · simp only [reduceCtorEq] at sfvc_eq
          · rename_i w h_fp
            rw [Except.ok.injEq] at sfvc_eq; subst sfvc_eq
            rw [show (() : Unit) = w from rfl]; exact h_fp
        split at h_stepeq
        · rename_i h_isbool
          rw [Except.ok.injEq, Prod.mk.injEq] at h_stepeq
          obtain ⟨_, h_E'⟩ := h_stepeq
          subst h_E'
          have h_bool : ia.toLMonoTy = LMonoTy.bool := by
            simp only [beq_iff_eq] at h_isbool; exact h_isbool
          exact ⟨resolve_preserves_context p.2 ia C₀ E E_ia h_res_p h_wf_E h_ne_E hfwf₀,
            resolve_absorbs p.2 ia C₀ E E_ia h_res_p h_wf_E h_ne_E hfwf₀,
            resolve_TEnvWF p.2 ia C₀ E E_ia h_res_p h_wf_E hfwf₀,
            resolve_genState_mono C₀ E E_ia p.2 ia h_res_p h_wf_E hfwf₀,
            ia, h_fvc_p, h_res_p, h_bool⟩
        · simp only [reduceCtorEq] at h_stepeq
      have h_rigid_inv : ∀ w, w ∈ C₀.rigidTypeVars →
          LMonoTy.subst Env_inv.stateSubstInfo.subst (.ftvar w) = .ftvar w :=
        CmdType.checkAnnotCompat_rigid C₀ Env_inv cac_eq
      have h_ctx_inv0 : Env_inv.context = Env₀.context := by
        rw [h_ctx_inv, h_ctx_m, h_ctx_g]
      have h_ne_inv : Env_inv.context.types ≠ [] := by rw [h_ctx_inv0]; exact hne₀
      have h_mono_inv : ContextMono Env_inv.context := by rw [h_ctx_inv0]; exact hmono₀
      obtain ⟨h_body_pres, h_Cloop⟩ :=
        goBlock_eq_GoPreserved P op C₀ Env_inv bss₀ [] labels₀ tb Env_loop C_loop h_gb_eq
          h_wf_inv hfwf₀ h_ne_inv h_mono_inv h_rigid_inv h_closed
      obtain ⟨hm_body, hd_body⟩ :=
        ih_body Env_inv tb Env_loop C_loop h_gb_eq h_wf_inv hfwf₀ h_ne_inv h_mono_inv h_rigid_inv
      rw [h_Cloop] at h_goeq
      obtain ⟨ih_m, ih_d⟩ :=
        ih_tail (Stmt.loop (ExprOrNondet.det (unresolved ga)) (Option.map unresolved mtOpt)
            (List.map (fun x => (x.fst, unresolved x.snd)) it) tb md₀) Env_loop C₀
          ss'₀ Env'₀ C'₀ h_goeq h_body_pres.wf h_body_pres.fwf h_body_pres.ne h_body_pres.mono
          h_body_pres.rigid_inv
      refine ⟨?_, ?_⟩
      · rw [ih_m]
        simp only [List.reverse_cons, block_modifiedVars_append, Block.modifiedVars.eq_2,
          Block.modifiedVars.eq_1, List.append_nil, Stmt.modifiedVars, List.append_assoc]
        rw [hm_body]
        simp only [List.reverse_nil, Block.modifiedVars.eq_1, List.nil_append]
      · intro b
        rw [ih_d b]
        simp only [List.reverse_cons, block_definedVars_append, Block.definedVars.eq_2,
          Block.definedVars.eq_1, List.append_nil, List.append_assoc]
        congr 1
        cases b with
        | true => simp only [Stmt.definedVars.eq_def, if_true]
        | false =>
          simp only [Stmt.definedVars.eq_def]
          rw [hd_body false]
          simp only [List.reverse_nil, Block.definedVars.eq_1, List.nil_append]
    | nondet =>
      simp only [pure, Except.pure] at h_body
      elim_err h_body with mres mres_eq
      obtain ⟨mtOpt, Env_m⟩ := mres
      elim_err h_body with fres fres_eq
      obtain ⟨it, Env_inv⟩ := fres
      elim_err h_body with cac_v cac_eq
      simp only at fres_eq cac_eq h_body
      obtain ⟨h_ctx_m, h_abs_m, h_wf_m, h_gen_m⟩ :
          Env_m.context = Env₀.context ∧
          Subst.absorbs Env_m.stateSubstInfo.subst Env₀.stateSubstInfo.subst ∧
          TEnvWF (T := CoreLParams) Env_m ∧
          Env_m.genEnv.genState.tyGen ≥ Env₀.genEnv.genState.tyGen := by
        cases measure₀ with
        | none =>
          simp only [Except.ok.injEq, Prod.mk.injEq] at mres_eq
          obtain ⟨_, h_em⟩ := mres_eq
          subst h_em
          exact ⟨rfl, Subst.absorbs_refl _ Env₀.stateSubstInfo.isWF, hwf₀, Nat.le_refl _⟩
        | some m =>
          simp only at mres_eq
          elim_err mres_eq with mfvc_v mfvc_eq
          elim_err mres_eq with mres_v mres_v_eq
          obtain ⟨ma, Env_ma⟩ := mres_v
          simp only [Except.ok.injEq, Prod.mk.injEq] at mres_eq
          obtain ⟨h_mt, h_em⟩ := mres_eq
          subst h_mt; subst h_em
          have h_res_m : LExpr.resolve C₀ Env₀ m = .ok (ma, Env_ma) := by
            split at mres_v_eq
            · simp only [reduceCtorEq] at mres_v_eq
            · rename_i w h_rm
              rw [Except.ok.injEq] at mres_v_eq; subst mres_v_eq; exact h_rm
          exact ⟨resolve_preserves_context m ma C₀ Env₀ Env_ma h_res_m hwf₀ hne₀ hfwf₀,
            resolve_absorbs m ma C₀ Env₀ Env_ma h_res_m hwf₀ hne₀ hfwf₀,
            resolve_TEnvWF m ma C₀ Env₀ Env_ma h_res_m hwf₀ hfwf₀,
            resolve_genState_mono C₀ Env₀ Env_ma m ma h_res_m hwf₀ hfwf₀⟩
      have h_ne_m : Env_m.context.types ≠ [] := by rw [h_ctx_m]; exact hne₀
      have h_mono_m : ContextMono Env_m.context := by rw [h_ctx_m]; exact hmono₀
      have h_gb : ∃ tb Env_loop C_loop,
          Statement.typeCheckAux.goBlock P op C₀ Env_inv bss₀ [] labels₀ = .ok (tb, Env_loop, C_loop) ∧
          v = (Stmt.loop ExprOrNondet.nondet (Option.map unresolved mtOpt)
                (List.map (fun x => (x.fst, unresolved x.snd)) it) tb md₀, Env_loop, C_loop) := by
        split at h_body
        · elim_err h_body with gbv h_gbeq
          obtain ⟨tb, Env_loop, C_loop⟩ := gbv
          rw [Except.ok.injEq] at h_body
          exact ⟨tb, Env_loop, C_loop, h_gbeq, h_body.symm⟩
        · elim_err h_body with gbv h_gbeq
          obtain ⟨tb, Env_loop, C_loop⟩ := gbv
          rw [Except.ok.injEq] at h_body
          exact ⟨tb, Env_loop, C_loop, h_gbeq, h_body.symm⟩
        · simp only [reduceCtorEq] at h_body
      obtain ⟨tb, Env_loop, C_loop, h_gb_eq, h_v⟩ := h_gb
      subst h_v
      obtain ⟨h_ctx_inv, h_abs_inv, h_wf_inv, h_gen_inv, _⟩ :
          Env_inv.context = Env_m.context ∧
          Subst.absorbs Env_inv.stateSubstInfo.subst Env_m.stateSubstInfo.subst ∧
          TEnvWF (T := CoreLParams) Env_inv ∧
          Env_inv.genEnv.genState.tyGen ≥ Env_m.genEnv.genState.tyGen ∧
          (∀ p, p ∈ invariant₀ → ∃ E_in E_out, TEnvWF (T := CoreLParams) E_in ∧
            E_in.context = Env_m.context ∧
            Subst.absorbs Env_inv.stateSubstInfo.subst E_out.stateSubstInfo.subst ∧
            ∃ ia, E_in.freeVarCheck p.2 (Std.format "[" ++
                Std.format (Stmt.loop ExprOrNondet.nondet measure₀ invariant₀ bss₀ md₀) ++
                Std.format "]") = Except.ok () ∧
              LExpr.resolve C₀ E_in p.2 = Except.ok (ia, E_out) ∧ ia.toLMonoTy = LMonoTy.bool) := by
        refine foldlM_env_threading _ _ ?_ invariant₀ [] Env_m Env_inv it h_wf_m h_ne_m fres_eq
        intro accp E p accp' E' h_wf_E h_ne_E h_stepeq
        elim_err h_stepeq with sfvc_v sfvc_eq
        elim_err h_stepeq with sres_v sres_eq
        obtain ⟨ia, E_ia⟩ := sres_v
        have h_res_p : LExpr.resolve C₀ E p.2 = .ok (ia, E_ia) := by
          split at sres_eq
          · simp only [reduceCtorEq] at sres_eq
          · rename_i w h_rp
            rw [Except.ok.injEq] at sres_eq; subst sres_eq; exact h_rp
        have h_fvc_p : E.freeVarCheck p.2 (Std.format "[" ++
            Std.format (Stmt.loop ExprOrNondet.nondet measure₀ invariant₀ bss₀ md₀) ++
            Std.format "]") = .ok () := by
          split at sfvc_eq
          · simp only [reduceCtorEq] at sfvc_eq
          · rename_i w h_fp
            rw [Except.ok.injEq] at sfvc_eq; subst sfvc_eq
            rw [show (() : Unit) = w from rfl]; exact h_fp
        split at h_stepeq
        · rename_i h_isbool
          rw [Except.ok.injEq, Prod.mk.injEq] at h_stepeq
          obtain ⟨_, h_E'⟩ := h_stepeq
          subst h_E'
          have h_bool : ia.toLMonoTy = LMonoTy.bool := by
            simp only [beq_iff_eq] at h_isbool; exact h_isbool
          exact ⟨resolve_preserves_context p.2 ia C₀ E E_ia h_res_p h_wf_E h_ne_E hfwf₀,
            resolve_absorbs p.2 ia C₀ E E_ia h_res_p h_wf_E h_ne_E hfwf₀,
            resolve_TEnvWF p.2 ia C₀ E E_ia h_res_p h_wf_E hfwf₀,
            resolve_genState_mono C₀ E E_ia p.2 ia h_res_p h_wf_E hfwf₀,
            ia, h_fvc_p, h_res_p, h_bool⟩
        · simp only [reduceCtorEq] at h_stepeq
      have h_rigid_inv : ∀ w, w ∈ C₀.rigidTypeVars →
          LMonoTy.subst Env_inv.stateSubstInfo.subst (.ftvar w) = .ftvar w :=
        CmdType.checkAnnotCompat_rigid C₀ Env_inv cac_eq
      have h_ctx_inv0 : Env_inv.context = Env₀.context := by rw [h_ctx_inv, h_ctx_m]
      have h_ne_inv : Env_inv.context.types ≠ [] := by rw [h_ctx_inv0]; exact hne₀
      have h_mono_inv : ContextMono Env_inv.context := by rw [h_ctx_inv0]; exact hmono₀
      obtain ⟨h_body_pres, h_Cloop⟩ :=
        goBlock_eq_GoPreserved P op C₀ Env_inv bss₀ [] labels₀ tb Env_loop C_loop h_gb_eq
          h_wf_inv hfwf₀ h_ne_inv h_mono_inv h_rigid_inv h_closed
      obtain ⟨hm_body, hd_body⟩ :=
        ih_body Env_inv tb Env_loop C_loop h_gb_eq h_wf_inv hfwf₀ h_ne_inv h_mono_inv h_rigid_inv
      rw [h_Cloop] at h_goeq
      obtain ⟨ih_m, ih_d⟩ :=
        ih_tail (Stmt.loop ExprOrNondet.nondet (Option.map unresolved mtOpt)
            (List.map (fun x => (x.fst, unresolved x.snd)) it) tb md₀) Env_loop C₀
          ss'₀ Env'₀ C'₀ h_goeq h_body_pres.wf h_body_pres.fwf h_body_pres.ne h_body_pres.mono
          h_body_pres.rigid_inv
      refine ⟨?_, ?_⟩
      · rw [ih_m]
        simp only [List.reverse_cons, block_modifiedVars_append, Block.modifiedVars.eq_2,
          Block.modifiedVars.eq_1, List.append_nil, Stmt.modifiedVars, List.append_assoc]
        rw [hm_body]
        simp only [List.reverse_nil, Block.modifiedVars.eq_1, List.nil_append]
      · intro b
        rw [ih_d b]
        simp only [List.reverse_cons, block_definedVars_append, Block.definedVars.eq_2,
          Block.definedVars.eq_1, List.append_nil, List.append_assoc]
        congr 1
        cases b with
        | true => simp only [Stmt.definedVars.eq_def, if_true]
        | false =>
          simp only [Stmt.definedVars.eq_def]
          rw [hd_body false]
          simp only [List.reverse_nil, Block.definedVars.eq_1, List.nil_append]
  case case_exit =>
    intro C₀ Env₀ acc₀ labels₀ srest₀ l₀ md₀ ih_tail ss'₀ Env'₀ C'₀ h_goeq hwf₀ hfwf₀ hne₀ hmono₀ hrigid₀
    unfold Statement.typeCheckAux.go at h_goeq
    simp only [Bind.bind, Except.bind, tryCatchThe, tryCatch, MonadExcept.tryCatch,
      MonadExceptOf.tryCatch, Except.tryCatch] at h_goeq
    cases op with
    | none => simp only [reduceCtorEq] at h_goeq
    | some proc =>
      by_cases h_lbl : labels₀.contains l₀
      · simp only [h_lbl, if_true] at h_goeq
        obtain ⟨ih_m, ih_d⟩ :=
          ih_tail (Stmt.exit l₀ md₀) Env₀ C₀ ss'₀ Env'₀ C'₀ h_goeq hwf₀ hfwf₀ hne₀ hmono₀ hrigid₀
        refine ⟨?_, ?_⟩
        · rw [ih_m]
          simp only [List.reverse_cons, block_modifiedVars_append, Block.modifiedVars.eq_2,
            Block.modifiedVars.eq_1, List.append_nil, List.nil_append, Stmt.modifiedVars]
        · intro b
          rw [ih_d b]
          simp only [List.reverse_cons, block_definedVars_append, Block.definedVars.eq_2,
            Block.definedVars.eq_1, List.append_nil, List.nil_append, Stmt.definedVars.eq_def]
      · simp only [h_lbl, if_false, Bool.false_eq_true, reduceCtorEq] at h_goeq
  case case_funcDecl =>
    intro C₀ Env₀ acc₀ labels₀ srest₀ decl₀ md₀ ih_tail ss'₀ Env'₀ C'₀ h_goeq hwf₀ hfwf₀ hne₀ hmono₀ hrigid₀
    obtain ⟨func0, func, Env_mid, decl', h_rec, h_of, h_ft, h_tail_eq⟩ :=
      Statement.typeCheckAux_go_funcDecl_inv P op C₀ Env₀ decl₀ md₀ srest₀ acc₀ labels₀
        ss'₀ Env'₀ C'₀ h_goeq
    have h_ctx : Env_mid.context = Env₀.context :=
      Function.typeCheck_context_eq C₀ Env₀ func0 func Env_mid h_ft hwf₀ hfwf₀
    have h_lfwf : Lambda.LFuncWF func.toLFunc :=
      Function.typeCheck_LFuncWF C₀ Env₀ func0 func Env_mid h_ft hwf₀
    have h_absorbs : Subst.absorbs Env_mid.stateSubstInfo.subst Env₀.stateSubstInfo.subst :=
      Function.typeCheck_absorbs C₀ Env₀ func0 func Env_mid h_ft hwf₀ hfwf₀
    have h_head : GoPreserved C₀ (C₀.addFactoryFunction func.toLFunc) Env₀ Env_mid := by
      refine ⟨Function.typeCheck_TEnvWF C₀ Env₀ func0 func Env_mid h_ft hwf₀ hfwf₀,
        addFactoryFunction_FactoryWF C₀ func.toLFunc hfwf₀ h_lfwf, ?_, ?_, h_absorbs,
        addFactoryFunction_rigidTypeVars C₀ func.toLFunc, ?_, ?_, ?_,
        Function.typeCheck_tyGen_mono C₀ Env₀ func0 func Env_mid h_ft hwf₀ hfwf₀⟩
      · rw [h_ctx]; exact hne₀
      · rw [h_ctx]; exact hmono₀
      · exact Function.typeCheck_preserves_rigid_inv C₀ Env₀ func0 func Env_mid h_ft hwf₀ hfwf₀ hrigid₀
      · rw [h_ctx]
      · rw [h_ctx]
    have h_rigid_mid : ∀ v, v ∈ (C₀.addFactoryFunction func.toLFunc).rigidTypeVars →
        LMonoTy.subst Env_mid.stateSubstInfo.subst (.ftvar v) = .ftvar v := by
      rw [addFactoryFunction_rigidTypeVars]; exact h_head.rigid_inv
    obtain ⟨ih_m, ih_d⟩ :=
      ih_tail (Stmt.funcDecl decl' md₀) Env_mid (C₀.addFactoryFunction func.toLFunc) ss'₀ Env'₀ C'₀
        h_tail_eq h_head.wf h_head.fwf h_head.ne h_head.mono h_rigid_mid
    refine ⟨?_, ?_⟩
    · rw [ih_m]
      simp only [List.reverse_cons, block_modifiedVars_append, Block.modifiedVars.eq_2,
        Block.modifiedVars.eq_1, List.append_nil, List.nil_append, Stmt.modifiedVars]
    · intro b
      rw [ih_d b]
      simp only [List.reverse_cons, block_definedVars_append, Block.definedVars.eq_2,
        Block.definedVars.eq_1, List.append_nil, List.nil_append, Stmt.definedVars.eq_def]
  case case_typeDecl =>
    intro C₀ Env₀ acc₀ labels₀ srest₀ tc₀ md₀ ih_tail ss'₀ Env'₀ C'₀ h_goeq hwf₀ hfwf₀ hne₀ hmono₀ hrigid₀
    unfold Statement.typeCheckAux.go at h_goeq
    simp only [Bind.bind, Except.bind, tryCatchThe, tryCatch, MonadExcept.tryCatch,
      MonadExceptOf.tryCatch, Except.tryCatch] at h_goeq
    cases h_add : C₀.addKnownTypeWithError { name := tc₀.name, metadata := tc₀.numargs }
        (md₀.toDiagnosticF (Std.format "Type '" ++ Std.format tc₀.name ++ Std.format "' is already declared")) with
    | error e => rw [h_add] at h_goeq; simp only [reduceCtorEq] at h_goeq
    | ok C_mid =>
      rw [h_add] at h_goeq
      simp only at h_goeq
      obtain ⟨h_fns, h_rig⟩ := addKnownTypeWithError_preserves C₀ C_mid _ _ h_add
      obtain ⟨ih_m, ih_d⟩ :=
        ih_tail (Stmt.typeDecl tc₀ md₀) Env₀ C_mid ss'₀ Env'₀ C'₀ h_goeq hwf₀ (h_fns ▸ hfwf₀)
          hne₀ hmono₀ (by rw [h_rig]; exact hrigid₀)
      refine ⟨?_, ?_⟩
      · rw [ih_m]
        simp only [List.reverse_cons, block_modifiedVars_append, Block.modifiedVars.eq_2,
          Block.modifiedVars.eq_1, List.append_nil, List.nil_append, Stmt.modifiedVars]
      · intro b
        rw [ih_d b]
        simp only [List.reverse_cons, block_definedVars_append, Block.definedVars.eq_2,
          Block.definedVars.eq_1, List.append_nil, List.nil_append, Stmt.definedVars.eq_def]
  case case_goBlock =>
    intro C₀ Env₀ bss₀ acc₀ labels₀ Env₁ ih_body ss'₀ Env'₀ C'₀ h_goeq hwf₀ hfwf₀ hne₀ hmono₀ hrigid₀
    unfold Statement.typeCheckAux.goBlock at h_goeq
    simp only [Bind.bind, Except.bind] at h_goeq
    cases h_body_run : Statement.typeCheckAux.go P op C₀ Env₀.pushEmptyContext bss₀ acc₀ labels₀ with
    | error e => rw [h_body_run] at h_goeq; simp only [reduceCtorEq] at h_goeq
    | ok v =>
      obtain ⟨bss', Env_body, C_body⟩ := v
      rw [h_body_run] at h_goeq
      simp only [Except.ok.injEq, Prod.mk.injEq] at h_goeq
      obtain ⟨hss, _, _⟩ := h_goeq
      subst hss
      have h_push_wf : TEnvWF (T := CoreLParams) Env₀.pushEmptyContext :=
        pushEmptyContext_TEnvWF Env₀ hwf₀
      have h_push_ne : Env₀.pushEmptyContext.context.types ≠ [] := by
        simp only [TEnv.pushEmptyContext, TEnv.updateContext, TEnv.context, Maps.push]
        exact List.cons_ne_nil _ _
      have h_push_mono : ContextMono Env₀.pushEmptyContext.context :=
        pushEmptyContext_ContextMono Env₀ hmono₀
      have h_push_rigid : ∀ v, v ∈ C₀.rigidTypeVars →
          LMonoTy.subst Env₀.pushEmptyContext.stateSubstInfo.subst (.ftvar v) = .ftvar v := by
        show ∀ v, v ∈ C₀.rigidTypeVars →
          LMonoTy.subst Env₀.stateSubstInfo.subst (.ftvar v) = .ftvar v
        exact hrigid₀
      exact ih_body bss' Env_body C_body h_body_run h_push_wf hfwf₀ h_push_ne h_push_mono h_push_rigid

/-- `Statement.typeCheck` (top level) preserves `modifiedVars`/`definedVars`. -/
theorem statement_typeCheck_vars (C : LContext CoreLParams) (Env : TEnv Unit)
    (P : Program) (op : Option Procedure) (ss ss' : List Statement) (Env' : TEnv Unit)
    (h_wf : TEnvWF (T := CoreLParams) Env)
    (h_fwf : FactoryWF C.functions)
    (h_ne : Env.context.types ≠ [])
    (h_mono : ContextMono Env.context)
    (h_rigid_inv : ∀ v, v ∈ C.rigidTypeVars →
      LMonoTy.subst Env.stateSubstInfo.subst (.ftvar v) = .ftvar v)
    (h_closed : CalledProcsClosed P)
    (h : Statement.typeCheck C Env P op ss = .ok (ss', Env')) :
    Block.modifiedVars ss' = Block.modifiedVars ss ∧
    (∀ b, Block.definedVars ss' b = Block.definedVars ss b) := by
  simp only [Statement.typeCheck, Statement.typeCheckAux, Bind.bind, Except.bind] at h
  cases h_aux : Statement.typeCheckAux.go P op C Env ss [] [] with
  | error e => rw [h_aux] at h; simp only [reduceCtorEq] at h
  | ok w =>
    obtain ⟨ssA, Env_aux, C_aux⟩ := w
    rw [h_aux] at h
    simp only [Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨h_ss', _⟩ := h
    obtain ⟨hm_aux, hd_aux⟩ :=
      typeCheckAux_go_vars P op h_closed C Env ss [] [] ssA Env_aux C_aux
        h_wf h_fwf h_ne h_mono h_rigid_inv h_aux
    simp only [List.reverse_nil, Block.modifiedVars.eq_1, List.nil_append] at hm_aux
    refine ⟨?_, ?_⟩
    · rw [← h_ss', Statement.subst_go_nil, subst_block_modifiedVars, hm_aux]
    · intro b
      have hd_aux_b := hd_aux b
      simp only [List.reverse_nil, Block.definedVars.eq_1, List.nil_append] at hd_aux_b
      rw [← h_ss', Statement.subst_go_nil, subst_block_definedVars, hd_aux_b]


/-! ### `rigidVars_fixed_by_unify` — the fresh instantiation vars are fixed by the
    body-unify result (feeds `modRights`/`bodyTyped`'s rigid_inv). -/

/-- Per-step keys bound: when the constraint's LHS is a type variable `a` not already a key of
    `S`, `unifyOne`'s result keys are contained in `a :: keys S`. -/
theorem unifyOne_keys_ftvar_lhs (a : TyIdentifier) (t : LMonoTy) (S : SubstInfo)
    (relS : ValidSubstRelation [(LMonoTy.ftvar a, t)] S)
    (h : Constraint.unifyOne (LMonoTy.ftvar a, t) S = .ok relS)
    (h_a : a ∉ Maps.keys S.subst) :
    Maps.keys relS.newS.subst ⊆ a :: Maps.keys S.subst := by
  rw [Constraint.unifyOne.eq_def] at h
  simp only at h
  split at h
  · -- reflexive: newS = S
    simp only [Except.ok.injEq] at h
    subst h
    exact List.subset_cons_of_subset a (fun x hx => hx)
  · -- ftvar a, orig branch
    rename_i h_neq
    split at h
    · -- ftvar a == subst S t : newS = S
      simp only [Except.ok.injEq] at h
      subst h
      exact List.subset_cons_of_subset a (fun x hx => hx)
    · split at h
      · -- occurs check: error, contradiction
        simp only [reduceCtorEq] at h
      · -- match on find? S.subst a
        split at h
        · -- some sty : impossible since find? = none
          rename_i sty h_find
          rw [Maps.not_mem_keys_find?_none' S.subst a h_a] at h_find
          simp only [reduceCtorEq] at h_find
        · -- none branch: insert a
          simp only [Except.ok.injEq] at h
          subst h
          show Maps.keys (Maps.insert (Subst.apply [(a, _)] S.subst) a _)
            ⊆ a :: Maps.keys S.subst
          have h_ins := Maps.insert_keys_subset (Subst.apply [(a, LMonoTy.subst S.subst t)] S.subst)
            (key := a) (val := LMonoTy.subst S.subst t)
          rw [Subst.keys_of_apply_eq] at h_ins
          exact h_ins

/-- LHS type variables of a constraint list. -/
def lhsVars (cs : Constraints) : List TyIdentifier :=
  cs.filterMap (fun p => match p.1 with | .ftvar a => some a | _ => none)

/-- When every constraint's LHS is a type variable, those LHS vars are distinct, and none is
    already a key of `S_in`, the only new keys `unifyCore` adds are those LHS variables — so a
    `w` that is neither a key of `S_in` nor an LHS variable stays a non-key.

    `h_lhs_fresh` is essential: it forces `Maps.find? S a = none` at each head, killing the
    `some sty` branch of `unifyOne` that could otherwise add arbitrary keys. -/
theorem unifyCore_keys_orient : ∀ (cs : Constraints) (S_in : SubstInfo)
    (relS : ValidSubstRelation cs S_in),
    Constraints.unifyCore cs S_in = .ok relS →
    (∀ p, p ∈ cs → ∃ a, p.1 = LMonoTy.ftvar a) →
    (∀ p, p ∈ cs → ∀ a, p.1 = LMonoTy.ftvar a → a ∉ Maps.keys S_in.subst) →
    (lhsVars cs).Nodup →
    ∀ (w : TyIdentifier), w ∉ Maps.keys S_in.subst →
    (∀ p, p ∈ cs → ∀ a, p.1 = LMonoTy.ftvar a → w ≠ a) →
    w ∉ Maps.keys relS.newS.subst := by
  intro cs
  induction cs with
  | nil =>
    intro S_in relS h _ _ _ w h_w _
    rw [Constraints.unifyCore.eq_def] at h; simp only at h
    simp only [Except.ok.injEq] at h; subst h
    exact h_w
  | cons c rest ih =>
    obtain ⟨c1, c2⟩ := c
    intro S_in relS h h_ftvar h_fresh h_nodup w h_w h_wlhs
    -- Expose head var a with c1 = ftvar a.
    obtain ⟨a, h_c1⟩ := h_ftvar (c1, c2) (List.mem_cons_self)
    simp only at h_c1; subst h_c1
    -- Decompose unifyCore on (ftvar a, c2) :: rest.
    rw [Constraints.unifyCore.eq_def] at h; simp only at h
    simp only [Bind.bind, Except.bind, Except.mapError] at h
    split at h
    · simp only [reduceCtorEq] at h
    · rename_i relS_one h_one_raw
      have h_one := Lambda.Except.mapError_ok_h' h_one_raw
      split at h
      · simp only [reduceCtorEq] at h
      · rename_i relS_rest h_rest
        simp only [Except.ok.injEq] at h; subst h
        have h_a_S : a ∉ Maps.keys S_in.subst :=
          h_fresh (LMonoTy.ftvar a, c2) (List.mem_cons_self) a rfl
        have h_step := unifyOne_keys_ftvar_lhs a c2 S_in relS_one h_one h_a_S
        have h_lhs_cons : lhsVars ((LMonoTy.ftvar a, c2) :: rest) = a :: lhsVars rest := by
          simp only [lhsVars, List.filterMap_cons]
        rw [h_lhs_cons] at h_nodup
        -- Re-establish the hypotheses for `rest` with `S = relS_one.newS`.
        have h_ftvar_rest : ∀ p, p ∈ rest → ∃ b, p.1 = LMonoTy.ftvar b :=
          fun p hp => h_ftvar p (List.mem_cons_of_mem _ hp)
        have h_fresh_rest : ∀ p, p ∈ rest → ∀ b, p.1 = LMonoTy.ftvar b →
            b ∉ Maps.keys relS_one.newS.subst := by
          intro p hp b hb hcontra
          have h_b_step := h_step hcontra
          rcases List.mem_cons.mp h_b_step with h_ba | h_bS
          · -- b = a : contradicts Nodup (b is in lhsVars rest, a is head)
            subst h_ba
            have h_b_in : b ∈ lhsVars rest := by
              simp only [lhsVars, List.mem_filterMap]
              exact ⟨p, hp, by rw [hb]⟩
            exact (List.nodup_cons.mp h_nodup).1 h_b_in
          · -- b ∈ keys S_in : contradicts h_fresh
            exact h_fresh p (List.mem_cons_of_mem _ hp) b hb h_bS
        have h_nodup_rest : (lhsVars rest).Nodup := (List.nodup_cons.mp h_nodup).2
        have h_w_rest : w ∉ Maps.keys relS_one.newS.subst := by
          intro hcontra
          rcases List.mem_cons.mp (h_step hcontra) with h_wa | h_wS
          · exact h_wlhs (LMonoTy.ftvar a, c2) (List.mem_cons_self) a rfl h_wa
          · exact h_w h_wS
        have h_wlhs_rest : ∀ p, p ∈ rest → ∀ b, p.1 = LMonoTy.ftvar b → w ≠ b :=
          fun p hp b hb => h_wlhs p (List.mem_cons_of_mem _ hp) b hb
        exact ih relS_one.newS relS_rest h_rest h_ftvar_rest h_fresh_rest h_nodup_rest
          w h_w_rest h_wlhs_rest

/-- Wrapper at the `unify` level. -/
theorem unify_keys_orient (cs : Constraints) (S_in S_out : SubstInfo)
    (h : Constraints.unify cs S_in = .ok S_out)
    (h_lhs_ftvar : ∀ p, p ∈ cs → ∃ a, p.1 = LMonoTy.ftvar a)
    (h_lhs_fresh : ∀ p, p ∈ cs → ∀ a, p.1 = LMonoTy.ftvar a → a ∉ Maps.keys S_in.subst)
    (h_nodup : (lhsVars cs).Nodup)
    (w : TyIdentifier)
    (h_w_notin_S : w ∉ Maps.keys S_in.subst)
    (h_w_notin_lhs : ∀ p, p ∈ cs → ∀ a, p.1 = LMonoTy.ftvar a → w ≠ a) :
    w ∉ Maps.keys S_out.subst := by
  simp only [Constraints.unify, bind, Except.bind] at h
  split at h
  · simp only [reduceCtorEq] at h
  · rename_i relS h_core
    simp only [Except.ok.injEq] at h; subst h
    exact unifyCore_keys_orient cs S_in relS h_core h_lhs_ftvar h_lhs_fresh h_nodup
      w h_w_notin_S h_w_notin_lhs

/-- Fresh RHS type variables introduced by `tyArgSubst` are fixed points of the
    unifying substitution `S_out`. -/
theorem rigidVars_fixed_by_unify
    (S_in S_out : SubstInfo) (tyArgSubst : Subst)
    (h_unify : Constraints.unify (tyArgSubst.flatten.map (fun kv => (LMonoTy.ftvar kv.1, kv.2))) S_in
      = .ok S_out)
    -- Fresh RHS vars are not keys of the incoming subst.
    (h_fresh_notin : ∀ id, (∃ k, (k, LMonoTy.ftvar id) ∈ tyArgSubst.flatten) →
      id ∉ Maps.keys S_in.subst)
    -- Fresh RHS vars are distinct from the declared (LHS) vars.
    (h_fresh_ne_lhs : ∀ id, (∃ k, (k, LMonoTy.ftvar id) ∈ tyArgSubst.flatten) →
      ∀ k, (∃ t, (k, t) ∈ tyArgSubst.flatten) → id ≠ k)
    -- Declared (LHS) vars are not keys of the incoming subst.
    (h_orig_notin_S : ∀ k, (∃ t, (k, t) ∈ tyArgSubst.flatten) → k ∉ Maps.keys S_in.subst)
    -- Provenance (call-site discharge): declared (LHS) vars are pairwise distinct.
    (h_orig_nodup : (tyArgSubst.flatten.map (fun kv => kv.1)).Nodup)
    (v : TyIdentifier)
    (h_v : v ∈ tyArgSubst.flatten.filterMap (fun kv => match kv.2 with
      | LMonoTy.ftvar id => some id | _ => none)) :
    LMonoTy.subst S_out.subst (LMonoTy.ftvar v) = LMonoTy.ftvar v := by
  have h_v_prov : ∃ k, (k, LMonoTy.ftvar v) ∈ tyArgSubst.flatten := by
    obtain ⟨kv, h_mem, h_eq⟩ := List.mem_filterMap.mp h_v
    split at h_eq
    · rename_i id heq
      simp only [Option.some.injEq] at h_eq
      subst h_eq
      refine ⟨kv.1, ?_⟩
      rw [← heq]
      exact h_mem
    · simp only [reduceCtorEq] at h_eq
  have h_v_notin_S : v ∉ Maps.keys S_in.subst := h_fresh_notin v h_v_prov
  have h_lhs_ftvar : ∀ p, p ∈ tyArgSubst.flatten.map (fun kv => (LMonoTy.ftvar kv.1, kv.2)) →
      ∃ a, p.1 = LMonoTy.ftvar a := by
    intro p hp
    obtain ⟨kv, _, h_p⟩ := List.mem_map.mp hp
    exact ⟨kv.1, by rw [← h_p]⟩
  have h_cs_mem : ∀ p, p ∈ tyArgSubst.flatten.map (fun kv => (LMonoTy.ftvar kv.1, kv.2)) →
      ∃ kv : TyIdentifier × LMonoTy, (kv.1, kv.2) ∈ tyArgSubst.flatten ∧
        p = (LMonoTy.ftvar kv.1, kv.2) := by
    intro p hp
    obtain ⟨kv, h_kv_mem, h_p⟩ := List.mem_map.mp hp
    exact ⟨kv, h_kv_mem, h_p.symm⟩
  have h_lhs_fresh : ∀ p, p ∈ tyArgSubst.flatten.map (fun kv => (LMonoTy.ftvar kv.1, kv.2)) →
      ∀ a, p.1 = LMonoTy.ftvar a → a ∉ Maps.keys S_in.subst := by
    intro p hp a ha
    obtain ⟨kv, h_kv_mem, h_peq⟩ := h_cs_mem p hp
    rw [h_peq] at ha; simp only [LMonoTy.ftvar.injEq] at ha; subst ha
    exact h_orig_notin_S kv.1 ⟨kv.2, h_kv_mem⟩
  have h_lhsVars_eq : lhsVars (tyArgSubst.flatten.map (fun kv => (LMonoTy.ftvar kv.1, kv.2)))
      = tyArgSubst.flatten.map (fun kv => kv.1) := by
    simp only [lhsVars, List.filterMap_map, Function.comp_def]
    induction tyArgSubst.flatten with
    | nil => rfl
    | cons a l ih => simp only [List.filterMap_cons, List.map_cons, ih]
  have h_nodup : (lhsVars (tyArgSubst.flatten.map (fun kv => (LMonoTy.ftvar kv.1, kv.2)))).Nodup := by
    rw [h_lhsVars_eq]; exact h_orig_nodup
  have h_v_notin_lhs : ∀ p, p ∈ tyArgSubst.flatten.map (fun kv => (LMonoTy.ftvar kv.1, kv.2)) →
      ∀ a, p.1 = LMonoTy.ftvar a → v ≠ a := by
    intro p hp a ha
    obtain ⟨kv, h_kv_mem, h_peq⟩ := h_cs_mem p hp
    rw [h_peq] at ha; simp only [LMonoTy.ftvar.injEq] at ha; subst ha
    exact h_fresh_ne_lhs v h_v_prov kv.1 ⟨kv.2, h_kv_mem⟩
  have h_v_notkey : v ∉ Maps.keys S_out.subst :=
    unify_keys_orient _ S_in S_out h_unify h_lhs_ftvar h_lhs_fresh h_nodup
      v h_v_notin_S h_v_notin_lhs
  apply LMonoTy.subst_no_relevant_keys
  intro x hx
  have h_xv : x = v := by
    simp only [LMonoTy.freeVars, List.mem_singleton] at hx; exact hx
  subst h_xv
  exact h_v_notkey


/-- Every variable a type-checked procedure's body modifies is an output or body-local
    (the `modRights` field of `ProcHasType'`). -/
theorem Procedure.typeCheck_modRights (C : LContext CoreLParams) (Env : TEnv Unit)
    (P : Program) (proc proc' : Procedure) (Env' : TEnv Unit) (md : MetaData Expression)
    (h : Procedure.typeCheck C Env P proc md = .ok (proc', Env'))
    (h_wf : TEnvWF (T := CoreLParams) Env)
    (h_fwf : FactoryWF C.functions)
    (h_resolved : TContext.AliasesResolved Env.context)
    (h_mono : ContextMono Env.context)
    (h_closed : CalledProcsClosed P) :
    ∀ v, v ∈ HasVarsImp.modifiedVars (P := Expression) proc'.body →
      v ∈ proc'.header.outputs.keys ++
          HasVarsImp.definedVars (P := Expression) proc'.body false := by
  unfold Procedure.typeCheck at h
  simp only [Procedure.checkNoDuplicates,
    Procedure.checkModificationRights, Bind.bind, Except.bind, pure, Except.pure] at h
  -- checkNoDuplicates (one match on a nested-if discriminant).
  split at h
  · simp only [reduceCtorEq] at h
  · -- checkTypeArgsWF (folded: peel with a named hypothesis).
    elim_err h with h_ta
    · -- checkModificationRights is `match (if oldDef then err else if modif then err else ok) with …`.
      -- Peel the outer `match`; the ok-branch's guard equation `h_mr` carries both nested `if`s,
      -- so split it twice (both error branches contradict `= ok`), leaving the modification-empty fact.
      split at h
      · simp only [reduceCtorEq] at h
      · rename_i _ _ h_mr
        split at h_mr
        · simp only [reduceCtorEq] at h_mr
        split at h_mr
        · simp only [reduceCtorEq] at h_mr
        · rename_i h_empty_neg
          have h_filter_empty : (List.filter
              (fun v => !(ListMap.keys proc.header.outputs ++
                (HasVarsImp.definedVars (P := Expression) proc.body false).eraseDups).contains v)
              (HasVarsImp.modifiedVars (P := Expression) proc.body).eraseDups) = [] := by
            rw [← List.isEmpty_iff]
            simpa using h_empty_neg
          rw [List.filter_eq_nil_iff] at h_filter_empty
          have h_guard : ∀ w, w ∈ HasVarsImp.modifiedVars (P := Expression) proc.body →
              w ∈ ListMap.keys proc.header.outputs ++
                  HasVarsImp.definedVars (P := Expression) proc.body false := by
            intro w hw
            have hw_ed : w ∈ (HasVarsImp.modifiedVars (P := Expression) proc.body).eraseDups :=
              List.mem_eraseDups.mpr hw
            have h_not := h_filter_empty w hw_ed
            have h_mem : w ∈ (ListMap.keys proc.header.outputs ++
                (HasVarsImp.definedVars (P := Expression) proc.body false).eraseDups) := by
              rw [← List.contains_iff_mem]
              simp only [Bool.not_eq_true, Bool.not_eq_false'] at h_not
              exact h_not
            rcases List.mem_append.mp h_mem with h_out | h_def
            · exact List.mem_append_left _ h_out
            · exact List.mem_append_right _ (List.mem_eraseDups.mp h_def)
          clear h_empty_neg h_filter_empty
          elim_err h
          rename_i v_setup h_setup
          elim_err h with v_pre h_pre
          elim_err h
          rename_i v_out h_out
          elim_err h with v_post h_post
          split at h
          · rename_i ss h_body
            elim_err h with v_unify h_unify
            split at h
            · simp at h
            rename_i h_rigid_none
            elim_err h with v_body h_stc
            injection h with h_pair
            injection h_pair with h_proc _
            subst h_proc
            have h_tc := Lambda.Except.mapError_ok_h' h_stc
            have h_ra := Lambda.Except.mapError_ok_h' h_out
            have h_penv := postEnv_wf C Env proc _ v_setup v_pre v_out h_ta h_setup h_pre h_ra
              h_wf h_fwf h_resolved
            have h_E4mono := E4_ContextMono C Env proc _ v_setup v_pre v_out h_setup h_pre h_ra
              h_wf h_fwf h_mono
            have h_cs_fresh := procBody_cs_fresh C Env proc _ v_setup v_pre v_out v_post
              h_ta h_setup h_pre h_ra h_post h_wf h_fwf h_resolved
            have h_unify' := Lambda.Except.mapError_ok_h' h_unify
            have h_bwf := procBodyEnv_wf C _ proc v_post _ v_unify h_post h_unify' h_cs_fresh
              h_penv.1 h_penv.2.1 h_E4mono h_penv.2.2 h_fwf
            have h_rigid_inv : ∀ w, w ∈ (List.filterMap
                (fun x => match x.snd with | LMonoTy.ftvar id => some id | x => none)
                (List.flatten v_setup.2.snd)) →
              LMonoTy.subst (v_post.snd.updateSubst v_unify).stateSubstInfo.subst (.ftvar w) = .ftvar w := by
              intro w hw
              have h_all := List.find?_eq_none.mp h_rigid_none w hw
              simpa only [bne_iff_ne, ne_eq, Decidable.not_not] using h_all
            obtain ⟨hb_wf, hb_ne, hb_mono, _⟩ := h_bwf
            have hb_fwf : FactoryWF C.functions := h_fwf
            have hb_rigid := h_rigid_inv
            have hb_closed : CalledProcsClosed P := h_closed
            obtain ⟨h_bm, h_bd⟩ :=
              statement_typeCheck_vars
                { functions := C.functions, datatypes := C.datatypes, knownTypes := C.knownTypes,
                  idents := C.idents,
                  rigidTypeVars := List.filterMap
                    (fun x => match x.snd with | LMonoTy.ftvar id => some id | x => none)
                    (List.flatten v_setup.2.snd) }
                (v_post.snd.updateSubst v_unify) P (some proc) ss v_body.fst v_body.snd
                hb_wf hb_fwf hb_ne hb_mono hb_rigid hb_closed h_tc
            have h_len : (ListMap.keys proc.header.outputs).length ≤ v_out.fst.length := by
              have h_len_ra := resolveAliasesList_length _ _ _ _ h_ra
              rw [h_len_ra, List.length_map, ListMap.keys_eq_map_fst,
                ListMap.values_eq_map_snd, List.length_map, List.length_map]
              exact Nat.le_refl _
            have h_keys : ListMap.keys (List.map
                (fun x => (x.fst, LMonoTy.subst
                  ([List.filterMap (fun x => match x.snd with
                    | LMonoTy.ftvar fresh => some (fresh, LMonoTy.ftvar x.fst) | x => none)
                    (List.flatten v_setup.2.snd)]) x.snd))
                ((ListMap.keys proc.header.outputs).zip v_out.fst))
                = ListMap.keys proc.header.outputs := by
              rw [ListMap.keys_eq_map_fst, List.map_map]
              have h_ml := List.map_congr_left
                (l := (ListMap.keys proc.header.outputs).zip v_out.fst)
                (f := (Prod.fst ∘ fun x : CoreIdent × LMonoTy =>
                  (x.fst, LMonoTy.subst
                    ([List.filterMap (fun x => match x.snd with
                      | LMonoTy.ftvar fresh => some (fresh, LMonoTy.ftvar x.fst) | x => none)
                      (List.flatten v_setup.2.snd)]) x.snd)))
                (g := Prod.fst) (fun p _ => rfl)
              rw [h_ml, List.map_fst_zip h_len]
            intro v hv
            simp only [HasVarsImp.modifiedVars, HasVarsImp.definedVars,
              subst_block_modifiedVars, subst_block_definedVars, h_bm, h_bd] at hv ⊢
            have h_gm : v ∈ HasVarsImp.modifiedVars (P := Expression) proc.body := by
              rw [h_body]; exact hv
            have h_res := h_guard v h_gm
            rw [h_body] at h_res
            -- Rewrite `outputs.keys` forward to the annotated (subst-renamed) keys.
            rw [← h_keys] at h_res
            exact h_res
          · simp at h


open Lambda.LTy.Syntax in
/-- Helper: every check produced by `updateCheckExprs.go` (when the expr list
    and the check list have equal length) has its `.expr` drawn from `es`. -/
theorem updateCheckExprs_go_expr_mem (es : List Expression.Expr) (checks : List Procedure.Check)
    (h_len : es.length = checks.length)
    (c : Procedure.Check) (hc : c ∈ Procedure.Spec.updateCheckExprs.go es checks) :
    c.expr ∈ es := by
  induction es generalizing checks with
  | nil =>
    cases checks with
    | nil =>
      rw [Procedure.Spec.updateCheckExprs.go] at hc
      exact absurd hc (List.not_mem_nil)
    | cons ch crest => simp only [List.length_nil, List.length_cons] at h_len; omega
  | cons e erest ih =>
    cases checks with
    | nil => simp only [List.length_cons, List.length_nil] at h_len; omega
    | cons ch crest =>
      rw [Procedure.Spec.updateCheckExprs.go] at hc
      rw [List.mem_cons] at hc
      cases hc with
      | inl h_eq => subst h_eq; exact List.mem_cons_self
      | inr h_rest =>
        have h_len' : erest.length = crest.length := by
          simp only [List.length_cons, Nat.add_right_cancel_iff] at h_len; exact h_len
        exact List.mem_cons_of_mem e (ih crest h_len' h_rest)

/-- Helper: every check in `(updateCheckExprs es conds).values` has its `.expr`
    drawn from `es`, given the lengths agree. -/
theorem updateCheckExprs_values_expr_mem (es : List Expression.Expr)
    (conds : ListMap CoreLabel Procedure.Check)
    (h_len : es.length = conds.values.length)
    (c : Procedure.Check) (hc : c ∈ (Procedure.Spec.updateCheckExprs es conds).values) :
    c.expr ∈ es := by
  rw [ListMap.values_eq_map_snd, Procedure.Spec.updateCheckExprs] at hc
  rw [List.mem_map] at hc
  obtain ⟨p, hp_mem, hp_eq⟩ := hc
  have h_in_go : c ∈ Procedure.Spec.updateCheckExprs.go es conds.values := by
    rw [← hp_eq]; exact (List.of_mem_zip hp_mem).2
  exact updateCheckExprs_go_expr_mem es conds.values h_len c h_in_go

open Lambda.LTy.Syntax in
/-- Every expression accumulated by `typeCheckConditions.go` is annotated-typed as
    `bool` (`HasTypeA [] e bool`), provided the accumulator's elements already are. -/
theorem typeCheckConditions_go_HasTypeA (C : Core.Expression.TyContext) (procName : CoreIdent)
    (conds : List (CoreLabel × Core.Procedure.Check)) (acc : Array Expression.Expr)
    (Env : Core.Expression.TyEnv) (res : Array Expression.Expr × Core.Expression.TyEnv)
    (h : Core.Procedure.typeCheckConditions.go C procName conds acc Env = .ok res)
    (h_wf : TEnvWF (T := CoreLParams) Env)
    (h_fwf : FactoryWF C.functions)
    (h_resolved : TContext.AliasesResolved Env.context)
    (h_acc : ∀ e ∈ acc.toList, LExpr.HasTypeA [] e mty[bool]) :
    ∀ e ∈ res.1.toList, LExpr.HasTypeA [] e mty[bool] := by
  induction conds generalizing acc Env with
  | nil =>
    simp only [Core.Procedure.typeCheckConditions.go] at h
    cases h; exact h_acc
  | cons pair rest ih =>
    obtain ⟨name, condition⟩ := pair
    simp only [Core.Procedure.typeCheckConditions.go, Bind.bind, Except.bind,
      Except.mapError] at h
    cases h_res : Lambda.LExpr.resolve C Env condition.expr with
    | error e => rw [h_res] at h; simp only [reduceCtorEq] at h
    | ok v_res =>
      obtain ⟨annotatedExpr, newEnv⟩ := v_res
      rw [h_res] at h
      simp only at h
      split at h
      · simp only [reduceCtorEq] at h
      · rename_i h_guard
        have h_ty_eq : annotatedExpr.toLMonoTy = mty[bool] := by
          simp only [bne_iff_ne, ne_eq, Decidable.not_not] at h_guard
          exact h_guard
        have h_ht : LExpr.HasTypeA [] annotatedExpr.unresolved annotatedExpr.toLMonoTy :=
          Lambda.resolve_HasTypeA condition.expr annotatedExpr C Env newEnv h_res h_wf h_fwf h_resolved
        have h_ht_bool : LExpr.HasTypeA [] annotatedExpr.unresolved mty[bool] := by
          rw [h_ty_eq] at h_ht; exact h_ht
        have h_newwf : TEnvWF (T := CoreLParams) newEnv :=
          Lambda.resolve_TEnvWF condition.expr annotatedExpr C Env newEnv h_res h_wf h_fwf
        have h_newresolved : TContext.AliasesResolved newEnv.context :=
          (Lambda.resolve_properties condition.expr annotatedExpr C Env newEnv h_res h_wf h_fwf h_resolved).2.1
        have h_acc' : ∀ e ∈ (acc.push annotatedExpr.unresolved).toList,
            LExpr.HasTypeA [] e mty[bool] := by
          intro e he
          rw [Array.toList_push, List.mem_append] at he
          cases he with
          | inl h_in_acc => exact h_acc e h_in_acc
          | inr h_in_new =>
            rw [List.mem_singleton] at h_in_new
            rw [h_in_new]; exact h_ht_bool
        exact ih (acc.push annotatedExpr.unresolved) newEnv h h_newwf h_newresolved h_acc'

open Lambda.LTy.Syntax in
/-- Top-level wrapper: every expression in the result array of `typeCheckConditions`
    is annotated-typed as `bool`. -/
theorem typeCheckConditions_HasTypeA (C : Core.Expression.TyContext) (Env : Core.Expression.TyEnv)
    (conditions : ListMap CoreLabel Core.Procedure.Check) (procName : CoreIdent)
    (res : Array Expression.Expr × Core.Expression.TyEnv)
    (h : Core.Procedure.typeCheckConditions C Env conditions procName = .ok res)
    (h_wf : TEnvWF (T := CoreLParams) Env)
    (h_fwf : FactoryWF C.functions)
    (h_resolved : TContext.AliasesResolved Env.context) :
    ∀ e ∈ res.1.toList, LExpr.HasTypeA [] e mty[bool] := by
  simp only [Core.Procedure.typeCheckConditions] at h
  exact typeCheckConditions_go_HasTypeA C procName conditions #[] Env res h h_wf h_fwf h_resolved
    (by intro e he; simp only [List.not_mem_nil] at he)

/-- Length of the result array of `typeCheckConditions.go`: one element per condition. -/
theorem typeCheckConditions_go_length (C : Core.Expression.TyContext) (procName : CoreIdent)
    (conds : List (CoreLabel × Core.Procedure.Check)) (acc : Array Expression.Expr)
    (Env : Core.Expression.TyEnv) (res : Array Expression.Expr × Core.Expression.TyEnv)
    (h : Core.Procedure.typeCheckConditions.go C procName conds acc Env = .ok res) :
    res.1.size = acc.size + conds.length := by
  induction conds generalizing acc Env with
  | nil =>
    simp only [Core.Procedure.typeCheckConditions.go] at h
    cases h; simp only [List.length_nil, Nat.add_zero]
  | cons pair rest ih =>
    obtain ⟨name, condition⟩ := pair
    simp only [Core.Procedure.typeCheckConditions.go, Bind.bind, Except.bind,
      Except.mapError] at h
    cases h_res : Lambda.LExpr.resolve C Env condition.expr with
    | error e => rw [h_res] at h; simp only [reduceCtorEq] at h
    | ok v_res =>
      obtain ⟨annotatedExpr, newEnv⟩ := v_res
      rw [h_res] at h
      simp only at h
      split at h
      · simp only [reduceCtorEq] at h
      · rename_i h_guard
        have h_rec := ih (acc.push annotatedExpr.unresolved) newEnv h
        rw [h_rec]
        simp only [Array.size_push, List.length_cons]
        omega

/-- Top-level length wrapper. -/
theorem typeCheckConditions_length (C : Core.Expression.TyContext) (Env : Core.Expression.TyEnv)
    (conditions : ListMap CoreLabel Core.Procedure.Check) (procName : CoreIdent)
    (res : Array Expression.Expr × Core.Expression.TyEnv)
    (h : Core.Procedure.typeCheckConditions C Env conditions procName = .ok res) :
    res.1.size = conditions.length := by
  simp only [Core.Procedure.typeCheckConditions] at h
  have := typeCheckConditions_go_length C procName conditions #[] Env res h
  simpa using this

open Lambda.LTy.Syntax in
/-- Annotated `preconditionsTyped`: each output precondition is `bool` under the
    annotated judgment (context-free, so holds for any `Γ`). -/
theorem Procedure.typeCheck_preconditionsTyped_annotated (C : LContext CoreLParams) (Env : TEnv Unit)
    (P : Program) (proc proc' : Procedure) (Env' : TEnv Unit) (md : MetaData Expression)
    (h : Procedure.typeCheck C Env P proc md = .ok (proc', Env'))
    (h_wf : TEnvWF (T := CoreLParams) Env)
    (h_fwf : FactoryWF C.functions)
    (h_resolved : TContext.AliasesResolved Env.context) :
    ∀ Γ, ∀ c ∈ proc'.spec.preconditions.values,
      instHasTypeA.exprTyped C (procInputContext Γ proc') c.expr (instHasTypeA.embed .bool) := by
  intro Γ c hc
  simp only [Procedure.typeCheck, bind, Except.bind] at h
  elim_err h
  elim_err h
  elim_err h
  elim_err h with h_setup
  rename_i v_setup
  elim_err h with h_pre
  rename_i v_pre
  elim_err h
  elim_err h
  split at h
  · rename_i ss h_body
    elim_err h
    elim_err h
    split at h
    · simp at h
    elim_err h
    elim_err h
    injection h with h_pair
    injection h_pair with h_proc _
    subst h_proc
    simp only at hc
    have h_env_wf : TEnvWF (T := CoreLParams) v_setup.2.1 :=
      setupInputEnv_TEnvWF C Env proc _ v_setup h_setup h_wf
    have h_env_resolved : TContext.AliasesResolved v_setup.2.1.context :=
      setupInputEnv_AliasesResolved C Env proc _ v_setup h_setup h_resolved
    have h_all : ∀ e ∈ v_pre.1.toList, LExpr.HasTypeA [] e mty[bool] :=
      typeCheckConditions_HasTypeA C v_setup.2.1 proc.spec.preconditions proc.header.name
        v_pre h_pre h_env_wf h_fwf h_env_resolved
    have h_len_arr : v_pre.1.size = proc.spec.preconditions.length :=
      typeCheckConditions_length C v_setup.2.1 proc.spec.preconditions proc.header.name v_pre h_pre
    have h_len : v_pre.1.toList.length = proc.spec.preconditions.values.length := by
      rw [Array.length_toList, h_len_arr, ListMap.values_eq_map_snd, List.length_map]
    have h_mem : c.expr ∈ v_pre.1.toList :=
      updateCheckExprs_values_expr_mem v_pre.1.toList proc.spec.preconditions h_len c hc
    show LExpr.HasTypeA [] c.expr mty[bool]
    exact h_all c.expr h_mem
  · exact absurd h (by simp only [reduceCtorEq, not_false_eq_true])

open Lambda.LTy.Syntax in
/-- Annotated `postconditionsTyped`: each output postcondition is `bool` under the
    annotated judgment. -/
theorem Procedure.typeCheck_postconditionsTyped_annotated (C : LContext CoreLParams) (Env : TEnv Unit)
    (P : Program) (proc proc' : Procedure) (Env' : TEnv Unit) (md : MetaData Expression)
    (h : Procedure.typeCheck C Env P proc md = .ok (proc', Env'))
    (h_wf : TEnvWF (T := CoreLParams) Env)
    (h_fwf : FactoryWF C.functions)
    (h_resolved : TContext.AliasesResolved Env.context) :
    ∀ Γ, ∀ c ∈ proc'.spec.postconditions.values,
      instHasTypeA.exprTyped C (procBodyContext Γ proc') c.expr (instHasTypeA.embed .bool) := by
  intro Γ c hc
  simp only [Procedure.typeCheck, bind, Except.bind] at h
  elim_err h
  elim_err h with h_ta
  elim_err h
  elim_err h with h_setup
  rename_i v_setup
  elim_err h with h_pre
  rename_i v_pre
  elim_err h with h_out
  rename_i v_out
  elim_err h with h_post
  rename_i v_post
  split at h
  · rename_i ss h_body
    elim_err h
    elim_err h
    split at h
    · simp at h
    elim_err h
    elim_err h
    injection h with h_pair
    injection h_pair with h_proc _
    subst h_proc
    simp only at hc
    show LExpr.HasTypeA [] c.expr mty[bool]
    have h_len_arr : v_post.1.size = proc.spec.postconditions.length :=
      typeCheckConditions_length C _ proc.spec.postconditions proc.header.name v_post h_post
    have h_len : v_post.1.toList.length = proc.spec.postconditions.values.length := by
      rw [Array.length_toList, h_len_arr, ListMap.values_eq_map_snd, List.length_map]
    have h_mem : c.expr ∈ v_post.1.toList :=
      updateCheckExprs_values_expr_mem v_post.1.toList proc.spec.postconditions h_len c hc
    have h_ra := Lambda.Except.mapError_ok_h' h_out
    have h_penv := postEnv_wf C Env proc _ v_setup v_pre v_out h_ta h_setup h_pre h_ra
      h_wf h_fwf h_resolved
    exact typeCheckConditions_HasTypeA C _ proc.spec.postconditions proc.header.name
      v_post h_post h_penv.1 h_fwf h_penv.2.2 c.expr h_mem
  · exact absurd h (by simp only [reduceCtorEq, not_false_eq_true])


/-! ## Call-site shape lemmas: simplify the three filterMaps over
`flatten [ids.zip (freshtvs.map ftvar)]`. -/

/-- The `filterMap` extracting range vars recovers `freshtvs`. -/
theorem filterMap_rigid (ids freshtvs : List TyIdentifier) (h : ids.length = freshtvs.length) :
    List.filterMap (fun x => match x.snd with | LMonoTy.ftvar id => some id | _ => none)
      (List.flatten [ids.zip (freshtvs.map LMonoTy.ftvar)]) = freshtvs := by
  simp only [List.flatten_cons, List.flatten_nil, List.append_nil]
  induction ids generalizing freshtvs with
  | nil => cases freshtvs with | nil => rfl | cons => simp at h
  | cons a as ih =>
    cases freshtvs with
    | nil => simp at h
    | cons f fs => simp only [List.map_cons, List.zip_cons_cons, List.filterMap_cons]; rw [ih fs (by simpa using h)]

/-- The `filterMap` building the fresh→user renaming recovers `freshtvs.zip (ids.map ftvar)`. -/
theorem filterMap_userSubst (ids freshtvs : List TyIdentifier) (h : ids.length = freshtvs.length) :
    List.filterMap (fun x => match x.snd with
        | LMonoTy.ftvar fresh => some (fresh, LMonoTy.ftvar x.fst) | _ => none)
      (List.flatten [ids.zip (freshtvs.map LMonoTy.ftvar)])
      = freshtvs.zip (ids.map LMonoTy.ftvar) := by
  simp only [List.flatten_cons, List.flatten_nil, List.append_nil]
  induction ids generalizing freshtvs with
  | nil => cases freshtvs with | nil => rfl | cons => simp at h
  | cons a as ih =>
    cases freshtvs with
    | nil => simp at h
    | cons f fs => simp only [List.map_cons, List.zip_cons_cons, List.filterMap_cons]; rw [ih fs (by simpa using h)]

/-- The `filterMap` building the user→fresh renaming recovers `ids.zip (freshtvs.map ftvar)`. -/
theorem filterMap_invSubst (ids freshtvs : List TyIdentifier) (h : ids.length = freshtvs.length) :
    List.filterMap (fun x => match x.snd with
        | LMonoTy.ftvar fresh => some (x.fst, LMonoTy.ftvar fresh) | _ => none)
      (List.flatten [ids.zip (freshtvs.map LMonoTy.ftvar)])
      = ids.zip (freshtvs.map LMonoTy.ftvar) := by
  simp only [List.flatten_cons, List.flatten_nil, List.append_nil]
  induction ids generalizing freshtvs with
  | nil => cases freshtvs with | nil => rfl | cons => simp at h
  | cons a as ih =>
    cases freshtvs with
    | nil => simp at h
    | cons f fs => simp only [List.map_cons, List.zip_cons_cons, List.filterMap_cons]; rw [ih fs (by simpa using h)]



/-- The forward renaming `subst [ids.zip (freshtvs.map ftvar)]` inverts
    `subst [freshtvs.zip (ids.map ftvar)]` on any `v ∈ freshtvs`. -/
theorem userSubst_inv (ids freshtvs : List TyIdentifier)
    (h_len : ids.length = freshtvs.length) (h_ids_nodup : ids.Nodup)
    (v : TyIdentifier) (hv : v ∈ freshtvs) :
    LMonoTy.subst [ids.zip (freshtvs.map LMonoTy.ftvar)]
      (LMonoTy.subst [freshtvs.zip (ids.map LMonoTy.ftvar)] (.ftvar v)) = .ftvar v := by
  -- `subst_rename_inverse (ids:=freshtvs) (freshtvs:=ids)`: forward = userSubst, backward = invSubst.
  exact subst_rename_inverse freshtvs ids h_len.symm h_ids_nodup (.ftvar v)
    (by intro w hw; simp only [LMonoTy.freeVars, List.mem_singleton] at hw; subst hw; exact hv)

/-- `userSubst` is a renaming (every `ftvar` maps to some `ftvar`). -/
theorem userSubst_ren (ids freshtvs : List TyIdentifier) (v : TyIdentifier) :
    ∃ w, LMonoTy.subst [freshtvs.zip (ids.map LMonoTy.ftvar)] (.ftvar v) = .ftvar w :=
  subst_zip_ftvar_renaming freshtvs ids v

/-- A key in a map's `keys` has a `some` lookup. -/
theorem mem_keys_find?_isSome (m : Map TyIdentifier LMonoTy) (k : TyIdentifier)
    (hk : k ∈ Map.keys m) : (Map.find? m k).isSome := by
  induction m with
  | nil => simp [Map.keys] at hk
  | cons hd tl ih =>
    simp only [Map.find?, Map.keys] at hk ⊢
    split
    · rfl
    · rename_i hne
      rcases List.mem_cons.mp hk with h | h
      · exact absurd h.symm hne
      · exact ih h

/-- For `v ∈ freshtvs` (disjoint from `ids`), `v` is not a free var of any `userSubst`-image:
    `userSubst` maps each `ftvar` to itself (∉ freshtvs) or to some `ftvar ids[i]`. -/
theorem userSubst_rig_notin (ids freshtvs : List TyIdentifier)
    (h_len : ids.length = freshtvs.length)
    (h_disj : ∀ f ∈ freshtvs, f ∉ ids)
    (v : TyIdentifier) (hv : v ∈ freshtvs) (x : TyIdentifier) :
    v ∉ LMonoTy.freeVars (LMonoTy.subst [freshtvs.zip (ids.map LMonoTy.ftvar)] (.ftvar x)) := by
  rw [LMonoTy.subst_unfold]
  simp only [Maps.find?]
  cases h_f : Map.find? (freshtvs.zip (ids.map LMonoTy.ftvar)) x with
  | none =>
    -- result = ftvar x; find? none ⟹ x ∉ keys = freshtvs, so v ≠ x.
    simp only [LMonoTy.freeVars, List.mem_singleton]
    intro h_eq
    have h_keys : Map.keys (freshtvs.zip (ids.map LMonoTy.ftvar)) = freshtvs :=
      keys_zip_map_ftvar freshtvs ids h_len.symm
    have h_x_in : x ∈ Map.keys (freshtvs.zip (ids.map LMonoTy.ftvar)) := by
      rw [h_keys, ← h_eq]; exact hv
    have h_some := mem_keys_find?_isSome _ x h_x_in
    rw [h_f] at h_some; simp only [Option.isSome_none, Bool.false_eq_true] at h_some
  | some t =>
    have h_tval : t ∈ Map.values (freshtvs.zip (ids.map LMonoTy.ftvar)) := Map.find?_mem_values _ h_f
    simp only [List.zip] at h_tval
    rw [Map.values_zipWith_eq_take] at h_tval
    have h_tmem : t ∈ ids.map LMonoTy.ftvar := List.mem_of_mem_take h_tval
    obtain ⟨u, hu_mem, hu_eq⟩ := List.mem_map.mp h_tmem
    subst hu_eq
    simp only [LMonoTy.freeVars, List.mem_singleton]
    intro h_eq; subst h_eq
    exact h_disj v hv hu_mem

/-- Lifts a per-variable substitution-commutation fact (`h_base`) to arbitrary monotypes whose
    free vars lie in `mty0`. -/
theorem subst_pullback_gen (S : Subst) (σ σ' : Map TyIdentifier LMonoTy) (mty0 : LMonoTy)
    (h_base : ∀ v, v ∈ LMonoTy.freeVars mty0 →
      LMonoTy.subst [σ'] (LMonoTy.subst S (.ftvar v))
        = LMonoTy.subst S (LMonoTy.subst [σ] (.ftvar v))) :
    ∀ t, (∀ v, v ∈ LMonoTy.freeVars t → v ∈ LMonoTy.freeVars mty0) →
      LMonoTy.subst [σ'] (LMonoTy.subst S t)
        = LMonoTy.subst S (LMonoTy.subst [σ] t) := by
  intro t
  induction t with
  | ftvar x => intro hcl; exact h_base x (hcl x (by simp [LMonoTy.freeVars]))
  | bitvec n => intro _; rw [LMonoTy.subst_bitvec, LMonoTy.subst_bitvec, LMonoTy.subst_bitvec, LMonoTy.subst_bitvec]
  | tcons name args ih =>
    intro hcl
    rw [LMonoTy.subst_tcons, LMonoTy.subst_tcons, LMonoTy.subst_tcons, LMonoTy.subst_tcons]
    congr 1
    induction args with
    | nil => rw [LMonoTys.subst_nil, LMonoTys.subst_nil, LMonoTys.subst_nil, LMonoTys.subst_nil]
    | cons hd tl ihl =>
      have h_hd_cl : ∀ v, v ∈ hd.freeVars → v ∈ LMonoTy.freeVars mty0 :=
        fun v hv => hcl v (by simp only [LMonoTy.freeVars, LMonoTys.freeVars, List.mem_append]; left; exact hv)
      have h_tl_cl : ∀ v, v ∈ (LMonoTy.tcons name tl).freeVars → v ∈ LMonoTy.freeVars mty0 :=
        fun v hv => hcl v (by
          simp only [LMonoTy.freeVars, LMonoTys.freeVars, List.mem_append] at hv ⊢; right; exact hv)
      rw [subst_cons_eq', subst_cons_eq', subst_cons_eq', subst_cons_eq']
      rw [ih hd (.head _) h_hd_cl]
      congr 1
      exact ihl (fun a ha => ih a (.tail _ ha)) h_tl_cl

/-- `RigidAnnotCompat` is preserved by applying a renaming `S` to both sides, given `S` is a
    renaming on `mty0`'s free vars, invertible by `Sinv`, and disjoint from the rigid vars. -/
theorem RigidAnnotCompat_subst_both
    {aliases : List TypeAlias} {rigidVars : List TyIdentifier}
    {mty0 mty : LMonoTy} (S Sinv : Subst)
    (h : RigidAnnotCompat aliases rigidVars mty0 mty)
    (h_aw : ∀ a, a ∈ aliases → TypeAlias.WF a)
    (h_rig_disjoint : ∀ v, v ∈ rigidVars → v ∉ LMonoTy.freeVars (LMonoTy.subst S mty0))
    (h_ren : ∀ v, v ∈ LMonoTy.freeVars mty0 → ∃ w, LMonoTy.subst S (.ftvar v) = .ftvar w)
    (h_inv : ∀ v, v ∈ LMonoTy.freeVars mty0 →
      LMonoTy.subst Sinv (LMonoTy.subst S (.ftvar v)) = .ftvar v) :
    RigidAnnotCompat aliases rigidVars (LMonoTy.subst S mty0) (LMonoTy.subst S mty) := by
  obtain ⟨σ, h_σ_rigid, h_ae⟩ := h
  have h_ae_S := AliasEquiv_subst aliases (LMonoTy.subst [σ] mty0) mty S h_ae h_aw
  let g : TyIdentifier → LMonoTy :=
    fun w => LMonoTy.subst S (LMonoTy.subst [σ] (LMonoTy.subst Sinv (.ftvar w)))
  let σ' : Map TyIdentifier LMonoTy :=
    (LMonoTy.freeVars (LMonoTy.subst S mty0)).map (fun w => (w, g w))
  have h_keys : Map.keys σ' = LMonoTy.freeVars (LMonoTy.subst S mty0) := by
    show Map.keys ((LMonoTy.freeVars (LMonoTy.subst S mty0)).map (fun w => (w, g w))) = _
    rw [Map.keys_eq_map_fst]; simp [List.map_map]; apply List.map_id''; simp
  refine ⟨σ', ?_, ?_⟩
  · intro v hv
    have h_v_notin : v ∉ Map.keys σ' := h_keys ▸ h_rig_disjoint v hv
    have h_none : Map.find? σ' v = none := Map.find?_none_of_not_mem_keys' σ' v h_v_notin
    rw [LMonoTy.subst_unfold]
    show (match Maps.find? [σ'] v with | some sty => sty | none => .ftvar v) = .ftvar v
    simp only [Maps.find?, h_none]
  · have h_base : ∀ v, v ∈ LMonoTy.freeVars mty0 →
        LMonoTy.subst [σ'] (LMonoTy.subst S (.ftvar v))
          = LMonoTy.subst S (LMonoTy.subst [σ] (.ftvar v)) := by
      intro v hv
      obtain ⟨w, h_Sv⟩ := h_ren v hv
      rw [h_Sv]
      have h_w_mem : w ∈ LMonoTy.freeVars (LMonoTy.subst S mty0) := by
        have := LMonoTy.mem_freeVars_subst_of_mem S mty0 v hv w
        rw [h_Sv] at this; exact this (by simp [LMonoTy.freeVars])
      have h_find : Map.find? σ' w = some (g w) := Map.find?_of_map_self _ g w h_w_mem
      have h_ne : Subst.hasEmptyScopes [σ'] = false := by
        cases h_fv : LMonoTy.freeVars (LMonoTy.subst S mty0) with
        | nil => exact absurd (h_fv ▸ h_w_mem) (by simp)
        | cons a as =>
          show Subst.hasEmptyScopes [σ'] = false
          simp only [σ', h_fv, Subst.hasEmptyScopes, List.map, List.all_cons]
          unfold Map.isEmpty; simp
      rw [LMonoTy.subst_ftvar_eq [σ'] w (g w) h_ne (by simp only [Maps.find?, h_find])]
      show LMonoTy.subst S (LMonoTy.subst [σ] (LMonoTy.subst Sinv (.ftvar w))) = _
      have h_inv_w : LMonoTy.subst Sinv (.ftvar w) = .ftvar v := by rw [← h_Sv]; exact h_inv v hv
      rw [h_inv_w]
    have h_pull := subst_pullback_gen S σ σ' mty0 h_base mty0 (fun v hv => hv)
    rw [h_pull]; exact h_ae_S

/-- Every free var of `subst S mty` comes from substituting some free var of `mty`. -/
theorem freeVars_subst_mem_exists (S : Subst) (mty : LMonoTy) (w : TyIdentifier)
    (hw : w ∈ LMonoTy.freeVars (LMonoTy.subst S mty)) :
    ∃ v, v ∈ LMonoTy.freeVars mty ∧ w ∈ LMonoTy.freeVars (LMonoTy.subst S (.ftvar v)) := by
  induction mty with
  | ftvar x => exact ⟨x, by simp [LMonoTy.freeVars], hw⟩
  | bitvec n => rw [LMonoTy.subst_bitvec] at hw; simp [LMonoTy.freeVars] at hw
  | tcons name args ih =>
    rw [LMonoTy.subst_unfold] at hw
    simp only [LMonoTy.freeVars] at hw
    obtain ⟨b, hb_mem, hb_fv⟩ := LMonoTys.freeVars_exists hw
    obtain ⟨a, ha_mem, ha_eq⟩ := List.mem_map.mp hb_mem
    subst ha_eq
    obtain ⟨v, hv_mem, hv_fv⟩ := ih a ha_mem hb_fv
    exact ⟨v, by simp only [LMonoTy.freeVars]; exact LMonoTys.freeVars_mem_subset ha_mem hv_mem, hv_fv⟩

/-- `openFull`-of-monomorphic form of `RigidAnnotCompat_subst_both`. -/
theorem RigidAnnotCompat_openFull_mono_subst
    {aliases : List TypeAlias} {rigidVars : List TyIdentifier}
    {mty0 mty : LMonoTy} {tys : List LMonoTy} (S Sinv : Subst)
    (h : RigidAnnotCompat aliases rigidVars ((LTy.forAll [] mty0).openFull tys) mty)
    (h_aw : ∀ a, a ∈ aliases → TypeAlias.WF a)
    (h_rig_disjoint : ∀ v, v ∈ rigidVars → v ∉ LMonoTy.freeVars (LMonoTy.subst S mty0))
    (h_ren : ∀ v, v ∈ LMonoTy.freeVars mty0 → ∃ w, LMonoTy.subst S (.ftvar v) = .ftvar w)
    (h_inv : ∀ v, v ∈ LMonoTy.freeVars mty0 →
      LMonoTy.subst Sinv (LMonoTy.subst S (.ftvar v)) = .ftvar v) :
    RigidAnnotCompat aliases rigidVars
      (((LTy.subst S (LTy.forAll [] mty0)).openFull tys)) (LMonoTy.subst S mty) := by
  have h_collapse : ∀ (m : LMonoTy) (ts : List LMonoTy), (LTy.forAll [] m).openFull ts = m := by
    intro m ts
    unfold LTy.openFull LTy.boundVars LTy.toMonoTypeUnsafe
    rw [show List.zip ([] : List TyIdentifier) ts = [] from rfl]
    exact LMonoTy.subst_emptyS (by simp [Subst.hasEmptyScopes, Map.isEmpty])
  rw [LTy.subst_forAll_nil, h_collapse]; rw [h_collapse] at h
  exact RigidAnnotCompat_subst_both S Sinv h h_aw h_rig_disjoint h_ren h_inv



/-! ## InitClosed predicate: every `var`-init annotation is monomorphic with only rigid free vars. -/

/-- A command is init-closed: any `init` annotation is a closed monotype over the rigid vars. -/
def CmdInitClosed (rig : List TyIdentifier) (c : Cmd Expression) : Prop :=
  match c with
  | .init _ xty _ _ => xty.boundVars = [] ∧ (∀ v, v ∈ LMonoTy.freeVars xty.toMonoTypeUnsafe → v ∈ rig)
  | _ => True

/-- `CmdInitClosed` lifted to extended commands (calls are trivially init-closed). -/
def CommandInitClosed (rig : List TyIdentifier) (c : Command) : Prop :=
  match c with
  | .cmd c0 => CmdInitClosed rig c0
  | .call _ _ _ => True

/-- `CommandInitClosed` lifted structurally to statements. -/
def StmtInitClosed (rig : List TyIdentifier) (s : Statement) : Prop :=
  match s with
  | .cmd c => CommandInitClosed rig c
  | .block _ b _ => ∀ s ∈ b, StmtInitClosed rig s
  | .ite _ t e _ => (∀ s ∈ t, StmtInitClosed rig s) ∧ (∀ s ∈ e, StmtInitClosed rig s)
  | .loop _ _ _ b _ => ∀ s ∈ b, StmtInitClosed rig s
  | .exit _ _ => True
  | .funcDecl _ _ => True
  | .typeDecl _ _ => True

abbrev StmtsInitClosed (rig : List TyIdentifier) (ss : List Statement) : Prop :=
  ∀ s ∈ ss, StmtInitClosed rig s

/-! ## Corrected SubstReq: S is a renaming with left-inverse on rigid vars. -/

structure SubstReq (C : LContext CoreLParams) (Γ : TContext Unit) (S Sinv : Subst) : Prop where
  ren : ∀ v, ∃ w, LMonoTy.subst S (.ftvar v) = .ftvar w
  rig_notin_range : ∀ v, v ∈ C.rigidTypeVars → ∀ x, v ∉ LMonoTy.freeVars (LMonoTy.subst S (.ftvar x))
  inv_on_rigid : ∀ v, v ∈ C.rigidTypeVars → LMonoTy.subst Sinv (LMonoTy.subst S (.ftvar v)) = .ftvar v
  aliasesWF : ∀ a, a ∈ Γ.aliases → TypeAlias.WF a

/-- Derive the three transport hypotheses for a mono-init annotation whose free vars
    are all rigid, from a `SubstReq`. -/
theorem init_transport {C : LContext CoreLParams} {Γ : TContext Unit} {S Sinv : Subst}
    (hS : SubstReq C Γ S Sinv) (mty0 : LMonoTy)
    (h_closed : ∀ v, v ∈ LMonoTy.freeVars mty0 → v ∈ C.rigidTypeVars) :
    (∀ v, v ∈ C.rigidTypeVars → v ∉ LMonoTy.freeVars (LMonoTy.subst S mty0)) ∧
    (∀ v, v ∈ LMonoTy.freeVars mty0 → ∃ w, LMonoTy.subst S (.ftvar v) = .ftvar w) ∧
    (∀ v, v ∈ LMonoTy.freeVars mty0 → LMonoTy.subst Sinv (LMonoTy.subst S (.ftvar v)) = .ftvar v) := by
  refine ⟨?_, ?_, ?_⟩
  · intro v hv h_in
    obtain ⟨u, hu_mem, hu_fv⟩ := freeVars_subst_mem_exists S mty0 v h_in
    exact hS.rig_notin_range v hv u hu_fv
  · intro v _; exact hS.ren v
  · intro v hv; exact hS.inv_on_rigid v (h_closed v hv)

/-- `CmdHasTypeA` is preserved under applying a rigid-respecting renaming `S` to the command
    and both contexts (given the command is init-closed). -/
theorem CmdHasTypeA_subst (C : LContext CoreLParams) (Γ Γ' : TContext Unit)
    (c : Cmd Expression) (S Sinv : Subst)
    (h : CmdHasTypeA C Γ c Γ')
    (hS : SubstReq C Γ S Sinv)
    (h_ic : CmdInitClosed C.rigidTypeVars c) :
    CmdHasTypeA C (TContext.subst Γ S) (Core.Statement.Cmd.subst S c) (TContext.subst Γ' S) := by
  cases h with
  | set_det x mty e md h_find h_expr =>
    simp only [Cmd.subst, substExprOrNondet, ExprOrNondet.map]
    have h_find_subst := TContext.subst_find_some Γ S x (.forAll [] mty) h_find
    rw [LTy.subst_forAll_nil] at h_find_subst
    have h_expr_subst : LExpr.HasTypeA [] (LExpr.applySubst e S) (LMonoTy.subst S mty) := by
      have h0 := applySubst_typeCheck S (Δ := ([] : List LMonoTy)) h_expr; simpa using h0
    exact CmdHasType'.set_det _ x (LMonoTy.subst S mty) (LExpr.applySubst e S) md h_find_subst h_expr_subst
  | set_nondet x mty md h_find =>
    simp only [Cmd.subst, substExprOrNondet, ExprOrNondet.map]
    have h_find_subst := TContext.subst_find_some Γ S x (.forAll [] mty) h_find
    rw [LTy.subst_forAll_nil] at h_find_subst
    exact CmdHasType'.set_nondet _ x (LMonoTy.subst S mty) md h_find_subst
  | assert l e md h_expr =>
    simp only [Cmd.subst]
    have h_expr0 : LExpr.HasTypeA [] e .bool := h_expr
    have h_expr_subst : LExpr.HasTypeA [] (LExpr.applySubst e S) .bool := by
      have h0 := applySubst_typeCheck S (Δ := ([] : List LMonoTy)) h_expr0
      rw [LMonoTy.subst_bool] at h0; simpa using h0
    exact CmdHasType'.assert _ l (LExpr.applySubst e S) md h_expr_subst
  | assume l e md h_expr =>
    simp only [Cmd.subst]
    have h_expr0 : LExpr.HasTypeA [] e .bool := h_expr
    have h_expr_subst : LExpr.HasTypeA [] (LExpr.applySubst e S) .bool := by
      have h0 := applySubst_typeCheck S (Δ := ([] : List LMonoTy)) h_expr0
      rw [LMonoTy.subst_bool] at h0; simpa using h0
    exact CmdHasType'.assume _ l (LExpr.applySubst e S) md h_expr_subst
  | cover l e md h_expr =>
    simp only [Cmd.subst]
    have h_expr0 : LExpr.HasTypeA [] e .bool := h_expr
    have h_expr_subst : LExpr.HasTypeA [] (LExpr.applySubst e S) .bool := by
      have h0 := applySubst_typeCheck S (Δ := ([] : List LMonoTy)) h_expr0
      rw [LMonoTy.subst_bool] at h0; simpa using h0
    exact CmdHasType'.cover _ l (LExpr.applySubst e S) md h_expr_subst
  | init_det x xty e mty tys md h_find h_getvars h_len h_rac h_expr =>
    simp only [Cmd.subst, substExprOrNondet, ExprOrNondet.map]
    have h_ic' : xty.boundVars = [] ∧ (∀ v, v ∈ LMonoTy.freeVars xty.toMonoTypeUnsafe → v ∈ C.rigidTypeVars) := by
      simpa only [CmdInitClosed] using h_ic
    obtain ⟨h_bv, h_closed⟩ := h_ic'
    obtain ⟨mty0, h_xty⟩ : ∃ m, xty = LTy.forAll [] m := by
      cases xty with | forAll xs body => cases xs with
        | nil => exact ⟨body, rfl⟩
        | cons a as => simp [LTy.boundVars] at h_bv
    subst h_xty
    have h_closed0 : ∀ v, v ∈ LMonoTy.freeVars mty0 → v ∈ C.rigidTypeVars := by
      intro v hv; exact h_closed v (by simpa [LTy.toMonoTypeUnsafe] using hv)
    obtain ⟨h_disj, h_ren, h_inv⟩ := init_transport hS mty0 h_closed0
    have h_find_subst := TContext.subst_find_none Γ S x h_find
    have h_getvars_subst : x ∉ HasVarsPure.getVars (P := Expression) (LExpr.applySubst e S) := by
      rw [show HasVarsPure.getVars (P := Expression) (LExpr.applySubst e S)
          = LExpr.getVars (LExpr.applySubst e S) from rfl, applySubst_getVars_eq e S]
      exact h_getvars
    have h_len_subst : tys.length = (LTy.subst S (LTy.forAll [] mty0)).boundVars.length := by
      rw [LTy_subst_boundVars]; exact h_len
    have h_rac_S : RigidAnnotCompat Γ.aliases C.rigidTypeVars
        ((LTy.subst S (LTy.forAll [] mty0)).openFull tys) (LMonoTy.subst S mty) :=
      RigidAnnotCompat_openFull_mono_subst S Sinv h_rac hS.aliasesWF h_disj h_ren h_inv
    have h_expr_subst : instHasTypeA.exprTyped C (TContext.subst Γ S) (LExpr.applySubst e S)
        (instHasTypeA.embed (LMonoTy.subst S mty)) := by
      show LExpr.HasTypeA [] (LExpr.applySubst e S) (LMonoTy.subst S mty)
      have h_e0 : LExpr.HasTypeA [] e mty := h_expr
      have h0 := applySubst_typeCheck S (Δ := ([] : List LMonoTy)) h_e0; simpa using h0
    have h_rac_alias : RigidAnnotCompat (TContext.subst Γ S).aliases C.rigidTypeVars
        ((LTy.subst S (LTy.forAll [] mty0)).openFull tys) (LMonoTy.subst S mty) := by
      rw [TContext.subst_aliases]; exact h_rac_S
    have h_target := CmdHasType'.init_det (C := C) (TContext.subst Γ S) x (LTy.subst S (LTy.forAll [] mty0))
      (LExpr.applySubst e S) (LMonoTy.subst S mty) tys md
      h_find_subst h_getvars_subst h_len_subst h_rac_alias h_expr_subst
    rw [TContext_subst_insert_fresh Γ S x (LTy.forAll [] mty) h_find, LTy.subst_forAll_nil]
    exact h_target
  | init_nondet x xty mty tys md h_find h_len h_rac =>
    simp only [Cmd.subst, substExprOrNondet, ExprOrNondet.map]
    have h_ic' : xty.boundVars = [] ∧ (∀ v, v ∈ LMonoTy.freeVars xty.toMonoTypeUnsafe → v ∈ C.rigidTypeVars) := by
      simpa only [CmdInitClosed] using h_ic
    obtain ⟨h_bv, h_closed⟩ := h_ic'
    obtain ⟨mty0, h_xty⟩ : ∃ m, xty = LTy.forAll [] m := by
      cases xty with | forAll xs body => cases xs with
        | nil => exact ⟨body, rfl⟩
        | cons a as => simp [LTy.boundVars] at h_bv
    subst h_xty
    have h_closed0 : ∀ v, v ∈ LMonoTy.freeVars mty0 → v ∈ C.rigidTypeVars := by
      intro v hv; exact h_closed v (by simpa [LTy.toMonoTypeUnsafe] using hv)
    obtain ⟨h_disj, h_ren, h_inv⟩ := init_transport hS mty0 h_closed0
    have h_find_subst := TContext.subst_find_none Γ S x h_find
    have h_len_subst : tys.length = (LTy.subst S (LTy.forAll [] mty0)).boundVars.length := by
      rw [LTy_subst_boundVars]; exact h_len
    have h_rac_S : RigidAnnotCompat Γ.aliases C.rigidTypeVars
        ((LTy.subst S (LTy.forAll [] mty0)).openFull tys) (LMonoTy.subst S mty) :=
      RigidAnnotCompat_openFull_mono_subst S Sinv h_rac hS.aliasesWF h_disj h_ren h_inv
    have h_rac_alias : RigidAnnotCompat (TContext.subst Γ S).aliases C.rigidTypeVars
        ((LTy.subst S (LTy.forAll [] mty0)).openFull tys) (LMonoTy.subst S mty) := by
      rw [TContext.subst_aliases]; exact h_rac_S
    have h_target := CmdHasType'.init_nondet (τ := LMonoTy) (S := instHasTypeA) (C := C)
      (TContext.subst Γ S) x (LTy.subst S (LTy.forAll [] mty0))
      (LMonoTy.subst S mty) tys md h_find_subst h_len_subst h_rac_alias
    rw [TContext_subst_insert_fresh Γ S x (LTy.forAll [] mty) h_find, LTy.subst_forAll_nil]
    exact h_target

/-! ## CmdExt-level subst (cmd + call). -/

/-- The per-argument map applied by `Command.subst` on a `.call`. -/
def substCallArgFn (S : Subst) : CallArg Expression → CallArg Expression
  | .inArg e => .inArg (e.applySubst S)
  | .inoutArg id => .inoutArg id
  | .outArg id => .outArg id

/-- `Command.subst` on a `.call` maps `substCallArgFn` over the arguments. -/
theorem Command_subst_call (S : Subst) (pname : String)
    (args : List (CallArg Expression)) (md : MetaData Expression) :
    Core.Statement.Command.subst S (.call pname args md)
      = .call pname (args.map (substCallArgFn S)) md := by
  simp only [Command.subst]; congr 1

/-- `applySubst` fixes a bare unannotated `fvar` (no annotation to rewrite). -/
theorem fvar_none_applySubst (id : Expression.Ident) (S : Subst) :
    (LExpr.fvar () id none : Expression.Expr).applySubst S = LExpr.fvar () id none := by
  rw [LExpr.applySubst_eq_replaceUserProvidedType]
  simp [LExpr.replaceUserProvidedType]

/-- `substCallArgFn` leaves the LHS variables of a call unchanged. -/
theorem getLhs_map_substCallArgFn (args : List (CallArg Expression)) (S : Subst) :
    CallArg.getLhs (args.map (substCallArgFn S)) = CallArg.getLhs args := by
  induction args with
  | nil => rfl
  | cons a rest ih =>
    unfold CallArg.getLhs at ih ⊢
    cases a <;> simp only [List.map_cons, substCallArgFn, List.filterMap_cons, ih]

/-- `substCallArgFn` distributes over `getInputExprs`, applying `applySubst` to each input. -/
theorem getInputExprs_map_substCallArgFn (args : List (CallArg Expression)) (S : Subst) :
    CallArg.getInputExprs (args.map (substCallArgFn S))
      = (CallArg.getInputExprs args).map (LExpr.applySubst · S) := by
  induction args with
  | nil => rfl
  | cons a rest ih =>
    cases a with
    | inArg e =>
      rw [List.map_cons]
      simp only [substCallArgFn]
      rw [show CallArg.getInputExprs (CallArg.inArg (e.applySubst S) :: rest.map (substCallArgFn S))
          = e.applySubst S :: CallArg.getInputExprs (rest.map (substCallArgFn S)) from rfl,
          show CallArg.getInputExprs (CallArg.inArg e :: rest)
          = e :: CallArg.getInputExprs rest from rfl,
          List.map_cons, ih]
    | inoutArg id =>
      rw [List.map_cons]
      simp only [substCallArgFn]
      rw [show CallArg.getInputExprs (CallArg.inoutArg id :: rest.map (substCallArgFn S))
          = (LExpr.fvar () id none) :: CallArg.getInputExprs (rest.map (substCallArgFn S)) from rfl,
          show CallArg.getInputExprs (CallArg.inoutArg id :: rest)
          = (LExpr.fvar () id none) :: CallArg.getInputExprs rest from rfl,
          List.map_cons, ih, fvar_none_applySubst]
    | outArg id =>
      rw [List.map_cons]
      simp only [substCallArgFn]
      rw [show CallArg.getInputExprs (CallArg.outArg id :: rest.map (substCallArgFn S))
          = CallArg.getInputExprs (rest.map (substCallArgFn S)) from rfl,
          show CallArg.getInputExprs (CallArg.outArg id :: rest)
          = CallArg.getInputExprs rest from rfl, ih]

/-- `substCallArgFn` preserves the number of input expressions. -/
theorem getInputExprs_map_substCallArgFn_length (args : List (CallArg Expression)) (S : Subst) :
    (CallArg.getInputExprs (args.map (substCallArgFn S))).length
      = (CallArg.getInputExprs args).length := by
  rw [getInputExprs_map_substCallArgFn, List.length_map]

/-- Zipping a list with its own image under `f` is the diagonal `map (v, f v)`. -/
theorem zip_map_eq {α β} (xs : List α) (f : α → β) :
    xs.zip (xs.map f) = xs.map (fun v => (v, f v)) := by
  induction xs with
  | nil => rfl
  | cons h t ih => rw [List.map_cons, List.map_cons, List.zip_cons_cons, ih]

/-- General diagonal substitution: a single scope collecting, for each variable
    `v` in `allVars ⊇ freeVars formal`, the two-step image
    `subst S (subst tyArgSubst (ftvar v))`, reproduces the two-step substitution
    on `formal`. No closedness needed (`typeArgs := allVars`). -/
theorem subst_diag_mem (S tyArgSubst : Subst) (allVars : List TyIdentifier) (formal : LMonoTy)
    (h_sub : ∀ v, v ∈ formal.freeVars → v ∈ allVars) :
    LMonoTy.subst
      [allVars.map (fun v => (v, LMonoTy.subst S (LMonoTy.subst tyArgSubst (.ftvar v))))]
      formal
      = LMonoTy.subst S (LMonoTy.subst tyArgSubst formal) := by
  have h := subst_diag_eq allVars S tyArgSubst formal h_sub
  rw [← zip_map_eq]; exact h


/-- Transport of the annotated input-node obligation through `applySubst S`. The
    `fvar _ _ none` (inout) branch lifts a context lookup via `TContext.subst_find_some`;
    every other branch (`exprTyped = HasTypeA []`) lifts via `applySubst_typeCheck`. -/
theorem input_node_transport (E : Expression.Expr) (S : Subst) (Γ : TContext Unit) (mty0 : LMonoTy)
    (h : match E with
         | .fvar _ x none => Γ.types.find? x = some (LTy.forAll [] mty0)
         | e => LExpr.HasTypeA [] e mty0) :
    match E.applySubst S with
    | .fvar _ x none => (Γ.subst S).types.find? x = some (LTy.forAll [] (LMonoTy.subst S mty0))
    | e => LExpr.HasTypeA [] e (LMonoTy.subst S mty0) := by
  cases E with
  | fvar m x uty =>
    cases uty with
    | none =>
      simp only at h
      rw [LExpr.applySubst_eq_replaceUserProvidedType]
      simp only [LExpr.replaceUserProvidedType, Option.map_none]
      have h_find := TContext.subst_find_some Γ S x (.forAll [] mty0) h
      rw [LTy.subst_forAll_nil] at h_find
      exact h_find
    | some t =>
      simp only at h
      rw [LExpr.applySubst_eq_replaceUserProvidedType]
      simp only [LExpr.replaceUserProvidedType, Option.map_some]
      have h0 := applySubst_typeCheck S (Δ := ([] : List LMonoTy)) h
      rw [LExpr.applySubst_eq_replaceUserProvidedType] at h0
      simpa using h0
  | const _ _ | op _ _ _ | bvar _ _ | app _ _ _ | abs _ _ _ _
  | quant _ _ _ _ _ _ | ite _ _ _ _ | eq _ _ _ =>
    all_goals (
      simp only at h
      rw [LExpr.applySubst_eq_replaceUserProvidedType]
      simp only [LExpr.replaceUserProvidedType]
      have h0 := applySubst_typeCheck S (Δ := ([] : List LMonoTy)) h
      rw [LExpr.applySubst_eq_replaceUserProvidedType] at h0
      simpa [LExpr.replaceUserProvidedType] using h0)

/-- `CmdExtHasTypeA` is preserved under applying a rigid-respecting renaming `S` to the command
    and both contexts (given the command is init-closed). -/
theorem CmdExtHasTypeA_subst (C : LContext CoreLParams) (P : Program)
    (Γ Γ' : TContext Unit) (c : Command) (S Sinv : Subst)
    (h : CmdExtHasTypeA C P Γ c Γ')
    (hS : SubstReq C Γ S Sinv)
    (h_ic : CommandInitClosed C.rigidTypeVars c) :
    CmdExtHasTypeA C P (TContext.subst Γ S) (Core.Statement.Command.subst S c) (TContext.subst Γ' S) := by
  cases h with
  | cmd Γ' c0 h_c0 =>
    simp only [Command.subst]
    have h_ic0 : CmdInitClosed C.rigidTypeVars c0 := by simpa only [CommandInitClosed] using h_ic
    have h_sub := CmdHasTypeA_subst C Γ Γ' c0 S Sinv h_c0 hS h_ic0
    exact CmdExtHasType'.cmd (TContext.subst Γ S) (TContext.subst Γ' S) (Cmd.subst S c0) h_sub
  | call pname callArgs proc md σ h_find h_inarity h_outarity h_lhsex h_inp h_out h_inout =>
    rw [Command_subst_call]
    -- Union of free vars of all formal input/output types (used as the diagonal domain).
    obtain ⟨allVars, h_allVars⟩ :
        ∃ x : List TyIdentifier,
          x = (proc.header.inputs.values ++ proc.header.outputs.values).flatMap LMonoTy.freeVars :=
      ⟨_, rfl⟩
    -- The new type instantiation: diagonal over `allVars`, combining `S ∘ subst [σ]`.
    obtain ⟨σnew, h_σnew⟩ :
        ∃ x : List (TyIdentifier × LMonoTy),
          x = allVars.map (fun v => (v, LMonoTy.subst S (LMonoTy.subst [σ] (.ftvar v)))) :=
      ⟨_, rfl⟩
    -- Diagonal identity: on any formal whose free vars ⊆ allVars,
    -- subst [σnew] formal = subst S (subst [σ] formal).
    have h_diag : ∀ (formal : LMonoTy), (∀ v, v ∈ formal.freeVars → v ∈ allVars) →
        LMonoTy.subst [σnew] formal = LMonoTy.subst S (LMonoTy.subst [σ] formal) := by
      intro formal h_sub
      rw [h_σnew]; exact subst_diag_mem S [σ] allVars formal h_sub
    apply CmdExtHasType'.call (Γ := Γ.subst S) (σ := σnew) (proc := proc) (md := md)
    · exact h_find
    · rw [getInputExprs_map_substCallArgFn_length]; exact h_inarity
    · rw [getLhs_map_substCallArgFn]; exact h_outarity
    · rw [getLhs_map_substCallArgFn]
      intro v hv
      obtain ⟨ty, h_opt⟩ := Option.isSome_iff_exists.mp (h_lhsex v hv)
      exact Option.isSome_iff_exists.mpr
        ⟨_, TContext.subst_find_some Γ S v ty h_opt⟩
    · -- input obligation
      rw [getInputExprs_map_substCallArgFn]
      intro i hi hj
      rw [List.length_map] at hi
      obtain ⟨mty0, h_ae, h_node⟩ := h_inp i hi hj
      refine ⟨LMonoTy.subst S mty0, ?_, ?_⟩
      · -- AliasEquiv transported + diagonal.
        rw [TContext.subst_aliases]
        have h_ae_S := AliasEquiv_subst Γ.aliases mty0
          (LMonoTy.subst [σ] (proc.header.inputs.values[i])) S h_ae hS.aliasesWF
        have h_formal_sub : ∀ v, v ∈ (proc.header.inputs.values[i]).freeVars → v ∈ allVars := by
          intro v hv
          rw [h_allVars, List.mem_flatMap]
          exact ⟨proc.header.inputs.values[i], by
            rw [List.mem_append]; left; exact List.getElem_mem hj, hv⟩
        rw [h_diag _ h_formal_sub]
        exact h_ae_S
      · -- Node obligation transported.
        rw [List.getElem_map]
        exact input_node_transport ((CallArg.getInputExprs callArgs)[i]) S Γ mty0 h_node
    · -- output obligation
      rw [getLhs_map_substCallArgFn]
      intro i hi hj
      obtain ⟨mty0, h_ae, h_find_i⟩ := h_out i hi hj
      refine ⟨LMonoTy.subst S mty0, ?_, ?_⟩
      · rw [TContext.subst_aliases]
        have h_ae_S := AliasEquiv_subst Γ.aliases mty0
          (LMonoTy.subst [σ] (proc.header.outputs.values[i])) S h_ae hS.aliasesWF
        have h_formal_sub : ∀ v, v ∈ (proc.header.outputs.values[i]).freeVars → v ∈ allVars := by
          intro v hv
          rw [h_allVars, List.mem_flatMap]
          exact ⟨proc.header.outputs.values[i], by
            rw [List.mem_append]; right; exact List.getElem_mem hj, hv⟩
        rw [h_diag _ h_formal_sub]
        exact h_ae_S
      · have h_find_subst := TContext.subst_find_some Γ S
          ((CallArg.getLhs callArgs)[i]) (.forAll [] mty0) h_find_i
        rw [LTy.subst_forAll_nil] at h_find_subst
        exact h_find_subst
    · -- inout obligation
      intro i hi h_contains
      obtain ⟨m, ty, h_get⟩ := h_inout i hi h_contains
      rw [getInputExprs_map_substCallArgFn]
      refine ⟨m, ty.map (LMonoTy.subst S), ?_⟩
      rw [List.getElem?_map, h_get]
      simp only [Option.map_some]
      rw [LExpr.applySubst_eq_replaceUserProvidedType]
      simp only [LExpr.replaceUserProvidedType]



/-- `CmdHasType'` leaves the alias list unchanged. -/
theorem CmdHasType'_aliases {τ : Type} [ES : ExprTypingSpec τ]
    {C : LContext CoreLParams} {Γ Γ' : TContext Unit} {c : Cmd Expression}
    (h : CmdHasType' (τ := τ) C Γ c Γ') : Γ'.aliases = Γ.aliases := by
  cases h <;> rfl

/-- `CmdExtHasType'` leaves the alias list unchanged. -/
theorem CmdExtHasType'_aliases {τ : Type} [ES : ExprTypingSpec τ]
    {C : LContext CoreLParams} {P : Program} {Γ Γ' : TContext Unit} {c : Command}
    (h : CmdExtHasType' (τ := τ) C P Γ c Γ') : Γ'.aliases = Γ.aliases := by
  cases h with
  | cmd Γ' c hc => exact CmdHasType'_aliases hc
  | call => rfl

/-- A statement-list derivation preserves the alias list from input to output.
    Only the `cmd` constructor mutates `Γ` (via `CmdExtHasType'`, which preserves
    aliases); `block`/`ite`/`loop`/`exit`/`funcDecl`/`typeDecl` all leave `Γ` fixed,
    and `cons` chains the two ends. Used to relate the checker's body output context
    to `procBodyContext Env'.context proc'` in `bodyTyped`. -/
theorem StmtsHasType'_aliases {τ : Type} [ES : ExprTypingSpec τ]
    {C C' : LContext CoreLParams} {P : Program} {Γ Γ' : TContext Unit} {L : List String}
    {ss : List Statement}
    (h : StmtsHasType' (τ := τ) P C Γ L ss C' Γ') : Γ'.aliases = Γ.aliases := by
  refine StmtsHasType'.rec
    (motive_1 := fun _ Γa _ _ _ Γa' _ => Γa'.aliases = Γa.aliases)
    (motive_2 := fun _ Γa _ _ _ Γa' _ => Γa'.aliases = Γa.aliases)
    ?cmd ?block ?ite_det ?ite_nondet ?loop ?exit ?funcDecl ?typeDecl ?nil ?cons h
  case cmd => intro Ca Γa Γa' La c h_cmd; exact CmdExtHasType'_aliases h_cmd
  case block => intros; rfl
  case ite_det => intros; rfl
  case ite_nondet => intros; rfl
  case loop => intros; rfl
  case exit => intros; rfl
  case funcDecl => intros; rfl
  case typeDecl => intros; rfl
  case nil => intros; rfl
  case cons => intro Ca Cb Cc Γa Γb Γc La s ss _ _ ih_s ih_ss; rw [ih_ss, ih_s]

/-- A single statement's derivation preserves `SubstReq` from input to output.
    `ren`/`rig_notin_range`/`inv_on_rigid` depend only on `S`/`C.rigidTypeVars`
    (preserved by funcDecl/typeDecl); `aliasesWF` via `CmdExtHasType'_aliases`. -/
theorem StmtHasType'_SubstReq {P : Program}
    {C C' : LContext CoreLParams} {Γ Γ' : TContext Unit} {L : List String}
    {s : Statement} (S Sinv : Subst)
    (h : StmtHasTypeA P C Γ L s C' Γ') (hS : SubstReq C Γ S Sinv) :
    SubstReq C' Γ' S Sinv := by
  cases h with
  | cmd _ _ _ _ _ h_cmd =>
    exact { ren := hS.ren, rig_notin_range := hS.rig_notin_range, inv_on_rigid := hS.inv_on_rigid,
            aliasesWF := by rw [CmdExtHasType'_aliases h_cmd]; exact hS.aliasesWF }
  | block => exact hS
  | ite_det => exact hS
  | ite_nondet => exact hS
  | loop => exact hS
  | exit => exact hS
  | funcDecl _ _ _ decl func md h_nrec h_func =>
    refine { ren := hS.ren, rig_notin_range := ?_, inv_on_rigid := ?_, aliasesWF := hS.aliasesWF }
    · intro v hv; rw [addFactoryFunction_rigidTypeVars] at hv; exact hS.rig_notin_range v hv
    · intro v hv; rw [addFactoryFunction_rigidTypeVars] at hv; exact hS.inv_on_rigid v hv
  | typeDecl _ C0' _ _ tc md h_add =>
    refine { ren := hS.ren, rig_notin_range := ?_, inv_on_rigid := ?_, aliasesWF := hS.aliasesWF }
    · intro v hv
      apply hS.rig_notin_range v
      simp only [LContext.addKnownTypeWithError, Bind.bind, Except.bind] at h_add
      split at h_add
      · simp only [reduceCtorEq] at h_add
      · injection h_add with h_add_eq; rw [← h_add_eq] at hv; exact hv
    · intro v hv
      apply hS.inv_on_rigid v
      simp only [LContext.addKnownTypeWithError, Bind.bind, Except.bind] at h_add
      split at h_add
      · simp only [reduceCtorEq] at h_add
      · injection h_add with h_add_eq; rw [← h_add_eq] at hv; exact hv


/-! ## Declarative rigidTypeVars preservation (for threading InitClosed in `cons`). -/

theorem StmtHasType'_rigid_eq {P : Program}
    {C C' : LContext CoreLParams} {Γ Γ' : TContext Unit} {L : List String}
    {s : Statement} (h : StmtHasTypeA P C Γ L s C' Γ') :
    C'.rigidTypeVars = C.rigidTypeVars := by
  cases h with
  | cmd => rfl
  | block => rfl
  | ite_det => rfl
  | ite_nondet => rfl
  | loop => rfl
  | exit => rfl
  | funcDecl _ _ _ decl func md h_nrec h_func => exact addFactoryFunction_rigidTypeVars _ _
  | typeDecl _ C0' _ _ tc md h_add =>
    simp only [LContext.addKnownTypeWithError, Bind.bind, Except.bind] at h_add
    split at h_add
    · simp only [reduceCtorEq] at h_add
    · injection h_add with h_add_eq; rw [← h_add_eq]

/-! ## Unfolding lemmas for InitClosed (well-founded recursion). -/

/-- `StmtInitClosed` on a `block` unfolds to init-closedness of the body. -/
theorem StmtInitClosed_block (rig) (l b md) :
    StmtInitClosed rig (.block l b md) = ∀ s ∈ b, StmtInitClosed rig s := by
  simp only [StmtInitClosed]

/-- `StmtInitClosed` on an `ite` unfolds to init-closedness of both branches. -/
theorem StmtInitClosed_ite (rig) (cnd t e md) :
    StmtInitClosed rig (.ite cnd t e md)
      = ((∀ s ∈ t, StmtInitClosed rig s) ∧ (∀ s ∈ e, StmtInitClosed rig s)) := by
  simp only [StmtInitClosed]

/-- `StmtInitClosed` on a `loop` unfolds to init-closedness of the body. -/
theorem StmtInitClosed_loop (rig) (g m i b md) :
    StmtInitClosed rig (.loop g m i b md) = ∀ s ∈ b, StmtInitClosed rig s := by
  simp only [StmtInitClosed]

/-- `StmtInitClosed` on a `cmd` unfolds to `CommandInitClosed`. -/
theorem StmtInitClosed_cmd (rig) (c) :
    StmtInitClosed rig (.cmd c) = CommandInitClosed rig c := by simp only [StmtInitClosed]


/-! ## Statement-list substitution (both-sides subst, with InitClosed). -/

theorem StmtsHasTypeA_subst_gen (P : Program) (C : LContext CoreLParams)
    (Γ : TContext Unit) (L : List String) (ss : List Statement)
    (C' : LContext CoreLParams) (Γ' : TContext Unit) (S Sinv : Lambda.Subst)
    (h : StmtsHasTypeA P C Γ L ss C' Γ')
    (hS : SubstReq C Γ S Sinv)
    (h_ic : StmtsInitClosed C.rigidTypeVars ss) :
    StmtsHasTypeA P C (TContext.subst Γ S) L (ss.map (Core.Statement.Statement.subst S)) C' (TContext.subst Γ' S) := by
  refine StmtsHasType'.rec
    (motive_1 := fun Ca Γa La s Ca' Γa' _ =>
      SubstReq Ca Γa S Sinv → StmtInitClosed Ca.rigidTypeVars s →
      StmtHasTypeA P Ca (TContext.subst Γa S) La (Statement.subst S s) Ca' (TContext.subst Γa' S))
    (motive_2 := fun Ca Γa La ss Ca' Γa' _ =>
      SubstReq Ca Γa S Sinv → StmtsInitClosed Ca.rigidTypeVars ss →
      StmtsHasTypeA P Ca (TContext.subst Γa S) La (ss.map (Statement.subst S)) Ca' (TContext.subst Γa' S))
    ?cmd ?block ?ite_det ?ite_nondet ?loop ?exit ?funcDecl ?typeDecl ?nil ?cons h hS h_ic
  case cmd =>
    intro Ca Γa Γa' La c h_cmd hS' h_ic'
    rw [StmtInitClosed_cmd] at h_ic'
    have h_sub := CmdExtHasTypeA_subst Ca P Γa Γa' c S Sinv h_cmd hS' h_ic'
    exact StmtHasType'.cmd Ca (TContext.subst Γa S) (TContext.subst Γa' S) La
      (Command.subst S c) h_sub
  case block =>
    intro Ca Γa C_body Γ_body La label body md h_notin _ ih_body hS' h_ic'
    simp only [Statement.subst, Statement.subst_go_nil]
    rw [StmtInitClosed_block] at h_ic'
    exact StmtHasType'.block Ca (TContext.subst Γa S) C_body (TContext.subst Γ_body S)
      La label (body.map (Statement.subst S)) md h_notin (ih_body hS' h_ic')
  case ite_det =>
    intro Ca Γa C_t Γ_t C_e Γ_e La cond thenb elseb md h_cond _ _ ih_t ih_e hS' h_ic'
    simp only [Statement.subst, Statement.subst_go_nil]
    rw [StmtInitClosed_ite] at h_ic'
    have h_cond_subst : LExpr.HasTypeA [] (LExpr.applySubst cond S) .bool := by
      have h_c0 : LExpr.HasTypeA [] cond .bool := h_cond
      have h0 := applySubst_typeCheck S (Δ := ([] : List LMonoTy)) h_c0
      rw [LMonoTy.subst_bool] at h0; simpa using h0
    exact StmtHasType'.ite_det Ca (TContext.subst Γa S) C_t (TContext.subst Γ_t S)
      C_e (TContext.subst Γ_e S) La (LExpr.applySubst cond S)
      (thenb.map (Statement.subst S)) (elseb.map (Statement.subst S)) md
      h_cond_subst (ih_t hS' h_ic'.1) (ih_e hS' h_ic'.2)
  case ite_nondet =>
    intro Ca Γa C_t Γ_t C_e Γ_e La thenb elseb md _ _ ih_t ih_e hS' h_ic'
    simp only [Statement.subst, Statement.subst_go_nil]
    rw [StmtInitClosed_ite] at h_ic'
    exact StmtHasType'.ite_nondet Ca (TContext.subst Γa S) C_t (TContext.subst Γ_t S)
      C_e (TContext.subst Γ_e S) La (thenb.map (Statement.subst S))
      (elseb.map (Statement.subst S)) md (ih_t hS' h_ic'.1) (ih_e hS' h_ic'.2)
  case loop =>
    intro Ca Γa C_body Γ_body La guard measure invariants body md h_g h_m h_i _ ih_body hS' h_ic'
    simp only [Statement.subst, Statement.subst_go_nil, substOptionExpr]
    rw [StmtInitClosed_loop] at h_ic'
    refine StmtHasType'.loop Ca (TContext.subst Γa S) C_body (TContext.subst Γ_body S)
      La _ _ _ (body.map (Statement.subst S)) md ?_ ?_ ?_ (ih_body hS' h_ic')
    · intro g h_gd
      cases guard with
      | nondet => simp only [ExprOrNondet.map, reduceCtorEq] at h_gd
      | det g0 =>
        simp only [ExprOrNondet.map, ExprOrNondet.det.injEq] at h_gd
        subst h_gd
        have h_g0 : LExpr.HasTypeA [] g0 .bool := h_g g0 rfl
        have h0 := applySubst_typeCheck S (Δ := ([] : List LMonoTy)) h_g0
        rw [LMonoTy.subst_bool] at h0; simpa using h0
    · intro m h_md
      cases measure with
      | none => simp only [reduceCtorEq] at h_md
      | some m0 =>
        simp only [Option.some.injEq] at h_md
        subst h_md
        have h_m0 : LExpr.HasTypeA [] m0 .int := h_m m0 rfl
        have h0 := applySubst_typeCheck S (Δ := ([] : List LMonoTy)) h_m0
        rw [LMonoTy.subst_int] at h0; simpa using h0
    · intro p h_pmem
      simp only [List.mem_map] at h_pmem
      obtain ⟨p0, h_p0_mem, h_p0_eq⟩ := h_pmem
      subst h_p0_eq
      have h_p0 : LExpr.HasTypeA [] p0.2 .bool := h_i p0 h_p0_mem
      have h0 := applySubst_typeCheck S (Δ := ([] : List LMonoTy)) h_p0
      rw [LMonoTy.subst_bool] at h0; simpa using h0
  case exit =>
    intro Ca Γa La label md h_mem hS' h_ic'
    exact StmtHasType'.exit Ca (TContext.subst Γa S) La label md h_mem
  case funcDecl =>
    intro Ca Γa La decl func md h_nrec h_func hS' h_ic'
    simp only [Statement.subst]
    have h_func' : FuncHasType' LMonoTy Ca (TContext.subst Γa S) func := {
      inputsNodup := h_func.inputsNodup
      typeArgsNodup := h_func.typeArgsNodup
      noUndeclaredVars := h_func.noUndeclaredVars
      bodyTyped := h_func.bodyTyped
      measureTyped := h_func.measureTyped }
    exact StmtHasType'.funcDecl Ca (TContext.subst Γa S) La _ func md h_nrec h_func'
  case typeDecl =>
    intro Ca Ca' Γa La tc md h_add hS' h_ic'
    have h_eq : Statement.subst S (Statement.typeDecl tc md) = Statement.typeDecl tc md := by
      simp only [Statement.subst]
    rw [h_eq]
    exact StmtHasType'.typeDecl Ca Ca' (TContext.subst Γa S) La tc md h_add
  case nil =>
    intro Ca Γa La hS' h_ic'
    exact StmtsHasType'.nil Ca (TContext.subst Γa S) La
  case cons =>
    intro Ca Cb Cc Γa Γb Γc La s ss h_s h_ss ih_s ih_ss hS' h_ic'
    have h_ic_head : StmtInitClosed Ca.rigidTypeVars s := h_ic' s List.mem_cons_self
    have h_ic_tail0 : StmtsInitClosed Ca.rigidTypeVars ss :=
      fun s' hs' => h_ic' s' (List.mem_cons_of_mem s hs')
    have hSb : SubstReq Cb Γb S Sinv := StmtHasType'_SubstReq S Sinv h_s hS'
    have h_rig_eq : Cb.rigidTypeVars = Ca.rigidTypeVars := StmtHasType'_rigid_eq h_s
    have h_ic_tail : StmtsInitClosed Cb.rigidTypeVars ss := by rw [h_rig_eq]; exact h_ic_tail0
    exact StmtsHasType'.cons Ca Cb Cc (TContext.subst Γa S) (TContext.subst Γb S)
      (TContext.subst Γc S) La (Statement.subst S s) (ss.map (Statement.subst S))
      (ih_s hS' h_ic_head) (ih_ss hSb h_ic_tail)


/-! ## Body-context agreement helpers: the checker's body context `find?`-agrees with
`procBodyContext`. -/

/-- Substitution commutes with `Maps.pop` (both act structurally on the scope list). -/
theorem types_subst_pop (ts : Maps CoreIdent LTy) (S : Subst) :
    Maps.pop (TContext.types.subst ts S) = TContext.types.subst (Maps.pop ts) S := by
  cases ts with
  | nil => rfl
  | cons t rest => simp only [TContext.types.subst, Maps.pop]

/-- For a successful `Statement.typeCheck`, the output env's popped context types equal
    `subst S' (pop input.types)` (S' = output subst). -/
theorem statement_typeCheck_popContext_types
    (C : LContext CoreLParams) (Env : TEnv Unit)
    (P : Program) (op : Option Procedure) (ss ss' : List Statement) (Env' : TEnv Unit)
    (h : Statement.typeCheck C Env P op ss = .ok (ss', Env'))
    (h_wf : TEnvWF (T := CoreLParams) Env)
    (h_fwf : FactoryWF C.functions)
    (h_ne : Env.context.types ≠ [])
    (h_mono : ContextMono Env.context)
    (h_rigid_inv : ∀ v, v ∈ C.rigidTypeVars →
      LMonoTy.subst Env.stateSubstInfo.subst (.ftvar v) = .ftvar v)
    (h_closed : CalledProcsClosed P) :
    Env'.popContext.context.types
      = TContext.types.subst (Maps.pop Env.context.types) Env'.stateSubstInfo.subst := by
  unfold Statement.typeCheck Statement.typeCheckAux at h
  cases h_go : Statement.typeCheckAux.go P op C Env ss [] [] with
  | error e => rw [h_go] at h; simp only [bind, Except.bind] at h; cases h
  | ok v_aux =>
    obtain ⟨ss_aux, Env_aux, C_aux⟩ := v_aux
    rw [h_go] at h
    simp only [bind, Except.bind, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨h_ss, h_env⟩ := h
    have h_pres := typeCheckAux_go_preserves C Env P op ss [] [] ss_aux Env_aux C_aux
      h_go h_wf h_fwf h_ne h_mono h_rigid_inv h_closed
    have h_tp := h_pres.types_pop
    subst h_env
    simp only [TEnv.context] at h_tp
    simp only [TEnv.popContext, TEnv.updateContext, TEnv.context, TContext.subst]
    rw [types_subst_pop, h_tp]

/-- `userSubst` (domain ⊆ `freshtvs`) fixes any monotype all of whose free vars are gen-below
    a bound `g`, given every element of `freshtvs` is gen-named at index `≥ g`. Used to leave the
    ambient tail untouched (vacuous for a closed ambient, and more generally for gen-below ones). -/
theorem userSubst_fixes_of_ambient_fresh
    (freshtvs ids : List TyIdentifier) (mty : LMonoTy) (g : Nat)
    (h_len : freshtvs.length = ids.length)
    (h_dom_gen : ∀ f ∈ freshtvs, ∃ k, k ≥ g ∧ f = TState.tyPrefix ++ toString k)
    (h_mty_below : ∀ v ∈ LMonoTy.freeVars mty, ∀ n, n ≥ g → v ≠ TState.tyPrefix ++ toString n) :
    LMonoTy.subst [freshtvs.zip (ids.map LMonoTy.ftvar)] mty = mty := by
  apply LMonoTy.subst_eq_self_of_fixes
  intro v hv
  have h_v_notin : v ∉ freshtvs := by
    intro hmem
    obtain ⟨k, hk_ge, hk_eq⟩ := h_dom_gen v hmem
    exact h_mty_below v hv k hk_ge hk_eq
  rw [LMonoTy.subst_unfold]
  simp only [Maps.find?]
  have h_keys : Map.keys (freshtvs.zip (ids.map LMonoTy.ftvar)) = freshtvs :=
    keys_zip_map_ftvar freshtvs ids h_len
  have h_none : Map.find? (freshtvs.zip (ids.map LMonoTy.ftvar)) v = none := by
    apply Map.find?_none_of_not_mem_keys'
    rw [h_keys]; exact h_v_notin
  rw [h_none]

/-- Any substitution fixes a closed monomorphic `LTy` (`boundVars = []`, `freeVars = []`).
    Ambient bindings satisfy both, so any substitution leaves the ambient tail untouched. -/
theorem LTy.subst_eq_self_of_mono_closed (S : Subst) (ty : LTy)
    (h_mono : LTy.boundVars ty = []) (h_closed : LTy.freeVars ty = []) :
    LTy.subst S ty = ty := by
  apply LTy.subst_eq_self_of_fixes_mono S ty h_mono
  intro v hv; rw [h_closed] at hv; exact absurd hv (List.not_mem_nil)

/-- `addInNewestContext` preserves the popped tail (only touches the newest scope). -/
theorem addInNewestContext_pop_types (Env : Core.Expression.TyEnv) (m : Map CoreIdent LTy) :
    Maps.pop (Env.addInNewestContext (T := CoreLParams) m).context.types
      = Maps.pop Env.context.types := by
  show Maps.pop (Maps.addInNewest Env.context.types m) = _
  simp only [Maps.addInNewest, Maps.newest, Maps.pop, Maps.push]

/-- `setupInputEnv` pushes exactly one scope: `pop (output types) = Env.context.types`. -/
theorem setupInputEnv_pop_context_types
    (C : Core.Expression.TyContext) (Env : Core.Expression.TyEnv)
    (proc : Procedure) (fr : Strata.FileRange)
    (res : @Lambda.LMonoTySignature Unit × Core.Expression.TyEnv × Lambda.Subst)
    (h : Core.Procedure.setupInputEnv C Env proc fr = .ok res) :
    Maps.pop res.2.1.context.types = Env.context.types := by
  simp only [Core.Procedure.setupInputEnv, Bind.bind, Except.bind, Except.mapError, pure,
    Except.pure] at h
  cases h_inst : Lambda.LMonoTySignature.instantiateWithSubst C Env.pushEmptyContext
      proc.header.typeArgs proc.header.inputs with
  | error e => rw [h_inst] at h; simp only [reduceCtorEq] at h
  | ok v =>
    obtain ⟨inp_mty_sig, Env₁, tyArgSubst⟩ := v
    rw [h_inst] at h
    simp only [Except.ok.injEq] at h
    subst h
    have h_ctx : Env₁.context = Env.pushEmptyContext.context :=
      instantiateWithSubst_preserves_context C Env.pushEmptyContext proc.header.typeArgs
        proc.header.inputs (inp_mty_sig, Env₁, tyArgSubst) h_inst
    show Maps.pop (Env₁.addInNewestContext
      (Lambda.LMonoTySignature.toTrivialLTy inp_mty_sig)).context.types = _
    rw [show (Env₁.addInNewestContext
        (Lambda.LMonoTySignature.toTrivialLTy inp_mty_sig)).context.types
        = Maps.addInNewest Env₁.context.types
          (Lambda.LMonoTySignature.toTrivialLTy inp_mty_sig) from rfl, h_ctx]
    simp only [TEnv.pushEmptyContext, TEnv.updateContext, TEnv.context, Maps.addInNewest,
      Maps.newest, Maps.pop, Maps.push]

/-- The checker's body-input env has exactly one scope over the ambient:
    `pop envForBody.context.types = Env.context.types`. -/
theorem envForBody_pop_context_types
    (C : Core.Expression.TyContext) (Env : Core.Expression.TyEnv) (proc : Procedure)
    (fr : Strata.FileRange)
    (v_setup : @Lambda.LMonoTySignature Unit × Core.Expression.TyEnv × Lambda.Subst)
    (v_pre : Array Expression.Expr × Core.Expression.TyEnv)
    (v_out : Lambda.LMonoTys × Core.Expression.TyEnv)
    (v_post : Array Expression.Expr × Core.Expression.TyEnv) (v_unify : SubstInfo)
    (h_setup : Core.Procedure.setupInputEnv C Env proc fr = .ok v_setup)
    (h_pre : Core.Procedure.typeCheckConditions C v_setup.2.1 proc.spec.preconditions
      proc.header.name = .ok v_pre)
    (h_ra : Lambda.LMonoTys.resolveAliases
      (proc.header.outputs.values.map (Lambda.LMonoTy.subst v_setup.2.2)) v_pre.2 = .ok v_out)
    (h_post : Core.Procedure.typeCheckConditions C
      ((v_out.snd.addInNewestContext (T := CoreLParams)
          (Lambda.LMonoTySignature.toTrivialLTy ((proc.header.outputs.keys).zip v_out.fst))).addInNewestContext
        ((v_setup.1.filter (fun x => (ListMap.keys proc.header.outputs).contains x.fst)).map
          (fun x => (CoreIdent.mkOld x.fst.name, LTy.forAll [] x.snd))))
      proc.spec.postconditions proc.header.name = .ok v_post)
    (h_ta : proc.checkTypeArgsWF fr = .ok ())
    (h_wf : TEnvWF (T := CoreLParams) Env)
    (h_fwf : FactoryWF C.functions)
    (h_resolved : TContext.AliasesResolved Env.context) :
    Maps.pop (v_post.2.updateSubst v_unify).context.types = Env.context.types := by
  have h_us : (v_post.2.updateSubst v_unify).context = v_post.2.context := by
    simp only [TEnv.updateSubst, TEnv.context]
  rw [h_us]
  have h_setup_wf : TEnvWF (T := CoreLParams) v_setup.2.1 :=
    setupInputEnv_TEnvWF C Env proc fr v_setup h_setup h_wf
  have h_setup_ne : v_setup.2.1.context.types ≠ [] :=
    setupInputEnv_types_ne C Env proc fr v_setup h_setup
  have h_pre_ctx : v_pre.2.context = v_setup.2.1.context :=
    typeCheckConditions_context C v_setup.2.1 proc.spec.preconditions proc.header.name v_pre
      h_pre h_setup_wf h_setup_ne h_fwf
  have h_out_env : v_out.2 = v_pre.2 :=
    LMonoTys_resolveAliases_env_local _ v_pre.2 v_out.1 v_out.2 h_ra
  have h_penv := postEnv_wf C Env proc fr v_setup v_pre v_out h_ta h_setup h_pre h_ra h_wf h_fwf
    h_resolved
  let E4 := (v_out.snd.addInNewestContext (T := CoreLParams)
      (Lambda.LMonoTySignature.toTrivialLTy ((proc.header.outputs.keys).zip v_out.fst))).addInNewestContext
    ((v_setup.1.filter (fun x => (ListMap.keys proc.header.outputs).contains x.fst)).map
      (fun x => (CoreIdent.mkOld x.fst.name, LTy.forAll [] x.snd)))
  have h_post_ctx : v_post.2.context = E4.context :=
    typeCheckConditions_context C E4 proc.spec.postconditions proc.header.name v_post
      h_post h_penv.1 h_penv.2.1 h_fwf
  rw [h_post_ctx]
  show Maps.pop E4.context.types = _
  rw [addInNewestContext_pop_types, addInNewestContext_pop_types, h_out_env, h_pre_ctx]
  exact setupInputEnv_pop_context_types C Env proc fr v_setup h_setup

/-- Maps-level: `newest` of an `addInNewest` appends the added map to the old newest scope. -/
theorem addInNewestContext_newest_types (Env : Core.Expression.TyEnv) (m : Map CoreIdent LTy) :
    Maps.newest (Env.addInNewestContext (T := CoreLParams) m).context.types
      = Maps.newest Env.context.types ++ m := by
  show Maps.newest (Maps.addInNewest Env.context.types m) = _
  simp only [Maps.addInNewest, Maps.newest, Maps.pop, Maps.push]

/-- `setupInputEnv`'s newest scope is exactly the instantiated inputs (`toTrivialLTy inp_mty_sig`). -/
theorem setupInputEnv_newest_context_types
    (C : Core.Expression.TyContext) (Env : Core.Expression.TyEnv)
    (proc : Procedure) (fr : Strata.FileRange)
    (res : @Lambda.LMonoTySignature Unit × Core.Expression.TyEnv × Lambda.Subst)
    (h : Core.Procedure.setupInputEnv C Env proc fr = .ok res) :
    Maps.newest res.2.1.context.types = Lambda.LMonoTySignature.toTrivialLTy res.1 := by
  simp only [Core.Procedure.setupInputEnv, Bind.bind, Except.bind, Except.mapError, pure,
    Except.pure] at h
  cases h_inst : Lambda.LMonoTySignature.instantiateWithSubst C Env.pushEmptyContext
      proc.header.typeArgs proc.header.inputs with
  | error e => rw [h_inst] at h; simp only [reduceCtorEq] at h
  | ok v =>
    obtain ⟨inp_mty_sig, Env₁, tyArgSubst⟩ := v
    rw [h_inst] at h
    simp only [Except.ok.injEq] at h
    subst h
    have h_ctx : Env₁.context = Env.pushEmptyContext.context :=
      instantiateWithSubst_preserves_context C Env.pushEmptyContext proc.header.typeArgs
        proc.header.inputs (inp_mty_sig, Env₁, tyArgSubst) h_inst
    show Maps.newest (Env₁.addInNewestContext
      (Lambda.LMonoTySignature.toTrivialLTy inp_mty_sig)).context.types = _
    rw [addInNewestContext_newest_types Env₁ (Lambda.LMonoTySignature.toTrivialLTy inp_mty_sig),
      h_ctx]
    simp only [TEnv.pushEmptyContext, TEnv.updateContext, TEnv.context, Maps.newest, Maps.push]
    rfl

/-- The checker's body-input env's newest scope is exactly the accumulated
    inputs ++ outputs ++ old-inout bindings. Newest-analogue of `envForBody_pop_context_types`. -/
theorem envForBody_newest_context_types
    (C : Core.Expression.TyContext) (Env : Core.Expression.TyEnv) (proc : Procedure)
    (fr : Strata.FileRange)
    (v_setup : @Lambda.LMonoTySignature Unit × Core.Expression.TyEnv × Lambda.Subst)
    (v_pre : Array Expression.Expr × Core.Expression.TyEnv)
    (v_out : Lambda.LMonoTys × Core.Expression.TyEnv)
    (v_post : Array Expression.Expr × Core.Expression.TyEnv) (v_unify : SubstInfo)
    (h_setup : Core.Procedure.setupInputEnv C Env proc fr = .ok v_setup)
    (h_pre : Core.Procedure.typeCheckConditions C v_setup.2.1 proc.spec.preconditions
      proc.header.name = .ok v_pre)
    (h_ra : Lambda.LMonoTys.resolveAliases
      (proc.header.outputs.values.map (Lambda.LMonoTy.subst v_setup.2.2)) v_pre.2 = .ok v_out)
    (h_post : Core.Procedure.typeCheckConditions C
      ((v_out.snd.addInNewestContext (T := CoreLParams)
          (Lambda.LMonoTySignature.toTrivialLTy ((proc.header.outputs.keys).zip v_out.fst))).addInNewestContext
        ((v_setup.1.filter (fun x => (ListMap.keys proc.header.outputs).contains x.fst)).map
          (fun x => (CoreIdent.mkOld x.fst.name, LTy.forAll [] x.snd))))
      proc.spec.postconditions proc.header.name = .ok v_post)
    (h_ta : proc.checkTypeArgsWF fr = .ok ())
    (h_wf : TEnvWF (T := CoreLParams) Env)
    (h_fwf : FactoryWF C.functions)
    (h_resolved : TContext.AliasesResolved Env.context) :
    Maps.newest (v_post.2.updateSubst v_unify).context.types
      = List.append
          (List.append
            (Lambda.LMonoTySignature.toTrivialLTy v_setup.1 : List (CoreIdent × LTy))
            (Lambda.LMonoTySignature.toTrivialLTy ((proc.header.outputs.keys).zip v_out.fst)))
          ((v_setup.1.filter (fun x => (ListMap.keys proc.header.outputs).contains x.fst)).map
            (fun x => (CoreIdent.mkOld x.fst.name, LTy.forAll [] x.snd))) := by
  have h_us : (v_post.2.updateSubst v_unify).context = v_post.2.context := by
    simp only [TEnv.updateSubst, TEnv.context]
  rw [h_us]
  have h_setup_wf : TEnvWF (T := CoreLParams) v_setup.2.1 :=
    setupInputEnv_TEnvWF C Env proc fr v_setup h_setup h_wf
  have h_setup_ne : v_setup.2.1.context.types ≠ [] :=
    setupInputEnv_types_ne C Env proc fr v_setup h_setup
  have h_pre_ctx : v_pre.2.context = v_setup.2.1.context :=
    typeCheckConditions_context C v_setup.2.1 proc.spec.preconditions proc.header.name v_pre
      h_pre h_setup_wf h_setup_ne h_fwf
  have h_out_env : v_out.2 = v_pre.2 :=
    LMonoTys_resolveAliases_env_local _ v_pre.2 v_out.1 v_out.2 h_ra
  have h_penv := postEnv_wf C Env proc fr v_setup v_pre v_out h_ta h_setup h_pre h_ra h_wf h_fwf
    h_resolved
  let E4 := (v_out.snd.addInNewestContext (T := CoreLParams)
      (Lambda.LMonoTySignature.toTrivialLTy ((proc.header.outputs.keys).zip v_out.fst))).addInNewestContext
    ((v_setup.1.filter (fun x => (ListMap.keys proc.header.outputs).contains x.fst)).map
      (fun x => (CoreIdent.mkOld x.fst.name, LTy.forAll [] x.snd)))
  have h_post_ctx : v_post.2.context = E4.context :=
    typeCheckConditions_context C E4 proc.spec.postconditions proc.header.name v_post
      h_post h_penv.1 h_penv.2.1 h_fwf
  rw [h_post_ctx]
  show Maps.newest E4.context.types = _
  rw [addInNewestContext_newest_types, addInNewestContext_newest_types, h_out_env, h_pre_ctx]
  rw [setupInputEnv_newest_context_types C Env proc fr v_setup h_setup]
  rfl

/-- After instantiation, `subst [ids ↦ freshtvs.map ftvar] mty` has free vars ⊆ `freshtvs`,
    provided the original `mty`'s free vars are all declared in `ids`. -/
theorem subst_zip_freeVars_subset (ids freshtvs : List TyIdentifier) (mty : LMonoTy)
    (h_len : ids.length = freshtvs.length)
    (h_mty : ∀ v ∈ LMonoTy.freeVars mty, v ∈ ids) :
    ∀ w ∈ LMonoTy.freeVars (LMonoTy.subst [ids.zip (freshtvs.map LMonoTy.ftvar)] mty),
      w ∈ freshtvs := by
  intro w hw
  obtain ⟨v, hv_mty, hv_w⟩ := freeVars_subst_mem_exists [ids.zip (freshtvs.map LMonoTy.ftvar)] mty w hw
  have h_v_ids : v ∈ ids := h_mty v hv_mty
  rw [LMonoTy.subst_unfold] at hv_w
  simp only [Maps.find?] at hv_w
  cases h_find : Map.find? (ids.zip (freshtvs.map LMonoTy.ftvar)) v with
  | none =>
    exfalso
    have h_keys : Map.keys (ids.zip (freshtvs.map LMonoTy.ftvar)) = ids :=
      keys_zip_map_ftvar ids freshtvs h_len
    have h_some := mem_keys_find?_isSome _ v (by rw [h_keys]; exact h_v_ids)
    rw [h_find] at h_some; simp at h_some
  | some t =>
    rw [h_find] at hv_w
    have h_t_val : t ∈ Map.values (ids.zip (freshtvs.map LMonoTy.ftvar)) :=
      Map.find?_mem_values _ h_find
    simp only [List.zip] at h_t_val
    rw [Map.values_zipWith_eq_take] at h_t_val
    have h_t_mem : t ∈ freshtvs.map LMonoTy.ftvar := List.mem_of_mem_take h_t_val
    obtain ⟨u, hu_mem, hu_eq⟩ := List.mem_map.mp h_t_mem
    subst hu_eq
    simp only [LMonoTy.freeVars, List.mem_singleton] at hv_w
    subst hv_w
    exact hu_mem

/-- Old-scope roundtrip core (inout params): the body substitution `S'` (the unify of the
    `tyArg` constraints) sends each declared `orig` to its fresh var `fresh`, exactly as
    `tyArgSubst` does. -/
theorem subst_S'_eq_tyArgSubst_on_typeArg
    (tyArgSubst : Subst) (S_in S' : SubstInfo)
    (h_unify : Constraints.unify (tyArgSubst.flatten.map (fun kv => (LMonoTy.ftvar kv.1, kv.2))) S_in
      = .ok S')
    (orig : TyIdentifier) (fresh : TyIdentifier)
    (h_mem : (orig, LMonoTy.ftvar fresh) ∈ tyArgSubst.flatten)
    (h_fix : LMonoTy.subst S'.subst (LMonoTy.ftvar fresh) = LMonoTy.ftvar fresh) :
    LMonoTy.subst S'.subst (LMonoTy.ftvar orig) = LMonoTy.ftvar fresh := by
  have h_c_mem : (LMonoTy.ftvar orig, LMonoTy.ftvar fresh)
      ∈ tyArgSubst.flatten.map (fun kv => (LMonoTy.ftvar kv.1, kv.2)) := by
    rw [List.mem_map]
    exact ⟨(orig, LMonoTy.ftvar fresh), h_mem, rfl⟩
  have h_sound := Constraints.unify_sound _ _ _ h_unify _ h_c_mem
  rw [h_fix] at h_sound
  exact h_sound

/-- `subst.go S` fixes a scope whose bindings are all `S`-fixed. Applies to the checker's
    fresh signature scope, fixed by the body substitution `S'` (its type vars are the rigid
    params), so the `subst.go S'` layer collapses. -/
theorem subst_go_fixes_scope (S : Subst) (scope : Map CoreIdent LTy)
    (h : ∀ p : CoreIdent × LTy, p ∈ scope.toList → LTy.subst S p.2 = p.2) :
    TContext.types.subst.go S scope = scope := by
  induction scope with
  | nil => rfl
  | cons p rest ih =>
    obtain ⟨k, ty⟩ := p
    simp only [TContext.types.subst.go]
    rw [h (k, ty) (List.mem_cons_self)]
    rw [ih (fun q hq => h q (List.mem_cons_of_mem _ hq))]

/-- A nonempty `Maps` stack reconstructs as `newest :: pop`. -/
theorem maps_eq_newest_cons_pop (ts : Maps CoreIdent LTy) (h : ts ≠ []) :
    ts = Maps.newest ts :: Maps.pop ts := by
  cases ts with
  | nil => exact absurd rfl h
  | cons t rest => simp only [Maps.newest, Maps.pop]

/-- `subst.go` distributes over scope append (the newest scope is inputs++outputs++old). -/
theorem subst_go_append (S : Subst) (l1 l2 : List (CoreIdent × LTy)) :
    TContext.types.subst.go S (l1 ++ l2)
      = TContext.types.subst.go S l1 ++ TContext.types.subst.go S l2 := by
  induction l1 with
  | nil => rfl
  | cons p rest ih =>
    obtain ⟨k, ty⟩ := p
    show TContext.types.subst.go S ((k, ty) :: (rest ++ l2)) = _
    show (k, LTy.subst S ty) :: TContext.types.subst.go S (rest ++ l2) = _
    rw [ih]; rfl

/-- `subst.go` on a `forAll []`-mapped scope pushes the subst into each stored monotype. -/
theorem subst_go_trivial_map (S : Subst) (l : List (CoreIdent × LMonoTy)) :
    TContext.types.subst.go S (l.map (fun p => (p.1, LTy.forAll [] p.2)))
      = l.map (fun p => (p.1, LTy.forAll [] (LMonoTy.subst S p.2))) := by
  induction l with
  | nil => rfl
  | cons p rest ih =>
    obtain ⟨k, mty⟩ := p
    simp only [List.map_cons, TContext.types.subst.go, LTy.subst_forAll_nil, ih]

/-- `subst.go` on a `toTrivialLTy` scope pushes the `LMonoTy.subst` into each stored monotype. -/
theorem subst_go_toTrivialLTy (S : Subst) (sig : @LMonoTySignature Unit) :
    TContext.types.subst.go S (Lambda.LMonoTySignature.toTrivialLTy sig)
      = Lambda.LMonoTySignature.toTrivialLTy (sig.map (fun p => (p.1, LMonoTy.subst S p.2))) := by
  simp only [Lambda.LMonoTySignature.toTrivialLTy, List.map_map]
  exact subst_go_trivial_map S sig

/-- `subst.go` on an `mkOld`-keyed `forAll []` scope pushes the `LMonoTy.subst` into each stored
    monotype (keys `mkOld x.1.name` are unchanged). The old-inout scope of `body_context_find_agree`'s
    `h_newest`. -/
theorem subst_go_old_scope (S : Subst) {β : Type} (l : List β) (key : β → CoreIdent) (val : β → LMonoTy) :
    TContext.types.subst.go S
        (l.map (fun x => (key x, LTy.forAll [] (val x))))
      = l.map (fun x => (key x, LTy.forAll [] (LMonoTy.subst S (val x)))) := by
  induction l with
  | nil => rfl
  | cons p rest ih =>
    simp only [List.map_cons, TContext.types.subst.go, LTy.subst_forAll_nil, ih]

/-- The old-inout scope match (`old` sub-scope of the newest scope): the spec's `mkOld`-keyed
    renamed inout params equal the checker's `subst.go US (subst.go S' (mkOld-keyed filter of sig))`. -/
theorem old_scope_eq
    (sig : List (CoreIdent × LMonoTy)) (okeys : List CoreIdent) (US S' : Subst)
    (h_fix : ∀ x ∈ sig, ∀ v ∈ LMonoTy.freeVars x.snd,
      LMonoTy.subst S' (LMonoTy.ftvar v) = LMonoTy.ftvar v) :
    List.map (fun x => (CoreIdent.mkOld x.fst.name, LTy.forAll [] x.snd))
        (List.filter (fun x => okeys.contains x.fst)
          (sig.map (fun x => (x.fst, LMonoTy.subst US x.snd))))
      = TContext.types.subst.go US (TContext.types.subst.go S'
          (List.map (fun x => (CoreIdent.mkOld x.fst.name, LTy.forAll [] x.snd))
            (List.filter (fun x => okeys.contains x.fst) sig))) := by
  rw [subst_go_old_scope, subst_go_old_scope]
  rw [List.filter_map]
  have h_pred : ((fun x : CoreIdent × LMonoTy => okeys.contains x.fst) ∘
        fun x : CoreIdent × LMonoTy => (x.fst, LMonoTy.subst US x.snd))
      = (fun x : CoreIdent × LMonoTy => okeys.contains x.fst) := by
    funext x; rfl
  rw [h_pred, List.map_map]
  apply List.map_congr_left
  intro p hp
  have h_mem : p ∈ sig := (List.mem_filter.mp hp).1
  have h_pfix : LMonoTy.subst S' p.snd = p.snd :=
    LMonoTy.subst_eq_self_of_fixes _ _ (h_fix p h_mem)
  simp only [Function.comp, h_pfix]

/-- Per-scope collapse-then-rename for inputs/outputs: if every value of `sig` has free vars ⊆
    `freshtvs` and `S'` fixes every `freshtvs` var, then
    `subst.go userSubst (subst.go S' (toTrivialLTy sig)) = toTrivialLTy (sig.map (·, subst userSubst ·))`. -/
theorem subst_go_collapse_rename (US S' : Subst) (freshtvs : List TyIdentifier)
    (sig : @LMonoTySignature Unit)
    (h_closed : ∀ w ∈ LMonoTys.freeVars (ListMap.values sig), w ∈ freshtvs)
    (h_fix : ∀ v ∈ freshtvs, LMonoTy.subst S' (LMonoTy.ftvar v) = LMonoTy.ftvar v) :
    TContext.types.subst.go US
        (TContext.types.subst.go S' (Lambda.LMonoTySignature.toTrivialLTy sig))
      = Lambda.LMonoTySignature.toTrivialLTy
          (sig.map (fun p => (p.1, LMonoTy.subst US p.2))) := by
  rw [subst_go_toTrivialLTy S' sig, subst_go_toTrivialLTy]
  congr 1
  rw [List.map_map]
  apply List.map_congr_left
  intro p hp
  simp only [Function.comp]
  have h_fix_p : LMonoTy.subst S' p.2 = p.2 := by
    apply LMonoTy.subst_eq_self_of_fixes
    intro v hv
    apply h_fix
    apply h_closed
    rw [ListMap.values_eq_map_snd]
    exact LMonoTys.freeVars_mem_subset (List.mem_map_of_mem hp) hv
  rw [h_fix_p]

/-- `subst.go` fixes a scope whose every value (`∈ Map.values`) is closed. -/
theorem subst_go_fix_scope (S : Subst) (scope : Map CoreIdent LTy)
    (h : ∀ ty ∈ Map.values scope, LTy.freeVars ty = []) :
    TContext.types.subst.go S scope = scope := by
  induction scope with
  | nil => rfl
  | cons p rest ih =>
    obtain ⟨k, ty⟩ := p
    show (k, LTy.subst S ty) :: TContext.types.subst.go S rest = _
    rw [LTy.subst_eq_self_of_closed S ty
      (h ty (by show ty ∈ ty :: Map.values rest; exact List.mem_cons_self))]
    rw [ih (fun t ht => h t (by show t ∈ ty :: Map.values rest; exact List.mem_cons_of_mem _ ht))]

/-- Any substitution fixes a closed `Maps` stack — the ambient-tail collapse
    (both `S'` and `userSubst` leave the closed ambient untouched). Closed alone suffices. -/
theorem subst_fix_closed (S : Subst) (ts : Maps CoreIdent LTy)
    (h : ∀ ty ∈ Maps.values ts, LTy.freeVars ty = []) :
    TContext.types.subst ts S = ts := by
  induction ts with
  | nil => rfl
  | cons scope rest ih =>
    simp only [TContext.types.subst]
    rw [subst_go_fix_scope S scope (fun ty hty => h ty (by
      show ty ∈ scope.values ++ Maps.values rest; exact List.mem_append_left _ hty))]
    rw [ih (fun ty hty => h ty (by
      show ty ∈ scope.values ++ Maps.values rest; exact List.mem_append_right _ hty))]

/-- Body-context agreement assembly: given the LHS/RHS `types`-stack shapes, the newest-scope
    agreement (`h_newest`), and the ambient being closed, the two contexts agree on `find?`. -/
theorem body_context_find_agree
    (Env' : TContext Unit) (proc' : Procedure) (bodyΓ : TContext Unit)
    (S' userSubst : Subst) (ambient : Maps CoreIdent LTy) (freshScope declScope : Map CoreIdent LTy)
    (h_pbc : (procBodyContext Env' proc').types = declScope :: TContext.types.subst ambient S')
    (h_bodyΓ_types : bodyΓ.types
      = TContext.types.subst.go S' freshScope :: TContext.types.subst ambient S')
    (h_newest : declScope = TContext.types.subst.go userSubst (TContext.types.subst.go S' freshScope))
    (h_closed : ∀ ty ∈ Maps.values ambient, LTy.freeVars ty = []) :
    ∀ x, Maps.find? (procBodyContext Env' proc').types x
        = Maps.find? (TContext.subst bodyΓ userSubst).types x := by
  intro x
  have h_rhs : (TContext.subst bodyΓ userSubst).types
      = TContext.types.subst.go userSubst (TContext.types.subst.go S' freshScope)
        :: TContext.types.subst (TContext.types.subst ambient S') userSubst := by
    show TContext.types.subst bodyΓ.types userSubst = _
    rw [h_bodyΓ_types]
    simp only [TContext.types.subst]
  have h_S'_fix : TContext.types.subst ambient S' = ambient := subst_fix_closed S' ambient h_closed
  rw [h_pbc, h_rhs, h_newest, h_S'_fix]
  have h_us_fix : TContext.types.subst ambient userSubst = ambient := subst_fix_closed userSubst ambient h_closed
  rw [h_us_fix]

/-! ## h_IC support: `Statement.typeCheck` output is init-closed (mono + rigid-closed). -/

/-! ### Crux: `CmdType.postprocess` output is mono + rigid-closed. -/

/-- `postprocess` always stores a `forAll []` (mono) type. -/
theorem postprocess_boundVars (C : LContext CoreLParams) (Env : TEnv Unit)
    (ty ty' : LTy) (Env' : TEnv Unit)
    (h : CmdType.postprocess C Env ty = .ok (ty', Env')) :
    ty'.boundVars = [] := by
  simp only [CmdType.postprocess, Bind.bind, Except.bind, pure, Except.pure] at h
  split at h
  · split at h
    · simp only [reduceCtorEq] at h
    · simp only [Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨h_ty', _⟩ := h
      subst h_ty'
      simp only [LTy.boundVars]
  · exact absurd h (by simp)

/-- For `forAll []` types, `LTy.freeVars` = `LMonoTy.freeVars` of the mono coercion. -/
theorem LTy_freeVars_eq_mono_of_boundVars_nil (ty : LTy) (h : ty.boundVars = []) :
    LTy.freeVars ty = LMonoTy.freeVars ty.toMonoTypeUnsafe := by
  cases ty with
  | forAll xs mty =>
    simp only [LTy.boundVars] at h
    subst h
    simp only [LTy.freeVars, LTy.toMonoTypeUnsafe, List.removeAll, List.elem_nil,
      Bool.not_false]
    exact List.filter_eq_self.mpr (fun _ _ => rfl)

/-- Output of `Imperative.Cmd.typeCheck` is init-closed w.r.t. `C.rigidTypeVars`. -/
theorem Cmd_typeCheck_InitClosed (C : LContext CoreLParams) (Env : TEnv Unit)
    (cmd cmd' : Cmd Expression) (Env' : TEnv Unit)
    (h : Imperative.Cmd.typeCheck C Env cmd = .ok (cmd', Env')) :
    CmdInitClosed C.rigidTypeVars cmd' := by
  cases cmd with
  | init x xty e md =>
    simp only [Cmd.typeCheck, Bind.bind, Except.bind] at h
    elim_err h
    rename_i h_lookup_none
    split at h
    · -- det
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
      simp only [TypeContext.lookup, TypeContext.preprocess,
        TypeContext.postprocess, TypeContext.inferType, TypeContext.unifyTypes,
        TypeContext.freeVars, TypeContext.checkAnnotCompat] at *
      simp only [CmdInitClosed]
      have h_bv := postprocess_boundVars C Env_unified v1.fst v3.fst v3.snd h_postprocess
      have h_fv := postprocess_freeVars_rigid C Env_unified v1.fst v3.fst v3.snd h_postprocess
      refine ⟨h_bv, ?_⟩
      rw [← LTy_freeVars_eq_mono_of_boundVars_nil v3.fst h_bv]
      exact h_fv
    · -- nondet
      rename_i heq_nondet
      elim_err h
      rename_i v1 h_preprocess
      elim_err h
      rename_i v2 h_postprocess
      cases h
      simp only [TypeContext.lookup, TypeContext.preprocess,
        TypeContext.postprocess] at *
      simp only [CmdInitClosed]
      have h_bv := postprocess_boundVars C v1.snd v1.fst v2.fst v2.snd h_postprocess
      have h_fv := postprocess_freeVars_rigid C v1.snd v1.fst v2.fst v2.snd h_postprocess
      refine ⟨h_bv, ?_⟩
      rw [← LTy_freeVars_eq_mono_of_boundVars_nil v2.fst h_bv]
      exact h_fv
  | set x e md =>
    simp only [Cmd.typeCheck, Bind.bind, Except.bind] at h
    elim_err h
    rename_i xty h_lookup
    split at h
    · rename_i expr heq_det
      elim_err h; rename_i v2 h_infer
      elim_err h; rename_i Env_unified h_unify
      elim_err h; rename_i _u h_ck
      cases h; exact True.intro
    · rename_i heq; cases h; exact True.intro
  | assert l e md =>
    simp only [Cmd.typeCheck, Bind.bind, Except.bind] at h
    elim_err h; rename_i v2 h_infer
    elim_err h; rename_i _u h_ck
    split at h
    · cases h; exact True.intro
    · simp only [tryCatch, tryCatchThe, MonadExcept.tryCatch, MonadExceptOf.tryCatch, Except.tryCatch, reduceCtorEq] at h
  | assume l e md =>
    simp only [Cmd.typeCheck, Bind.bind, Except.bind] at h
    elim_err h; rename_i v2 h_infer
    elim_err h; rename_i _u h_ck
    split at h
    · cases h; exact True.intro
    · simp only [tryCatch, tryCatchThe, MonadExcept.tryCatch, MonadExceptOf.tryCatch, Except.tryCatch, reduceCtorEq] at h
  | cover l e md =>
    simp only [Cmd.typeCheck, Bind.bind, Except.bind] at h
    elim_err h; rename_i v2 h_infer
    elim_err h; rename_i _u h_ck
    split at h
    · cases h; exact True.intro
    · simp only [tryCatch, tryCatchThe, MonadExcept.tryCatch, MonadExceptOf.tryCatch, Except.tryCatch, reduceCtorEq] at h

/-- `Statement.typeCheckCmd` output is init-closed. `.call` output is trivially closed. -/
theorem typeCheckCmd_InitClosed (C : LContext CoreLParams) (Env : TEnv Unit)
    (P : Program) (cmd cmd' : Command) (Env' : TEnv Unit)
    (h : Statement.typeCheckCmd C Env P cmd = .ok (cmd', Env')) :
    CommandInitClosed C.rigidTypeVars cmd' := by
  cases cmd with
  | cmd c =>
    unfold Statement.typeCheckCmd at h
    simp only [Bind.bind, Except.bind] at h
    elim_err h with v h_tc
    obtain ⟨c', Env_inner⟩ := v
    simp only [Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨h_cmd_eq, _⟩ := h
    subst h_cmd_eq
    simp only [CommandInitClosed]
    exact Cmd_typeCheck_InitClosed C Env c c' Env_inner h_tc
  | call pname callArgs md =>
    -- output is a `.call`, so CommandInitClosed is `True`.
    unfold Statement.typeCheckCmd at h
    simp only [Bind.bind, Except.bind] at h
    split at h
    · simp only [tryCatchThe, tryCatch, MonadExcept.tryCatch] at h; contradiction
    · rename_i proc heq_find
      simp only [tryCatchThe, tryCatch, MonadExcept.tryCatch,
                 MonadExceptOf.tryCatch, Except.tryCatch] at h
      elim_err h with h_inner h_eq
      obtain ⟨h_cmd, h_env⟩ := Prod.mk.inj (Except.ok.inj h)
      elim_err h_eq with h_lhs_exist
      elim_err h_eq with h_out_arity
      elim_err h_eq with h_inp_arity
      elim_err h_eq with h_inout_check
      elim_err h_eq with h_inout_valid
      elim_err h_eq with v1 h_inst_lhs
      elim_err h_eq with lhs_tys Env1
      elim_err h_eq with v2 h_fvc
      elim_err h_eq with v3 h_inst_inputs
      elim_err h_eq with v4 h_resolves
      elim_err h_eq with h_rigid_check
      cases h_eq
      subst h_cmd
      simp only [CommandInitClosed]

/-- `goBlock` returns its INPUT context `C` and its output body comes from an inner
    `go` on the pushed environment (WF-free structural inversion). -/
theorem goBlock_inv (P : Program) (op : Option Procedure)
    (C : LContext CoreLParams) (Env : TEnv Unit) (bss acc : List Statement)
    (labels : List String) (ss' : List Statement) (Env' : TEnv Unit) (C' : LContext CoreLParams)
    (h : Statement.typeCheckAux.goBlock P op C Env bss acc labels = .ok (ss', Env', C')) :
    C' = C ∧ ∃ Env_i C_i,
      Statement.typeCheckAux.go P op C Env.pushEmptyContext bss acc labels
        = .ok (ss', Env_i, C_i) := by
  unfold Statement.typeCheckAux.goBlock at h
  simp only [Bind.bind, Except.bind] at h
  cases h_body : Statement.typeCheckAux.go P op C Env.pushEmptyContext bss acc labels with
  | error e => rw [h_body] at h; simp only [reduceCtorEq] at h
  | ok v =>
    obtain ⟨bss_i, Env_i, C_i⟩ := v
    rw [h_body] at h
    simp only [Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨h_ss, _, h_C⟩ := h
    refine ⟨h_C.symm, Env_i, C_i, ?_⟩
    rw [h_ss]

/-! ### The go.induct structural lemma. -/

theorem typeCheckAux_go_InitClosed (P : Program) (op : Option Procedure)
    (C : LContext CoreLParams) (Env : TEnv Unit) (ss acc : List Statement) (labels : List String)
    (ss' : List Statement) (Env' : TEnv Unit) (C' : LContext CoreLParams)
    (h : Statement.typeCheckAux.go P op C Env ss acc labels = .ok (ss', Env', C'))
    (h_acc : StmtsInitClosed C.rigidTypeVars acc) :
    StmtsInitClosed C.rigidTypeVars ss' := by
  refine (Statement.typeCheckAux.go.induct P op
    (motive1 := fun C Env ss acc labels =>
      ∀ ss' Env' C',
      Statement.typeCheckAux.go P op C Env ss acc labels = .ok (ss', Env', C') →
      StmtsInitClosed C.rigidTypeVars acc →
      StmtsInitClosed C.rigidTypeVars ss')
    (motive2 := fun C Env bss acc labels =>
      ∀ ss' Env' C',
      Statement.typeCheckAux.goBlock P op C Env bss acc labels = .ok (ss', Env', C') →
      StmtsInitClosed C.rigidTypeVars acc →
      StmtsInitClosed C.rigidTypeVars ss')
    ?case_nil ?case_cmd ?case_block_clash ?case_block ?case_ite ?case_loop
    ?case_exit ?case_funcDecl ?case_typeDecl ?case_goBlock
    C Env ss acc labels) ss' Env' C' h h_acc
  case case_nil =>
    intro C₀ Env₀ acc₀ labels₀ ss'₀ Env'₀ C'₀ h₀ hacc₀
    simp only [Statement.typeCheckAux.go, Except.ok.injEq, Prod.mk.injEq] at h₀
    obtain ⟨hss, _, _⟩ := h₀
    subst hss
    intro s hs
    exact hacc₀ s (List.mem_reverse.mp hs)
  case case_cmd =>
    intro C₀ Env₀ acc₀ labels₀ srest₀ cmd₀ ih ss'₀ Env'₀ C'₀ h₀ hacc₀
    simp only [Statement.typeCheckAux.go, Bind.bind, Except.bind] at h₀
    cases h_tc : Statement.typeCheckCmd C₀ Env₀ P cmd₀ with
    | error e => rw [h_tc] at h₀; simp at h₀
    | ok v =>
      obtain ⟨c', Env_mid⟩ := v
      rw [h_tc] at h₀
      simp only at h₀
      have h_c'_ic : CommandInitClosed C₀.rigidTypeVars c' :=
        typeCheckCmd_InitClosed C₀ Env₀ P cmd₀ c' Env_mid h_tc
      have h_acc' : StmtsInitClosed C₀.rigidTypeVars (Stmt.cmd c' :: acc₀) := by
        intro s hs
        rcases List.mem_cons.mp hs with h_eq | h_mem
        · subst h_eq; rw [StmtInitClosed_cmd]; exact h_c'_ic
        · exact hacc₀ s h_mem
      exact ih (Stmt.cmd c') Env_mid C₀ ss'₀ Env'₀ C'₀ h₀ h_acc'
  case case_block_clash =>
    intro C₀ Env₀ acc₀ labels₀ srest₀ label₀ bss₀ md₀ h_clash ih_tail ih_block
      ss'₀ Env'₀ C'₀ h_goeq hacc₀
    rw [Statement.typeCheckAux.go] at h_goeq
    simp only [h_clash, if_true, Bind.bind, Except.bind] at h_goeq
    exact absurd h_goeq (by simp)
  case case_block =>
    intro C₀ Env₀ acc₀ labels₀ srest₀ label₀ bss₀ md₀ h_noclash ih_tail ih_block
      ss'₀ Env'₀ C'₀ h_goeq hacc₀
    rw [Statement.typeCheckAux.go] at h_goeq
    simp only [h_noclash, if_false, Bool.false_eq_true, Bind.bind, Except.bind] at h_goeq
    cases h_blk : Statement.typeCheckAux.goBlock P op C₀ Env₀ bss₀ [] (label₀ :: labels₀) with
    | error e => rw [h_blk] at h_goeq; simp [pure, Except.pure] at h_goeq
    | ok v =>
      obtain ⟨bss', Env_blk, C_blk⟩ := v
      rw [h_blk] at h_goeq
      simp only [pure, Except.pure] at h_goeq
      obtain ⟨h_Cblk, _⟩ := goBlock_inv P op C₀ Env₀ bss₀ [] (label₀ :: labels₀) bss' Env_blk C_blk h_blk
      subst C_blk
      -- body InitClosed via goBlock motive with acc = [].
      have h_body_ic : StmtsInitClosed C₀.rigidTypeVars bss' := by
        refine ih_block bss' Env_blk C₀ h_blk ?_
        intro s hs; exact absurd hs (List.not_mem_nil)
      have h_acc' : StmtsInitClosed C₀.rigidTypeVars (Stmt.block label₀ bss' md₀ :: acc₀) := by
        intro s hs
        rcases List.mem_cons.mp hs with h_eq | h_mem
        · subst h_eq; rw [StmtInitClosed_block]; exact h_body_ic
        · exact hacc₀ s h_mem
      exact ih_tail (Stmt.block label₀ bss' md₀) Env_blk C₀ ss'₀ Env'₀ C'₀ h_goeq h_acc'
  case case_ite =>
    intro C₀ Env₀ acc₀ labels₀ srest₀ cond₀ tss₀ ess₀ md₀ ih_tail ih_branches
      ss'₀ Env'₀ C'₀ h_goeq hacc₀
    unfold Statement.typeCheckAux.go at h_goeq
    simp only [Bind.bind, Except.bind, tryCatchThe, tryCatch, MonadExcept.tryCatch,
      MonadExceptOf.tryCatch, Except.tryCatch, Except.mapError] at h_goeq
    cases cond₀ with
    | det c =>
      simp only at h_goeq ih_branches
      obtain ⟨ih_then, ih_else⟩ := ih_branches
      cases h_fvc : Env₀.freeVarCheck c (Std.format "[" ++ Std.format (Stmt.ite (ExprOrNondet.det c) tss₀ ess₀ md₀) ++ Std.format "]") with
      | error e => rw [h_fvc] at h_goeq; simp only [reduceCtorEq] at h_goeq
      | ok _ =>
        rw [h_fvc] at h_goeq
        simp only at h_goeq
        cases h_res : LExpr.resolve C₀ Env₀ c with
        | error e => rw [h_res] at h_goeq; simp only [reduceCtorEq] at h_goeq
        | ok vr =>
          obtain ⟨conda, Env_r⟩ := vr
          rw [h_res] at h_goeq
          simp only at h_goeq
          cases h_cac : CmdType.checkAnnotCompat C₀ Env_r with
          | error e => rw [h_cac] at h_goeq; simp only [reduceCtorEq] at h_goeq
          | ok _ =>
            rw [h_cac] at h_goeq
            simp only at h_goeq
            elim_err h_goeq with v heq
            obtain ⟨h_condty, h_blocks⟩ :=
              condty_bool_match_ok conda.toLMonoTy _ _ _ v heq
            cases h_t : Statement.typeCheckAux.goBlock P op C₀ Env_r tss₀ [] labels₀ with
            | error e => rw [h_t] at h_blocks; simp only [reduceCtorEq] at h_blocks
            | ok vt =>
              obtain ⟨tss', Env_t, C_t⟩ := vt
              rw [h_t] at h_blocks
              simp only at h_blocks
              obtain ⟨h_Ct, _⟩ := goBlock_inv P op C₀ Env_r tss₀ [] labels₀ tss' Env_t C_t h_t
              subst C_t
              cases h_e : Statement.typeCheckAux.goBlock P op C₀ Env_t ess₀ [] labels₀ with
              | error e => rw [h_e] at h_blocks; simp only [reduceCtorEq] at h_blocks
              | ok ve =>
                obtain ⟨ess', Env_e, C_e⟩ := ve
                rw [h_e] at h_blocks
                simp only [Except.ok.injEq] at h_blocks
                obtain ⟨h_Ce, _⟩ := goBlock_inv P op C₀ Env_t ess₀ [] labels₀ ess' Env_e C_e h_e
                subst C_e
                subst h_blocks
                simp only at h_goeq
                have h_tss_ic : StmtsInitClosed C₀.rigidTypeVars tss' := by
                  refine ih_then Env_r tss' Env_t C₀ h_t ?_
                  intro s hs; exact absurd hs (List.not_mem_nil)
                have h_ess_ic : StmtsInitClosed C₀.rigidTypeVars ess' := by
                  refine ih_else Env_t C₀ ess' Env_e C₀ h_e ?_
                  intro s hs; exact absurd hs (List.not_mem_nil)
                have h_acc' : StmtsInitClosed C₀.rigidTypeVars
                    (Stmt.ite (.det (unresolved conda)) tss' ess' md₀ :: acc₀) := by
                  intro s hs
                  rcases List.mem_cons.mp hs with h_eq | h_mem
                  · subst h_eq; rw [StmtInitClosed_ite]; exact ⟨h_tss_ic, h_ess_ic⟩
                  · exact hacc₀ s h_mem
                exact ih_tail (Stmt.ite (.det (unresolved conda)) tss' ess' md₀) Env_e C₀
                  ss'₀ Env'₀ C'₀ h_goeq h_acc'
    | nondet =>
      simp only at h_goeq ih_branches
      obtain ⟨ih_then, ih_else⟩ := ih_branches
      cases h_t : Statement.typeCheckAux.goBlock P op C₀ Env₀ tss₀ [] labels₀ with
      | error e => rw [h_t] at h_goeq; simp only [reduceCtorEq] at h_goeq
      | ok vt =>
        obtain ⟨tss', Env_t, C_t⟩ := vt
        rw [h_t] at h_goeq
        simp only at h_goeq
        obtain ⟨h_Ct, _⟩ := goBlock_inv P op C₀ Env₀ tss₀ [] labels₀ tss' Env_t C_t h_t
        subst C_t
        cases h_e : Statement.typeCheckAux.goBlock P op C₀ Env_t ess₀ [] labels₀ with
        | error e => rw [h_e] at h_goeq; simp only [reduceCtorEq] at h_goeq
        | ok ve =>
          obtain ⟨ess', Env_e, C_e⟩ := ve
          rw [h_e] at h_goeq
          simp only at h_goeq
          obtain ⟨h_Ce, _⟩ := goBlock_inv P op C₀ Env_t ess₀ [] labels₀ ess' Env_e C_e h_e
          subst C_e
          have h_tss_ic : StmtsInitClosed C₀.rigidTypeVars tss' := by
            refine ih_then tss' Env_t C₀ h_t ?_
            intro s hs; exact absurd hs (List.not_mem_nil)
          have h_ess_ic : StmtsInitClosed C₀.rigidTypeVars ess' := by
            refine ih_else Env_t C₀ ess' Env_e C₀ h_e ?_
            intro s hs; exact absurd hs (List.not_mem_nil)
          have h_acc' : StmtsInitClosed C₀.rigidTypeVars
              (Stmt.ite .nondet tss' ess' md₀ :: acc₀) := by
            intro s hs
            rcases List.mem_cons.mp hs with h_eq | h_mem
            · subst h_eq; rw [StmtInitClosed_ite]; exact ⟨h_tss_ic, h_ess_ic⟩
            · exact hacc₀ s h_mem
          exact ih_tail (Stmt.ite .nondet tss' ess' md₀) Env_e C₀ ss'₀ Env'₀ C'₀ h_goeq h_acc'
  case case_loop =>
    intro C₀ Env₀ acc₀ labels₀ srest₀ guard₀ measure₀ invariant₀ bss₀ md₀ ih_tail ih_body
      ss'₀ Env'₀ C'₀ h_goeq hacc₀
    unfold Statement.typeCheckAux.go at h_goeq
    simp only [Bind.bind, Except.bind, tryCatchThe, tryCatch, MonadExcept.tryCatch,
      MonadExceptOf.tryCatch, Except.tryCatch, Except.mapError] at h_goeq
    elim_err h_goeq with v heq
    have h_body := trycatch_ok _ _ v heq
    clear heq
    -- Shared tail for both guard branches, built existentially over the goBlock/output-loop shape.
    have h_finish : ∀ (guarda' : ExprOrNondet Expression) (mtOpt' : Option (LExprT CoreLParams.mono))
        (it' : List (String × LExprT CoreLParams.mono)) (Env_inv : TEnv Unit),
        (∃ tb Env_loop C_loop,
          Statement.typeCheckAux.goBlock P op C₀ Env_inv bss₀ [] labels₀ = .ok (tb, Env_loop, C_loop) ∧
          v = (Stmt.loop guarda' (Option.map unresolved mtOpt')
                (List.map (fun x => (x.fst, unresolved x.snd)) it') tb md₀, Env_loop, C_loop)) →
        StmtsInitClosed C₀.rigidTypeVars ss'₀ := by
      intro guarda' mtOpt' it' Env_inv h_gb
      obtain ⟨tb, Env_loop, C_loop, h_gb_eq, h_v⟩ := h_gb
      subst h_v
      obtain ⟨h_Cloop, _⟩ := goBlock_inv P op C₀ Env_inv bss₀ [] labels₀ tb Env_loop C_loop h_gb_eq
      subst C_loop
      simp only at h_goeq
      have h_body_ic : StmtsInitClosed C₀.rigidTypeVars tb := by
        refine ih_body Env_inv tb Env_loop C₀ h_gb_eq ?_
        intro s hs; exact absurd hs (List.not_mem_nil)
      have h_acc' : StmtsInitClosed C₀.rigidTypeVars
          (Stmt.loop guarda' (Option.map unresolved mtOpt')
            (List.map (fun x => (x.fst, unresolved x.snd)) it') tb md₀ :: acc₀) := by
        intro s hs
        rcases List.mem_cons.mp hs with h_eq | h_mem
        · subst h_eq; rw [StmtInitClosed_loop]; exact h_body_ic
        · exact hacc₀ s h_mem
      exact ih_tail _ Env_loop C₀ ss'₀ Env'₀ C'₀ h_goeq h_acc'
    cases guard₀ with
    | det g =>
      simp only at h_body
      elim_err h_body with hfvc_v hfvc_eq
      elim_err h_body with res_v res_eq
      obtain ⟨ga, Env_g⟩ := res_v
      simp only [pure, Except.pure] at h_body
      obtain ⟨h_g_bool, h_body⟩ := guard_bool_if_ok _ _ _ _ h_body
      elim_err h_body with mres mres_eq
      obtain ⟨mtOpt, Env_m⟩ := mres
      elim_err h_body with fres fres_eq
      obtain ⟨it, Env_inv⟩ := fres
      elim_err h_body with cac_v cac_eq
      simp only at fres_eq cac_eq h_body
      have h_gb : ∃ tb Env_loop C_loop,
          Statement.typeCheckAux.goBlock P op C₀ Env_inv bss₀ [] labels₀ = .ok (tb, Env_loop, C_loop) ∧
          v = (Stmt.loop (ExprOrNondet.det (unresolved ga)) (Option.map unresolved mtOpt)
                (List.map (fun x => (x.fst, unresolved x.snd)) it) tb md₀, Env_loop, C_loop) := by
        split at h_body
        · elim_err h_body with gbv h_gbeq
          obtain ⟨tb, Env_loop, C_loop⟩ := gbv
          rw [Except.ok.injEq] at h_body
          exact ⟨tb, Env_loop, C_loop, h_gbeq, h_body.symm⟩
        · elim_err h_body with gbv h_gbeq
          obtain ⟨tb, Env_loop, C_loop⟩ := gbv
          rw [Except.ok.injEq] at h_body
          exact ⟨tb, Env_loop, C_loop, h_gbeq, h_body.symm⟩
        · simp only [reduceCtorEq] at h_body
      exact h_finish _ mtOpt it Env_inv h_gb
    | nondet =>
      simp only [pure, Except.pure] at h_body
      elim_err h_body with mres mres_eq
      obtain ⟨mtOpt, Env_m⟩ := mres
      elim_err h_body with fres fres_eq
      obtain ⟨it, Env_inv⟩ := fres
      elim_err h_body with cac_v cac_eq
      simp only at fres_eq cac_eq h_body
      have h_gb : ∃ tb Env_loop C_loop,
          Statement.typeCheckAux.goBlock P op C₀ Env_inv bss₀ [] labels₀ = .ok (tb, Env_loop, C_loop) ∧
          v = (Stmt.loop ExprOrNondet.nondet (Option.map unresolved mtOpt)
                (List.map (fun x => (x.fst, unresolved x.snd)) it) tb md₀, Env_loop, C_loop) := by
        split at h_body
        · elim_err h_body with gbv h_gbeq
          obtain ⟨tb, Env_loop, C_loop⟩ := gbv
          rw [Except.ok.injEq] at h_body
          exact ⟨tb, Env_loop, C_loop, h_gbeq, h_body.symm⟩
        · elim_err h_body with gbv h_gbeq
          obtain ⟨tb, Env_loop, C_loop⟩ := gbv
          rw [Except.ok.injEq] at h_body
          exact ⟨tb, Env_loop, C_loop, h_gbeq, h_body.symm⟩
        · simp only [reduceCtorEq] at h_body
      exact h_finish _ mtOpt it Env_inv h_gb
  case case_exit =>
    intro C₀ Env₀ acc₀ labels₀ srest₀ l₀ md₀ ih_tail ss'₀ Env'₀ C'₀ h_goeq hacc₀
    unfold Statement.typeCheckAux.go at h_goeq
    simp only [Bind.bind, Except.bind, tryCatchThe, tryCatch, MonadExcept.tryCatch,
      MonadExceptOf.tryCatch, Except.tryCatch] at h_goeq
    cases op with
    | none => simp only [reduceCtorEq] at h_goeq
    | some proc =>
      by_cases h_lbl : labels₀.contains l₀
      · simp only [h_lbl, if_true] at h_goeq
        have h_acc' : StmtsInitClosed C₀.rigidTypeVars (Stmt.exit l₀ md₀ :: acc₀) := by
          intro s hs
          rcases List.mem_cons.mp hs with h_eq | h_mem
          · subst h_eq; simp only [StmtInitClosed]
          · exact hacc₀ s h_mem
        exact ih_tail (Stmt.exit l₀ md₀) Env₀ C₀ ss'₀ Env'₀ C'₀ h_goeq h_acc'
      · simp only [h_lbl, if_false, Bool.false_eq_true, reduceCtorEq] at h_goeq
  case case_funcDecl =>
    intro C₀ Env₀ acc₀ labels₀ srest₀ decl₀ md₀ ih_tail ss'₀ Env'₀ C'₀ h_goeq hacc₀
    obtain ⟨func0, func, Env_mid, decl', h_rec, h_of, h_ft, h_tail_eq⟩ :=
      Statement.typeCheckAux_go_funcDecl_inv P op C₀ Env₀ decl₀ md₀ srest₀ acc₀ labels₀
        ss'₀ Env'₀ C'₀ h_goeq
    have h_rig : (C₀.addFactoryFunction func.toLFunc).rigidTypeVars = C₀.rigidTypeVars :=
      addFactoryFunction_rigidTypeVars C₀ func.toLFunc
    have h_acc' : StmtsInitClosed (C₀.addFactoryFunction func.toLFunc).rigidTypeVars
        (Stmt.funcDecl decl' md₀ :: acc₀) := by
      rw [h_rig]
      intro s hs
      rcases List.mem_cons.mp hs with h_eq | h_mem
      · subst h_eq; simp only [StmtInitClosed]
      · exact hacc₀ s h_mem
    have h_out := ih_tail (Stmt.funcDecl decl' md₀) Env_mid (C₀.addFactoryFunction func.toLFunc)
      ss'₀ Env'₀ C'₀ h_tail_eq h_acc'
    rw [h_rig] at h_out
    exact h_out
  case case_typeDecl =>
    intro C₀ Env₀ acc₀ labels₀ srest₀ tc₀ md₀ ih_tail ss'₀ Env'₀ C'₀ h_goeq hacc₀
    unfold Statement.typeCheckAux.go at h_goeq
    simp only [Bind.bind, Except.bind, tryCatchThe, tryCatch, MonadExcept.tryCatch,
      MonadExceptOf.tryCatch, Except.tryCatch] at h_goeq
    cases h_add : C₀.addKnownTypeWithError { name := tc₀.name, metadata := tc₀.numargs }
        (md₀.toDiagnosticF (Std.format "Type '" ++ Std.format tc₀.name ++ Std.format "' is already declared")) with
    | error e => rw [h_add] at h_goeq; simp only [reduceCtorEq] at h_goeq
    | ok C_mid =>
      rw [h_add] at h_goeq
      simp only at h_goeq
      obtain ⟨_, h_rig⟩ := addKnownTypeWithError_preserves C₀ C_mid _ _ h_add
      have h_acc' : StmtsInitClosed C_mid.rigidTypeVars (Stmt.typeDecl tc₀ md₀ :: acc₀) := by
        rw [h_rig]
        intro s hs
        rcases List.mem_cons.mp hs with h_eq | h_mem
        · subst h_eq; simp only [StmtInitClosed]
        · exact hacc₀ s h_mem
      have h_out := ih_tail (Stmt.typeDecl tc₀ md₀) Env₀ C_mid ss'₀ Env'₀ C'₀ h_goeq h_acc'
      rw [h_rig] at h_out
      exact h_out
  case case_goBlock =>
    intro C₀ Env₀ bss₀ acc₀ labels₀ Env₁ ih_body ss'₀ Env'₀ C'₀ h_goeq hacc₀
    unfold Statement.typeCheckAux.goBlock at h_goeq
    simp only [Bind.bind, Except.bind] at h_goeq
    cases h_body_run : Statement.typeCheckAux.go P op C₀ Env₀.pushEmptyContext bss₀ acc₀ labels₀ with
    | error e => rw [h_body_run] at h_goeq; simp only [reduceCtorEq] at h_goeq
    | ok v =>
      obtain ⟨bss', Env_body, C_body⟩ := v
      rw [h_body_run] at h_goeq
      simp only [Except.ok.injEq, Prod.mk.injEq] at h_goeq
      obtain ⟨hss, _, _⟩ := h_goeq
      subst hss
      exact ih_body bss' Env_body C_body h_body_run hacc₀

/-! ### Subst preserves InitClosed when S fixes rigid vars. -/

/-- If `S` fixes rigid vars, `Cmd.subst S` preserves `CmdInitClosed`. -/
theorem subst_preserves_CmdInitClosed (rig : List TyIdentifier) (S : Subst)
    (h_fix : ∀ v, v ∈ rig → LMonoTy.subst S (.ftvar v) = .ftvar v)
    (c : Cmd Expression) (h_ic : CmdInitClosed rig c) :
    CmdInitClosed rig (Cmd.subst S c) := by
  cases c with
  | init x xty e md =>
    simp only [CmdInitClosed] at h_ic ⊢
    obtain ⟨h_bv, h_fv⟩ := h_ic
    -- `S` fixes every free var of `xty` (all rigid), so `LTy.subst S xty = xty`.
    have h_fix_xty : ∀ v, v ∈ LTy.freeVars xty → LMonoTy.subst S (.ftvar v) = .ftvar v := by
      intro v hv
      rw [LTy_freeVars_eq_mono_of_boundVars_nil xty h_bv] at hv
      exact h_fix v (h_fv v hv)
    have h_eq : LTy.subst S xty = xty := LTy.subst_eq_self_of_fixes_mono S xty h_bv h_fix_xty
    rw [Cmd.subst]
    rw [h_eq]
    exact ⟨h_bv, h_fv⟩
  | set x e md => rw [Cmd.subst]; exact True.intro
  | assert l e md => rw [Cmd.subst]; exact True.intro
  | assume l e md => rw [Cmd.subst]; exact True.intro
  | cover l e md => rw [Cmd.subst]; exact True.intro

/-- If `S` fixes rigid vars, `Command.subst S` preserves `CommandInitClosed`. -/
theorem subst_preserves_CommandInitClosed (rig : List TyIdentifier) (S : Subst)
    (h_fix : ∀ v, v ∈ rig → LMonoTy.subst S (.ftvar v) = .ftvar v)
    (c : Command) (h_ic : CommandInitClosed rig c) :
    CommandInitClosed rig (Command.subst S c) := by
  cases c with
  | cmd c0 =>
    simp only [CommandInitClosed] at h_ic ⊢
    rw [Command.subst]
    exact subst_preserves_CmdInitClosed rig S h_fix c0 h_ic
  | call pname args md =>
    rw [Command_subst_call]
    simp only [CommandInitClosed]

/-- `Statement.subst` by a substitution fixing the rigid vars preserves `StmtInitClosed`. -/
theorem subst_preserves_StmtInitClosed (rig : List TyIdentifier) (S : Subst)
    (h_fix : ∀ v, v ∈ rig → LMonoTy.subst S (.ftvar v) = .ftvar v)
    (s : Statement) (h_ic : StmtInitClosed rig s) :
    StmtInitClosed rig (Statement.subst S s) := by
  refine (Statement.subst.induct S
    (motive_1 := fun ss acc =>
      StmtsInitClosed rig acc → StmtsInitClosed rig ss →
      StmtsInitClosed rig (Statement.subst.go S ss acc))
    (motive_2 := fun s =>
      StmtInitClosed rig s → StmtInitClosed rig (Statement.subst S s))
    ?cmd ?block ?ite ?loop ?exit ?funcDecl ?typeDecl ?nil ?cons s) h_ic
  case cmd =>
    intro cmd h_ic0
    rw [StmtInitClosed_cmd] at h_ic0
    simp only [Statement.subst, StmtInitClosed_cmd]
    exact subst_preserves_CommandInitClosed rig S h_fix cmd h_ic0
  case block =>
    intro label bss md ih h_ic0
    rw [StmtInitClosed_block] at h_ic0
    simp only [Statement.subst, StmtInitClosed_block]
    have h_go := ih (fun s hs => absurd hs (List.not_mem_nil)) h_ic0
    intro s hs; exact h_go s hs
  case ite =>
    intro cond tss ess md ih_t ih_e h_ic0
    rw [StmtInitClosed_ite] at h_ic0
    simp only [Statement.subst, StmtInitClosed_ite]
    refine ⟨?_, ?_⟩
    · have h_go := ih_t (fun s hs => absurd hs (List.not_mem_nil)) h_ic0.1
      intro s hs; exact h_go s hs
    · have h_go := ih_e (fun s hs => absurd hs (List.not_mem_nil)) h_ic0.2
      intro s hs; exact h_go s hs
  case loop =>
    intro guard measure invariant bss md ih h_ic0
    rw [StmtInitClosed_loop] at h_ic0
    simp only [Statement.subst, StmtInitClosed_loop]
    have h_go := ih (fun s hs => absurd hs (List.not_mem_nil)) h_ic0
    intro s hs; exact h_go s hs
  case exit =>
    intro l md h_ic0
    simp only [Statement.subst, StmtInitClosed]
  case funcDecl =>
    intro decl md h_ic0
    simp only [Statement.subst, StmtInitClosed]
  case typeDecl =>
    intro tc md h_ic0
    simp only [Statement.subst, StmtInitClosed]
  case nil =>
    intro acc h_acc _
    rw [Statement.subst.go]
    intro s hs; exact h_acc s (List.mem_reverse.mp hs)
  case cons =>
    intro acc s srest ih_s ih_rest h_acc h_ss
    rw [Statement.subst.go]
    have h_s_ic : StmtInitClosed rig s := h_ss s List.mem_cons_self
    have h_ss_tail : StmtsInitClosed rig srest := fun s' hs' => h_ss s' (List.mem_cons_of_mem s hs')
    have h_acc' : StmtsInitClosed rig (Statement.subst S s :: acc) := by
      intro s' hs'
      rcases List.mem_cons.mp hs' with h_eq | h_mem
      · subst h_eq; exact ih_s h_s_ic
      · exact h_acc s' h_mem
    exact ih_rest h_acc' h_ss_tail

/-! ### Statement typechecking yields `InitClosed`. -/

theorem statement_typeCheck_InitClosed (C : LContext CoreLParams) (Env : TEnv Unit)
    (P : Program) (op : Option Procedure) (ss ss' : List Statement) (Env' : TEnv Unit)
    (h : Statement.typeCheck C Env P op ss = .ok (ss', Env'))
    (h_wf : TEnvWF (T := CoreLParams) Env) (h_fwf : FactoryWF C.functions)
    (h_ne : Env.context.types ≠ []) (h_mono : ContextMono Env.context)
    (h_rigid_inv : ∀ v, v ∈ C.rigidTypeVars →
      LMonoTy.subst Env.stateSubstInfo.subst (.ftvar v) = .ftvar v)
    (h_closed : CalledProcsClosed P) :
    StmtsInitClosed C.rigidTypeVars ss' := by
  simp only [Statement.typeCheck, Statement.typeCheckAux, Bind.bind, Except.bind] at h
  cases h_aux : Statement.typeCheckAux.go P op C Env ss [] [] with
  | error e => rw [h_aux] at h; simp only [reduceCtorEq] at h
  | ok w =>
    obtain ⟨ssA, Env_aux, C_aux⟩ := w
    rw [h_aux] at h
    simp only [Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨h_ss', _⟩ := h
    have h_ssA_ic : StmtsInitClosed C.rigidTypeVars ssA :=
      typeCheckAux_go_InitClosed P op C Env ss [] [] ssA Env_aux C_aux h_aux
        (fun s hs => absurd hs (List.not_mem_nil))
    have h_pres := typeCheckAux_go_preserves C Env P op ss [] [] ssA Env_aux C_aux
      h_aux h_wf h_fwf h_ne h_mono h_rigid_inv h_closed
    have h_fix : ∀ v, v ∈ C.rigidTypeVars →
        LMonoTy.subst Env_aux.stateSubstInfo.subst (.ftvar v) = .ftvar v := by
      intro v hv; exact h_pres.rigid_inv v (h_pres.rigid_eq ▸ hv)
    rw [← h_ss', Statement.subst_go_nil]
    intro s hs
    simp only [List.mem_map] at hs
    obtain ⟨s0, h_s0_mem, h_s0_eq⟩ := hs
    subst h_s0_eq
    exact subst_preserves_StmtInitClosed C.rigidTypeVars Env_aux.stateSubstInfo.subst h_fix
      s0 (h_ssA_ic s0 h_s0_mem)


/-! ## Annotated body derivation transports across a `rigidTypeVars` drop. -/

theorem RigidAnnotCompat_antitone (aliases : List TypeAlias) (R1 R2 : List Lambda.TyIdentifier)
    (ann mty : LMonoTy) (h_sub : R2 ⊆ R1)
    (h : RigidAnnotCompat aliases R1 ann mty) :
    RigidAnnotCompat aliases R2 ann mty := by
  obtain ⟨σ, h_fix, h_ae⟩ := h
  exact ⟨σ, fun v hv => h_fix v (h_sub hv), h_ae⟩

/-- `CmdHasTypeA` (annotated) transports under a rigid-set drop `R2 ⊆ C.rigidTypeVars`.
    Only init cases read `C.rigidTypeVars` (via antitone `RigidAnnotCompat`); the rest ignore C. -/
theorem CmdHasTypeA_rig_drop (C : LContext CoreLParams) (R2 : List Lambda.TyIdentifier)
    (Γ : TContext Unit) (c : Cmd Expression) (Γ' : TContext Unit)
    (h : @CmdHasType' LMonoTy C instHasTypeA Γ c Γ')
    (h_sub : R2 ⊆ C.rigidTypeVars) :
    @CmdHasType' LMonoTy ({ C with rigidTypeVars := R2 }) instHasTypeA Γ c Γ' := by
  cases h
  case init_det x xty e mty tys md h_find h_gv h_len h_rac h_expr =>
    exact CmdHasType'.init_det _ x xty e mty tys md h_find h_gv h_len
      (RigidAnnotCompat_antitone _ _ _ _ _ h_sub h_rac) h_expr
  case init_nondet x xty mty tys md h_find h_len h_rac =>
    exact CmdHasType'.init_nondet _ x xty mty tys md h_find h_len
      (RigidAnnotCompat_antitone _ _ _ _ _ h_sub h_rac)
  case set_det x mty e md h_find h_expr =>
    exact CmdHasType'.set_det _ x mty e md h_find h_expr
  case set_nondet x mty md h_find =>
    exact CmdHasType'.set_nondet _ x mty md h_find
  case assert l e md h_expr =>
    exact CmdHasType'.assert _ l e md h_expr
  case assume l e md h_expr =>
    exact CmdHasType'.assume _ l e md h_expr
  case cover l e md h_expr =>
    exact CmdHasType'.cover _ l e md h_expr

/-- `CmdExtHasTypeA` transports under a rigid-set drop. `cmd` via `CmdHasTypeA_rig_drop`;
    `call` is C-independent (annotated exprTyped ignores C; aliases carry no C). -/
theorem CmdExtHasTypeA_rig_drop (C : LContext CoreLParams) (P : Program)
    (R2 : List Lambda.TyIdentifier) (Γ : TContext Unit) (c : Command) (Γ' : TContext Unit)
    (h : @CmdExtHasType' _ C P instHasTypeA Γ c Γ')
    (h_sub : R2 ⊆ C.rigidTypeVars) :
    @CmdExtHasType' _ ({ C with rigidTypeVars := R2 }) P instHasTypeA Γ c Γ' := by
  cases h
  case cmd c0 h_cmd =>
    exact CmdExtHasType'.cmd _ Γ' c0 (CmdHasTypeA_rig_drop C R2 Γ c0 Γ' h_cmd h_sub)
  case call pname callArgs proc md σ h_find h_ia h_oa h_lhs h_inp h_out h_inout =>
    exact CmdExtHasType'.call _ pname callArgs proc md σ h_find h_ia h_oa h_lhs h_inp h_out h_inout

set_option maxHeartbeats 1000000 in
/-- General rigid-drop transport (motive over `Ca.rigidTypeVars`). -/
theorem StmtsHasTypeA_rig_drop (P : Program) (R2 : List Lambda.TyIdentifier)
    (C : LContext CoreLParams) (Γ : TContext Unit) (L : List String) (ss : List Statement)
    (C' : LContext CoreLParams) (Γ' : TContext Unit)
    (h : StmtsHasTypeA P C Γ L ss C' Γ')
    (h_sub : R2 ⊆ C.rigidTypeVars) :
    StmtsHasTypeA P ({ C with rigidTypeVars := R2 }) Γ L ss
      ({ C' with rigidTypeVars := R2 }) Γ' := by
  refine StmtsHasType'.rec
    (motive_1 := fun Ca Γa La s Ca' Γa' _ =>
      R2 ⊆ Ca.rigidTypeVars →
      StmtHasTypeA P ({ Ca with rigidTypeVars := R2 }) Γa La s ({ Ca' with rigidTypeVars := R2 }) Γa')
    (motive_2 := fun Ca Γa La ss Ca' Γa' _ =>
      R2 ⊆ Ca.rigidTypeVars →
      StmtsHasTypeA P ({ Ca with rigidTypeVars := R2 }) Γa La ss ({ Ca' with rigidTypeVars := R2 }) Γa')
    ?cmd ?block ?ite_det ?ite_nondet ?loop ?exit ?funcDecl ?typeDecl ?nil ?cons h h_sub
  case cmd =>
    intro Ca Γa Γa' La c h_cmd h_sub'
    exact StmtHasType'.cmd _ Γa Γa' La c (CmdExtHasTypeA_rig_drop Ca P R2 Γa c Γa' h_cmd h_sub')
  case block =>
    intro Ca Γa C_body Γ_body La label body md h_notin _ ih_body h_sub'
    exact StmtHasType'.block _ Γa ({ C_body with rigidTypeVars := R2 }) Γ_body La label body md
      h_notin (ih_body h_sub')
  case ite_det =>
    intro Ca Γa C_t Γ_t C_e Γ_e La cond thenb elseb md h_cond _ _ ih_t ih_e h_sub'
    exact StmtHasType'.ite_det _ Γa ({ C_t with rigidTypeVars := R2 }) Γ_t
      ({ C_e with rigidTypeVars := R2 }) Γ_e La cond thenb elseb md
      h_cond (ih_t h_sub') (ih_e h_sub')
  case ite_nondet =>
    intro Ca Γa C_t Γ_t C_e Γ_e La thenb elseb md _ _ ih_t ih_e h_sub'
    exact StmtHasType'.ite_nondet _ Γa ({ C_t with rigidTypeVars := R2 }) Γ_t
      ({ C_e with rigidTypeVars := R2 }) Γ_e La thenb elseb md (ih_t h_sub') (ih_e h_sub')
  case loop =>
    intro Ca Γa C_body Γ_body La guard measure invariants body md h_g h_m h_i _ ih_body h_sub'
    exact StmtHasType'.loop _ Γa ({ C_body with rigidTypeVars := R2 }) Γ_body La
      guard measure invariants body md h_g h_m h_i (ih_body h_sub')
  case exit =>
    intro Ca Γa La label md h_mem h_sub'
    exact StmtHasType'.exit _ Γa La label md h_mem
  case funcDecl =>
    intro Ca Γa La decl func md h_nrec h_func h_sub'
    -- `FuncHasTypeA` transports: annotated `exprTyped` ignores `C`, so the body/measure fields
    -- are definitionally reusable at the rig-swapped context.
    have h_func' : FuncHasType' LMonoTy ({ Ca with rigidTypeVars := R2 }) Γa func := {
      inputsNodup := h_func.inputsNodup
      typeArgsNodup := h_func.typeArgsNodup
      noUndeclaredVars := h_func.noUndeclaredVars
      bodyTyped := h_func.bodyTyped
      measureTyped := h_func.measureTyped }
    -- `addFactoryFunction` touches only `.functions`, so it commutes with the rig swap.
    have h_comm : ({ Ca with rigidTypeVars := R2 }).addFactoryFunction func.toLFunc
        = { Ca.addFactoryFunction func.toLFunc with rigidTypeVars := R2 } := by
      simp only [LContext.addFactoryFunction]
      split <;> rfl
    rw [← h_comm]
    exact StmtHasType'.funcDecl _ Γa La decl func md h_nrec h_func'
  case typeDecl =>
    intro Ca Ca' Γa La tc md h_add h_sub'
    -- `addKnownTypeWithError` touches only `.knownTypes`, so it commutes with the rig swap.
    have h_add' : ({ Ca with rigidTypeVars := R2 }).addKnownTypeWithError
        { name := tc.name, metadata := tc.numargs } default
        = .ok ({ Ca' with rigidTypeVars := R2 }) := by
      simp only [LContext.addKnownTypeWithError, Bind.bind, Except.bind] at h_add
      cases h_kt : Ca.knownTypes.addWithError { name := tc.name, metadata := tc.numargs } default with
      | error e => rw [h_kt] at h_add; simp only [reduceCtorEq] at h_add
      | ok kt =>
        rw [h_kt] at h_add
        simp only [Except.ok.injEq] at h_add
        simp only [LContext.addKnownTypeWithError, Bind.bind, Except.bind, h_kt]
        subst h_add
        rfl
    exact StmtHasType'.typeDecl _ ({ Ca' with rigidTypeVars := R2 }) Γa La tc md h_add'
  case nil =>
    intro Ca Γa La h_sub'
    exact StmtsHasType'.nil _ Γa La
  case cons =>
    intro Ca Cb Cc Γa Γb Γc La s ss h_s h_ss ih_s ih_ss h_sub'
    have h_rig_eq : Cb.rigidTypeVars = Ca.rigidTypeVars := StmtHasType'_rigid_eq h_s
    have h_sub_b : R2 ⊆ Cb.rigidTypeVars := by rw [h_rig_eq]; exact h_sub'
    exact StmtsHasType'.cons _ _ _ Γa Γb Γc La s ss (ih_s h_sub') (ih_ss h_sub_b)


/-! ## Weak (AliasEquiv-on-old-keys) find?-congruence for the annotated body context bridge. -/

/-- `mkOld`-prefixed identifiers ARE old-idents. Re-exports `CoreIdent.isOldIdent_mkOld`, proved in
    `Identifiers.lean` where `isOldIdent`/`mkOld` are transparent. -/
theorem isOldIdent_mkOld (n : String) : CoreIdent.isOldIdent (CoreIdent.mkOld n) = true :=
  CoreIdent.isOldIdent_mkOld n

abbrev NotOld (x : CoreIdent) : Prop := ¬ CoreIdent.isOldIdent x = true

/-- Context-agreement for the annotated bridge. `Γ₂` agrees with `Γ₁`: (1) same aliases;
    (2) exact `find?` on non-old keys; (3) on old keys, `find?` matches up to `AliasEquiv` of the
    stored monotype (both none, or both `some (forAll [] ·)` with the mtys alias-equiv). -/
structure CtxAgreeA (Γ₂ Γ₁ : TContext Unit) : Prop where
  al : Γ₂.aliases = Γ₁.aliases
  nonold : ∀ x, NotOld x → Γ₂.types.find? x = Γ₁.types.find? x
  old : ∀ x m₁, CoreIdent.isOldIdent x = true → Γ₁.types.find? x = some (.forAll [] m₁) →
    ∃ m₂, Γ₂.types.find? x = some (.forAll [] m₂) ∧ AliasEquiv Γ₁.aliases m₂ m₁

/-- `CtxAgreeA` is preserved by inserting the SAME non-old binding into both contexts (init case). -/
theorem CtxAgreeA.insert_nonold (Γ₂ Γ₁ : TContext Unit) (x : CoreIdent) (ty : LTy)
    (h : CtxAgreeA Γ₂ Γ₁) (h_x : NotOld x) :
    CtxAgreeA { Γ₂ with types := Γ₂.types.insert x ty } { Γ₁ with types := Γ₁.types.insert x ty } := by
  refine ⟨h.al, ?_, ?_⟩
  · intro y h_y
    by_cases h_xy : y = x
    · rw [h_xy]
      show (Maps.insert Γ₂.types x ty).find? x = (Maps.insert Γ₁.types x ty).find? x
      rw [Maps.find?_insert_self, Maps.find?_insert_self]
    · show (Maps.insert Γ₂.types x ty).find? y = (Maps.insert Γ₁.types x ty).find? y
      rw [Maps.find?_insert_ne _ _ _ _ h_xy, Maps.find?_insert_ne _ _ _ _ h_xy]; exact h.nonold y h_y
  · intro y m₁ h_old h_find
    -- y is old, x is non-old, so y ≠ x; the insert doesn't affect y.
    have h_yx : y ≠ x := by rintro rfl; exact h_x h_old
    show ∃ m₂, (Maps.insert Γ₂.types x ty).find? y = some (.forAll [] m₂) ∧ AliasEquiv Γ₁.aliases m₂ m₁
    rw [Maps.find?_insert_ne _ _ _ _ h_yx]
    rw [Maps.find?_insert_ne _ _ _ _ h_yx] at h_find
    exact h.old y m₁ h_old h_find

/-- Annotated `CmdHasTypeA` transports across `CtxAgreeA`. set/init targets are `NotOld` (mod/def
    vars, provably non-old), read via `.nonold`; expr premises ignore Γ; output `CtxAgreeA` restored
    via `insert_nonold` for init. -/
theorem CmdHasTypeA_find_congr_weak2
    {C : LContext CoreLParams} {Γ₁ Γ₁' : TContext Unit} {c : Cmd Expression}
    (h : @CmdHasType' LMonoTy C instHasTypeA Γ₁ c Γ₁')
    (Γ₂ : TContext Unit) (h_ag : CtxAgreeA Γ₂ Γ₁)
    (h_mod : ∀ v ∈ Cmd.modifiedVars (P := Expression) c, NotOld v)
    (h_def : ∀ v ∈ Cmd.definedVars (P := Expression) c, NotOld v) :
    ∃ Γ₂', CtxAgreeA Γ₂' Γ₁' ∧ @CmdHasType' LMonoTy C instHasTypeA Γ₂ c Γ₂' := by
  have h_expr_congr : ∀ (Γa Γb : TContext Unit) (e : Expression.Expr) (t : LMonoTy),
      instHasTypeA.exprTyped C Γa e t → instHasTypeA.exprTyped C Γb e t :=
    fun _ _ _ _ h_e => h_e
  cases h
  case init_det x xty e mty tys md h_find h_notin h_len h_rigid h_e =>
    have h_x : NotOld x := h_def x (by simp [Cmd.definedVars])
    refine ⟨{ Γ₂ with types := Γ₂.types.insert x (.forAll [] mty) }, h_ag.insert_nonold Γ₂ Γ₁ x _ h_x, ?_⟩
    exact CmdHasType'.init_det Γ₂ x xty e mty tys md (by rw [h_ag.nonold x h_x]; exact h_find)
      h_notin h_len (by rw [h_ag.al]; exact h_rigid) (h_expr_congr Γ₁ Γ₂ e _ h_e)
  case init_nondet x xty mty tys md h_find h_len h_rigid =>
    have h_x : NotOld x := h_def x (by simp [Cmd.definedVars])
    refine ⟨{ Γ₂ with types := Γ₂.types.insert x (.forAll [] mty) }, h_ag.insert_nonold Γ₂ Γ₁ x _ h_x, ?_⟩
    exact CmdHasType'.init_nondet Γ₂ x xty mty tys md (by rw [h_ag.nonold x h_x]; exact h_find)
      h_len (by rw [h_ag.al]; exact h_rigid)
  case set_det x mty e md h_find h_e =>
    have h_x : NotOld x := h_mod x (by simp [Cmd.modifiedVars])
    exact ⟨Γ₂, h_ag, CmdHasType'.set_det Γ₂ x mty e md (by rw [h_ag.nonold x h_x]; exact h_find)
      (h_expr_congr Γ₁ Γ₂ e _ h_e)⟩
  case set_nondet x mty md h_find =>
    have h_x : NotOld x := h_mod x (by simp [Cmd.modifiedVars])
    exact ⟨Γ₂, h_ag, CmdHasType'.set_nondet Γ₂ x mty md (by rw [h_ag.nonold x h_x]; exact h_find)⟩
  case assert l e md h_e => exact ⟨Γ₂, h_ag, CmdHasType'.assert Γ₂ l e md (h_expr_congr Γ₁ Γ₂ e _ h_e)⟩
  case assume l e md h_e => exact ⟨Γ₂, h_ag, CmdHasType'.assume Γ₂ l e md (h_expr_congr Γ₁ Γ₂ e _ h_e)⟩
  case cover l e md h_e => exact ⟨Γ₂, h_ag, CmdHasType'.cover Γ₂ l e md (h_expr_congr Γ₁ Γ₂ e _ h_e)⟩

/-- Annotated `CmdExtHasTypeA` transports across `CtxAgreeA`. `cmd` delegates; `call` LHS/output read
    non-old keys (modifiedVars); the `call` bare-fvar INPUT may read an OLD key — there we re-pick the
    stored mty from `Γ₂` and transport `AliasEquiv` by `.trans`. -/
theorem CmdExtHasTypeA_find_congr_weak2 {P : Program}
    {C : LContext CoreLParams} {Γ₁ Γ₁' : TContext Unit} {c : Command}
    (h : @CmdExtHasType' _ C P instHasTypeA Γ₁ c Γ₁')
    (Γ₂ : TContext Unit) (h_ag : CtxAgreeA Γ₂ Γ₁)
    (h_mod : ∀ v ∈ Command.modifiedVars c, NotOld v)
    (h_def : ∀ v ∈ Command.definedVars c, NotOld v) :
    ∃ Γ₂', CtxAgreeA Γ₂' Γ₁' ∧ @CmdExtHasType' _ C P instHasTypeA Γ₂ c Γ₂' := by
  cases h
  case cmd c0 h_cmd =>
    have h_mod0 : ∀ v ∈ Cmd.modifiedVars (P := Expression) c0, NotOld v := by
      intro v hv; exact h_mod v (by simp only [Command.modifiedVars]; exact hv)
    have h_def0 : ∀ v ∈ Cmd.definedVars (P := Expression) c0, NotOld v := by
      intro v hv; exact h_def v (by simp only [Command.definedVars]; exact hv)
    obtain ⟨Γ₂', h_ag', h_cmd'⟩ := CmdHasTypeA_find_congr_weak2 h_cmd Γ₂ h_ag h_mod0 h_def0
    exact ⟨Γ₂', h_ag', CmdExtHasType'.cmd Γ₂ Γ₂' c0 h_cmd'⟩
  case call pname callArgs proc md σ h_find h_ia h_oa h_lhs h_inp h_out h_inout =>
    have h_lhs_notold : ∀ v ∈ CallArg.getLhs callArgs, NotOld v := by
      intro v hv; exact h_mod v (by simp only [Command.modifiedVars]; exact hv)
    refine ⟨Γ₂, h_ag, ?_⟩
    refine CmdExtHasType'.call Γ₂ pname callArgs proc md σ h_find h_ia h_oa ?_ ?_ ?_ h_inout
    · -- all lhs vars exist (non-old)
      intro v hv; rw [h_ag.nonold v (h_lhs_notold v hv)]; exact h_lhs v hv
    · -- input positions: bare-fvar reads find? (may be old ⟹ re-pick + AliasEquiv.trans); else exprTyped
      intro i hi hj
      obtain ⟨mty, h_ae, h_match⟩ := h_inp i hi hj
      revert h_match
      split
      · rename_i x h_arg_eq
        intro h_match  -- h_match : Γ₁.types.find? x = some (.forAll [] mty)
        by_cases h_xold : CoreIdent.isOldIdent x = true
        · -- old key: re-pick m₂ from Γ₂, AliasEquiv m₂ mty; then AliasEquiv m₂ formal by trans.
          obtain ⟨m₂, h_find₂, h_aem⟩ := h_ag.old x mty h_xold h_match
          refine ⟨m₂, ?_, ?_⟩
          · rw [h_ag.al]; exact AliasEquiv.trans h_aem h_ae
          · exact h_find₂
        · -- non-old key: exact agreement, same mty.
          have h_xn : NotOld x := h_xold
          refine ⟨mty, by rw [h_ag.al]; exact h_ae, ?_⟩
          rw [h_ag.nonold x h_xn]; exact h_match
      · rename_i e h_ne
        intro h_match
        exact ⟨mty, by rw [h_ag.al]; exact h_ae, h_match⟩
    · -- lhs types (non-old)
      intro i hi hj
      obtain ⟨mty, h_ae, h_find_lhs⟩ := h_out i hi hj
      refine ⟨mty, by rw [h_ag.al]; exact h_ae, ?_⟩
      rw [h_ag.nonold _ (h_lhs_notold _ (List.getElem_mem hi))]; exact h_find_lhs

/-- All modified/defined vars of a statement are `NotOld` (recursive over block/ite/loop bodies).
    Discharged at the call site from `modRights` (mod ⊆ outputs++defined, all non-old). -/
def StmtModDefNotOld (s : Statement) : Prop :=
  match s with
  | .cmd c => (∀ v ∈ Command.modifiedVars c, NotOld v) ∧ (∀ v ∈ Command.definedVars c, NotOld v)
  | .block _ b _ => ∀ s ∈ b, StmtModDefNotOld s
  | .ite _ t e _ => (∀ s ∈ t, StmtModDefNotOld s) ∧ (∀ s ∈ e, StmtModDefNotOld s)
  | .loop _ _ _ b _ => ∀ s ∈ b, StmtModDefNotOld s
  | _ => True

abbrev StmtsModDefNotOld (ss : List Statement) : Prop := ∀ s ∈ ss, StmtModDefNotOld s

/-- `StmtModDefNotOld` on a `block` unfolds to the property over the body. -/
theorem StmtModDefNotOld_block (l b md) :
    StmtModDefNotOld (.block l b md) = ∀ s ∈ b, StmtModDefNotOld s := by simp only [StmtModDefNotOld]

/-- `StmtModDefNotOld` on an `ite` unfolds to the property over both branches. -/
theorem StmtModDefNotOld_ite (cnd t e md) :
    StmtModDefNotOld (.ite cnd t e md)
      = ((∀ s ∈ t, StmtModDefNotOld s) ∧ (∀ s ∈ e, StmtModDefNotOld s)) := by
  simp only [StmtModDefNotOld]

/-- `StmtModDefNotOld` on a `loop` unfolds to the property over the body. -/
theorem StmtModDefNotOld_loop (g m i b md) :
    StmtModDefNotOld (.loop g m i b md) = ∀ s ∈ b, StmtModDefNotOld s := by simp only [StmtModDefNotOld]

/-- `StmtModDefNotOld` on a `cmd` unfolds to `NotOld` of its modified/defined vars. -/
theorem StmtModDefNotOld_cmd (c) :
    StmtModDefNotOld (.cmd c)
      = ((∀ v ∈ Command.modifiedVars c, NotOld v) ∧ (∀ v ∈ Command.definedVars c, NotOld v)) := by
  simp only [StmtModDefNotOld]

set_option maxHeartbeats 1000000 in
/-- `StmtsHasTypeA` transfers along a `CtxAgreeA`-related context, given every modified/defined
    var is `NotOld` (so the `old`-key discrepancies between the contexts are irrelevant). -/
theorem StmtsHasTypeA_find_congr_weak2 {P : Program}
    {C C' : LContext CoreLParams} {Γ₁ Γ₁' : TContext Unit} {L : List String} {ss : List Statement}
    (h : StmtsHasTypeA P C Γ₁ L ss C' Γ₁')
    (h_mdno : StmtsModDefNotOld ss) :
    ∀ (Γ₂ : TContext Unit), CtxAgreeA Γ₂ Γ₁ →
      ∃ Γ₂', CtxAgreeA Γ₂' Γ₁' ∧ StmtsHasTypeA P C Γ₂ L ss C' Γ₂' := by
  have h_expr_congr : ∀ (Γa Γb : TContext Unit) (Cx : LContext CoreLParams)
      (e : Expression.Expr) (t : LMonoTy),
      instHasTypeA.exprTyped Cx Γa e t → instHasTypeA.exprTyped Cx Γb e t :=
    fun _ _ _ _ _ h_e => h_e
  refine StmtsHasType'.rec
    (motive_1 := fun Ca Γa La s Ca' Γa' _ =>
      StmtModDefNotOld s → ∀ Γ₂, CtxAgreeA Γ₂ Γa →
        ∃ Γ₂', CtxAgreeA Γ₂' Γa' ∧ StmtHasTypeA P Ca Γ₂ La s Ca' Γ₂')
    (motive_2 := fun Ca Γa La ss Ca' Γa' _ =>
      StmtsModDefNotOld ss → ∀ Γ₂, CtxAgreeA Γ₂ Γa →
        ∃ Γ₂', CtxAgreeA Γ₂' Γa' ∧ StmtsHasTypeA P Ca Γ₂ La ss Ca' Γ₂')
    ?cmd ?block ?ite_det ?ite_nondet ?loop ?exit ?funcDecl ?typeDecl ?nil ?cons h h_mdno
  case cmd =>
    intro Ca Γa Γa' La c h_cmd h_md Γ₂ h_ag
    rw [StmtModDefNotOld_cmd] at h_md
    obtain ⟨Γ₂', h_ag', h_cmd'⟩ := CmdExtHasTypeA_find_congr_weak2 h_cmd Γ₂ h_ag h_md.1 h_md.2
    exact ⟨Γ₂', h_ag', StmtHasType'.cmd Ca Γ₂ Γ₂' La c h_cmd'⟩
  case block =>
    intro Ca Γa C_body Γ_body La label body md h_notin _ ih h_md Γ₂ h_ag
    rw [StmtModDefNotOld_block] at h_md
    obtain ⟨Γ_body', _, h_body'⟩ := ih h_md Γ₂ h_ag
    exact ⟨Γ₂, h_ag, StmtHasType'.block Ca Γ₂ C_body Γ_body' La label body md h_notin h_body'⟩
  case ite_det =>
    intro Ca Γa C_t Γ_t C_e Γ_e La cond t e md h_c _ _ ih_t ih_e h_md Γ₂ h_ag
    rw [StmtModDefNotOld_ite] at h_md
    obtain ⟨Γ_t', _, h_t'⟩ := ih_t h_md.1 Γ₂ h_ag
    obtain ⟨Γ_e', _, h_e'⟩ := ih_e h_md.2 Γ₂ h_ag
    exact ⟨Γ₂, h_ag, StmtHasType'.ite_det Ca Γ₂ C_t Γ_t' C_e Γ_e' La cond t e md
      (h_expr_congr Γa Γ₂ Ca cond _ h_c) h_t' h_e'⟩
  case ite_nondet =>
    intro Ca Γa C_t Γ_t C_e Γ_e La t e md _ _ ih_t ih_e h_md Γ₂ h_ag
    rw [StmtModDefNotOld_ite] at h_md
    obtain ⟨Γ_t', _, h_t'⟩ := ih_t h_md.1 Γ₂ h_ag
    obtain ⟨Γ_e', _, h_e'⟩ := ih_e h_md.2 Γ₂ h_ag
    exact ⟨Γ₂, h_ag, StmtHasType'.ite_nondet Ca Γ₂ C_t Γ_t' C_e Γ_e' La t e md h_t' h_e'⟩
  case loop =>
    intro Ca Γa C_body Γ_body La g m inv body md h_g h_m h_i _ ih h_md Γ₂ h_ag
    rw [StmtModDefNotOld_loop] at h_md
    obtain ⟨Γ_body', _, h_body'⟩ := ih h_md Γ₂ h_ag
    exact ⟨Γ₂, h_ag, StmtHasType'.loop Ca Γ₂ C_body Γ_body' La g m inv body md
      (fun gg h_gd => h_expr_congr Γa Γ₂ Ca gg _ (h_g gg h_gd))
      (fun mm h_md' => h_expr_congr Γa Γ₂ Ca mm _ (h_m mm h_md'))
      (fun p h_pm => h_expr_congr Γa Γ₂ Ca p.2 _ (h_i p h_pm)) h_body'⟩
  case exit =>
    intro Ca Γa La label md h_mem _ Γ₂ h_ag
    exact ⟨Γ₂, h_ag, StmtHasType'.exit Ca Γ₂ La label md h_mem⟩
  case funcDecl =>
    intro Ca Γa La decl func md h_nrec h_func _ Γ₂ h_ag
    have h_func₂ : FuncHasType' LMonoTy Ca Γ₂ func := {
      inputsNodup := h_func.inputsNodup, typeArgsNodup := h_func.typeArgsNodup
      noUndeclaredVars := h_func.noUndeclaredVars
      bodyTyped := fun body h_b => h_expr_congr _ Γ₂ Ca body _ (h_func.bodyTyped body h_b)
      measureTyped := fun mm h_m h_nv => h_expr_congr _ Γ₂ Ca mm _ (h_func.measureTyped mm h_m h_nv) }
    exact ⟨Γ₂, h_ag, StmtHasType'.funcDecl Ca Γ₂ La decl func md h_nrec h_func₂⟩
  case typeDecl =>
    intro Ca Ca' Γa La tc md h_add _ Γ₂ h_ag
    exact ⟨Γ₂, h_ag, StmtHasType'.typeDecl Ca Ca' Γ₂ La tc md h_add⟩
  case nil => intro Ca Γa La _ Γ₂ h_ag; exact ⟨Γ₂, h_ag, StmtsHasType'.nil Ca Γ₂ La⟩
  case cons =>
    intro Ca Cb Cc Γa Γb Γc La s ss _ _ ih_s ih_ss h_md Γ₂ h_ag
    have h_s : StmtModDefNotOld s := h_md s List.mem_cons_self
    have h_ss : StmtsModDefNotOld ss := fun s' hs' => h_md s' (List.mem_cons_of_mem s hs')
    obtain ⟨Γb', h_agb, h_s'⟩ := ih_s h_s Γ₂ h_ag
    obtain ⟨Γc', h_agc, h_ss'⟩ := ih_ss h_ss Γb' h_agb
    exact ⟨Γc', h_agc, StmtsHasType'.cons Ca Cb Cc Γ₂ Γb' Γc' La s ss h_s' h_ss'⟩

/-- Structural core for the newest-scope agreement feeding `body_context_ctxAgreeA`. Two newest
    scopes share an IO prefix `ioScope` (inputs++outputs, values all `forAll [] _`) and differ only
    in their old tails `oldA`/`oldB`, which are per-key `AliasEquiv`-related. Then the full scopes
    agree exactly on NotOld keys and up to `AliasEquiv` on old keys. -/
theorem newest_scope_agree
    (aliases : List TypeAlias) (ioScope oldA oldB : Map CoreIdent LTy)
    (h_io_forall : ∀ x m, ioScope.find? x = some m → ∃ mty, m = .forAll [] mty)
    (h_oldA_notold_none : ∀ x, NotOld x → oldA.find? x = none)
    (h_oldB_notold_none : ∀ x, NotOld x → oldB.find? x = none)
    (h_old_agree : ∀ x, CoreIdent.isOldIdent x = true →
      (oldA.find? x = none ∧ oldB.find? x = none)
      ∨ ∃ mA mB, oldA.find? x = some (.forAll [] mA) ∧ oldB.find? x = some (.forAll [] mB)
          ∧ AliasEquiv aliases mA mB) :
    (∀ x, NotOld x → (ioScope ++ oldA).find? x = (ioScope ++ oldB).find? x)
    ∧ (∀ x, CoreIdent.isOldIdent x = true →
        ((ioScope ++ oldA).find? x = none ∧ (ioScope ++ oldB).find? x = none)
        ∨ ∃ mA mB, (ioScope ++ oldA).find? x = some (.forAll [] mA)
            ∧ (ioScope ++ oldB).find? x = some (.forAll [] mB) ∧ AliasEquiv aliases mA mB) := by
  refine ⟨?_, ?_⟩
  · -- nonold: io part decides (oldA/oldB miss); the io part is shared.
    intro x h_x
    rw [Map.find?_map_append, Map.find?_map_append, h_oldA_notold_none x h_x, h_oldB_notold_none x h_x]
  · -- old: io part decides if it hits (exact agreement, both sides same io value); else oldA/oldB.
    intro x h_x
    rw [Map.find?_map_append, Map.find?_map_append]
    cases h_io : ioScope.find? x with
    | some v =>
      simp only
      obtain ⟨mty, h_mty⟩ := h_io_forall x v h_io
      subst h_mty
      exact Or.inr ⟨mty, mty, rfl, rfl, AliasEquiv.refl⟩
    | none =>
      simp only
      exact h_old_agree x h_x

/-- A scope built by `mkOld`-keying a parameter list contains only old-idents, so `find?` at a
    NotOld key misses. Used to show the spec/checker old-scopes have no non-old keys. -/
theorem old_map_notold_none (oldParams : List (CoreIdent × LMonoTy)) (x : CoreIdent)
    (h_x : ¬ CoreIdent.isOldIdent x = true) :
    Map.find? (oldParams.map (fun p => (CoreIdent.mkOld p.1.name, LTy.forAll [] p.2))) x = none := by
  apply Map.find?_none_of_not_mem_keys'
  rw [Map.keys_eq_map_fst, List.map_map, List.mem_map]
  rintro ⟨p, hp, h_key⟩
  exact h_x (h_key ▸ isOldIdent_mkOld p.1.name)

mutual
/-- `StmtModDefNotOld` follows from every modified/defined var of `s` being `NotOld`. -/
theorem StmtModDefNotOld_of_vars (s : Statement)
    (h_m : ∀ v ∈ Stmt.modifiedVars (P := Expression) (C := Command) s, NotOld v)
    (h_d : ∀ v ∈ Stmt.definedVars (P := Expression) (C := Command) s false, NotOld v) :
    StmtModDefNotOld s := by
  cases s with
  | cmd c =>
    rw [StmtModDefNotOld_cmd]
    exact ⟨fun v hv => h_m v (by rw [Stmt.modifiedVars.eq_1]; exact hv),
           fun v hv => h_d v (by rw [Stmt.definedVars.eq_1]; exact hv)⟩
  | block l bss md =>
    rw [StmtModDefNotOld_block]
    apply StmtsModDefNotOld_of_vars
    · exact fun v hv => h_m v (by rw [Stmt.modifiedVars.eq_3]; exact hv)
    · exact fun v hv => h_d v (by rw [Stmt.definedVars.eq_2]; simpa using hv)
  | ite cnd t e md =>
    rw [StmtModDefNotOld_ite]
    refine ⟨?_, ?_⟩
    · apply StmtsModDefNotOld_of_vars
      · exact fun v hv => h_m v (by rw [Stmt.modifiedVars.eq_4]; exact List.mem_append_left _ hv)
      · refine fun v hv => h_d v ?_
        rw [Stmt.definedVars.eq_3]; simp only [Bool.false_eq_true, reduceIte]
        exact List.mem_append_left _ hv
    · apply StmtsModDefNotOld_of_vars
      · exact fun v hv => h_m v (by rw [Stmt.modifiedVars.eq_4]; exact List.mem_append_right _ hv)
      · refine fun v hv => h_d v ?_
        rw [Stmt.definedVars.eq_3]; simp only [Bool.false_eq_true, reduceIte]
        exact List.mem_append_right _ hv
  | loop g m i bss md =>
    rw [StmtModDefNotOld_loop]
    apply StmtsModDefNotOld_of_vars
    · exact fun v hv => h_m v (by rw [Stmt.modifiedVars.eq_5]; exact hv)
    · exact fun v hv => h_d v (by rw [Stmt.definedVars.eq_4]; simpa using hv)
  | exit l md => simp only [StmtModDefNotOld]
  | funcDecl d f => simp only [StmtModDefNotOld]
  | typeDecl t md => simp only [StmtModDefNotOld]

/-- Block form of `StmtModDefNotOld_of_vars`. -/
theorem StmtsModDefNotOld_of_vars (ss : List Statement)
    (h_m : ∀ v ∈ Block.modifiedVars (P := Expression) (C := Command) ss, NotOld v)
    (h_d : ∀ v ∈ Block.definedVars (P := Expression) (C := Command) ss false, NotOld v) :
    StmtsModDefNotOld ss := by
  cases ss with
  | nil => intro s hs; simp at hs
  | cons s rest =>
    intro s' hs'
    rw [List.mem_cons] at hs'
    rcases hs' with h_eq | h_rest
    · subst h_eq
      apply StmtModDefNotOld_of_vars
      · exact fun v hv => h_m v (by rw [Block.modifiedVars.eq_2]; exact List.mem_append_left _ hv)
      · exact fun v hv => h_d v (by rw [Block.definedVars.eq_2]; exact List.mem_append_left _ hv)
    · exact StmtsModDefNotOld_of_vars rest
        (fun v hv => h_m v (by rw [Block.modifiedVars.eq_2]; exact List.mem_append_right _ hv))
        (fun v hv => h_d v (by rw [Block.definedVars.eq_2]; exact List.mem_append_right _ hv))
        s' h_rest
end

/-- The checker's reserved-`old`-prefix write guard (the first `if` in `checkModificationRights`):
    reaching `.ok` means `((modifiedVars ++ definedVars).filter isOldIdent).isEmpty`, so every
    modified/defined var of the INPUT body is `NotOld`. -/
theorem Procedure.typeCheck_modDefNotOld (C : LContext CoreLParams) (Env : TEnv Unit)
    (P : Program) (proc proc' : Procedure) (Env' : TEnv Unit) (md : MetaData Expression)
    (h : Procedure.typeCheck C Env P proc md = .ok (proc', Env')) :
    (∀ v ∈ HasVarsImp.modifiedVars (P := Expression) proc.body, NotOld v) ∧
    (∀ v ∈ HasVarsImp.definedVars (P := Expression) proc.body false, NotOld v) := by
  unfold Procedure.typeCheck at h
  simp only [Procedure.checkNoDuplicates,
    Procedure.checkModificationRights, Bind.bind, Except.bind, pure, Except.pure] at h
  split at h
  · simp only [reduceCtorEq] at h
  · elim_err h with h_ta
    · split at h
      · simp only [reduceCtorEq] at h
      · rename_i _ _ h_mr
        split at h_mr
        · simp only [reduceCtorEq] at h_mr
        · rename_i h_old_neg
          have h_filter_empty : (List.filter (fun v => CoreIdent.isOldIdent v)
              ((HasVarsImp.modifiedVars (P := Expression) proc.body).eraseDups ++
               (HasVarsImp.definedVars (P := Expression) proc.body false).eraseDups)) = [] := by
            rw [← List.isEmpty_iff]
            simpa using h_old_neg
          rw [List.filter_eq_nil_iff] at h_filter_empty
          -- Every var in the eraseDups'd append is NotOld.
          have h_notold : ∀ w, w ∈ (HasVarsImp.modifiedVars (P := Expression) proc.body).eraseDups ++
              (HasVarsImp.definedVars (P := Expression) proc.body false).eraseDups → NotOld w := by
            intro w hw
            have h_not := h_filter_empty w hw
            simpa only [Bool.not_eq_true] using h_not
          refine ⟨?_, ?_⟩
          · intro v hv
            exact h_notold v (List.mem_append_left _ (List.mem_eraseDups.mpr hv))
          · intro v hv
            exact h_notold v (List.mem_append_right _ (List.mem_eraseDups.mpr hv))

/-- The `CtxAgreeA` (annotated) variant of `body_context_find_agree`: the two body contexts agree
    exactly on non-old keys and up to `AliasEquiv` on old keys. -/
theorem body_context_ctxAgreeA
    (Env' : TContext Unit) (proc' : Procedure) (bodyΓ : TContext Unit)
    (S' userSubst : Subst) (ambient : Maps CoreIdent LTy) (freshScope declScope : Map CoreIdent LTy)
    (h_pbc : (procBodyContext Env' proc').types = declScope :: TContext.types.subst ambient S')
    (h_bodyΓ_types : bodyΓ.types
      = TContext.types.subst.go S' freshScope :: TContext.types.subst ambient S')
    (h_al : (procBodyContext Env' proc').aliases = (TContext.subst bodyΓ userSubst).aliases)
    -- Non-old keys agree exactly on the newest scopes.
    (h_newest_nonold : ∀ x, NotOld x →
      declScope.find? x
        = (TContext.types.subst.go userSubst (TContext.types.subst.go S' freshScope)).find? x)
    -- Old keys agree up to `AliasEquiv` (both none, or both `some (forAll [] ·)` with equiv mtys).
    (h_newest_old : ∀ x, CoreIdent.isOldIdent x = true →
      (declScope.find? x = none
        ∧ (TContext.types.subst.go userSubst (TContext.types.subst.go S' freshScope)).find? x = none)
      ∨ ∃ m₂ m₁, declScope.find? x = some (.forAll [] m₂)
          ∧ (TContext.types.subst.go userSubst (TContext.types.subst.go S' freshScope)).find? x
              = some (.forAll [] m₁)
          ∧ AliasEquiv (procBodyContext Env' proc').aliases m₂ m₁)
    (h_closed : ∀ ty ∈ Maps.values ambient, LTy.freeVars ty = []) :
    CtxAgreeA (procBodyContext Env' proc') (TContext.subst bodyΓ userSubst) := by
  have h_rhs : (TContext.subst bodyΓ userSubst).types
      = TContext.types.subst.go userSubst (TContext.types.subst.go S' freshScope)
        :: TContext.types.subst (TContext.types.subst ambient S') userSubst := by
    show TContext.types.subst bodyΓ.types userSubst = _
    rw [h_bodyΓ_types]; simp only [TContext.types.subst]
  have h_S'_fix : TContext.types.subst ambient S' = ambient := subst_fix_closed S' ambient h_closed
  have h_us_fix : TContext.types.subst ambient userSubst = ambient := subst_fix_closed userSubst ambient h_closed
  have h_single : ∀ (m : Map CoreIdent LTy) (y), Maps.find? [m] y = m.find? y := by
    intro m y; simp only [Maps.find?]; cases m.find? y <;> rfl
  refine ⟨h_al, ?_, ?_⟩
  · -- nonold
    intro x h_x
    rw [h_pbc, h_rhs, h_S'_fix, h_us_fix]
    show Maps.find? (declScope :: ambient) x
      = Maps.find? (TContext.types.subst.go userSubst (TContext.types.subst.go S' freshScope) :: ambient) x
    simp only [Maps.find?, h_newest_nonold x h_x]
  · -- old
    intro x m₁ h_old h_find
    rw [h_rhs, h_S'_fix, h_us_fix] at h_find
    rw [h_pbc, h_S'_fix]
    let newestRHS := TContext.types.subst.go userSubst (TContext.types.subst.go S' freshScope)
    show ∃ m₂, Maps.find? (declScope :: ambient) x = some (.forAll [] m₂)
      ∧ AliasEquiv (TContext.subst bodyΓ userSubst).aliases m₂ m₁
    -- `find? (head :: ambient) x` = if head hits, head; else ambient. Case on checker head.
    have h_find' : Maps.find? (newestRHS :: ambient) x = some (.forAll [] m₁) := h_find
    rw [Maps.find?] at h_find'
    rcases h_newest_old x h_old with ⟨h_dnone, h_hnone⟩ | ⟨m₂, m₁', h_dsome, h_hsome, h_ae⟩
    · -- both newest heads miss ⟹ both fall through to the same ambient.
      rw [h_hnone] at h_find'
      refine ⟨m₁, ?_, ?_⟩
      · rw [Maps.find?, h_dnone]; exact h_find'
      · exact .refl
    · -- both hit; checker gives m₁' = m₁ (from h_find'), spec gives m₂ AliasEquiv m₁'.
      rw [h_hsome] at h_find'
      have h_m1 : m₁' = m₁ := by injection h_find' with h_eq; injection h_eq
      subst h_m1
      refine ⟨m₂, ?_, ?_⟩
      · rw [Maps.find?, h_dsome]
      · rw [← h_al]; exact h_ae

/-- Every modified/defined variable of the checker-output body is `NotOld` (from the
    reserved-`old`-prefix write guard in `checkModificationRights`). -/
theorem Procedure.typeCheck_bodyModDefNotOld (C : LContext CoreLParams) (Env : TEnv Unit)
    (P : Program) (proc proc' : Procedure) (Env' : TEnv Unit) (md : MetaData Expression)
    (h : Procedure.typeCheck C Env P proc md = .ok (proc', Env'))
    (h_wf : TEnvWF (T := CoreLParams) Env)
    (h_fwf : FactoryWF C.functions)
    (h_resolved : TContext.AliasesResolved Env.context)
    (h_mono : ContextMono Env.context)
    (h_closed : CalledProcsClosed P) :
    (∀ v ∈ HasVarsImp.modifiedVars (P := Expression) proc'.body, NotOld v) ∧
    (∀ v ∈ HasVarsImp.definedVars (P := Expression) proc'.body false, NotOld v) := by
  unfold Procedure.typeCheck at h
  simp only [Procedure.checkNoDuplicates,
    Procedure.checkModificationRights, Bind.bind, Except.bind, pure, Except.pure] at h
  split at h
  · simp only [reduceCtorEq] at h
  · elim_err h with h_ta
    · split at h
      · simp only [reduceCtorEq] at h
      · rename_i _ _ h_mr
        split at h_mr
        · simp only [reduceCtorEq] at h_mr
        · rename_i h_oldempty_neg
          have h_old_empty : (List.filter (fun v => CoreIdent.isOldIdent v)
              ((HasVarsImp.modifiedVars (P := Expression) proc.body).eraseDups ++
               (HasVarsImp.definedVars (P := Expression) proc.body false).eraseDups)) = [] := by
            rw [← List.isEmpty_iff]
            simpa using h_oldempty_neg
          rw [List.filter_eq_nil_iff] at h_old_empty
          have h_notold : ∀ w, (w ∈ HasVarsImp.modifiedVars (P := Expression) proc.body ∨
              w ∈ HasVarsImp.definedVars (P := Expression) proc.body false) → NotOld w := by
            intro w hw
            apply h_old_empty
            rw [List.mem_append]
            rcases hw with h | h
            · exact Or.inl (List.mem_eraseDups.mpr h)
            · exact Or.inr (List.mem_eraseDups.mpr h)
          split at h_mr
          · simp only [reduceCtorEq] at h_mr
          · rename_i _
            elim_err h
            rename_i v_setup h_setup
            elim_err h with v_pre h_pre
            elim_err h
            rename_i v_out h_out
            elim_err h with v_post h_post
            split at h
            · rename_i ss h_body
              elim_err h with v_unify h_unify
              split at h
              · simp at h
              rename_i h_rigid_none
              elim_err h with v_body h_stc
              injection h with h_pair
              injection h_pair with h_proc _
              subst h_proc
              have h_tc := Lambda.Except.mapError_ok_h' h_stc
              have h_ra := Lambda.Except.mapError_ok_h' h_out
              have h_penv := postEnv_wf C Env proc _ v_setup v_pre v_out h_ta h_setup h_pre h_ra
                h_wf h_fwf h_resolved
              have h_E4mono := E4_ContextMono C Env proc _ v_setup v_pre v_out h_setup h_pre h_ra
                h_wf h_fwf h_mono
              have h_cs_fresh := procBody_cs_fresh C Env proc _ v_setup v_pre v_out v_post
                h_ta h_setup h_pre h_ra h_post h_wf h_fwf h_resolved
              have h_unify' := Lambda.Except.mapError_ok_h' h_unify
              have h_bwf := procBodyEnv_wf C _ proc v_post _ v_unify h_post h_unify' h_cs_fresh
                h_penv.1 h_penv.2.1 h_E4mono h_penv.2.2 h_fwf
              have h_rigid_inv : ∀ w, w ∈ (List.filterMap
                  (fun x => match x.snd with | LMonoTy.ftvar id => some id | x => none)
                  (List.flatten v_setup.2.snd)) →
                LMonoTy.subst (v_post.snd.updateSubst v_unify).stateSubstInfo.subst (.ftvar w) = .ftvar w := by
                intro w hw
                have h_all := List.find?_eq_none.mp h_rigid_none w hw
                simpa only [bne_iff_ne, ne_eq, Decidable.not_not] using h_all
              obtain ⟨hb_wf, hb_ne, hb_mono, _⟩ := h_bwf
              obtain ⟨h_bm, h_bd⟩ :=
                statement_typeCheck_vars
                  { functions := C.functions, datatypes := C.datatypes, knownTypes := C.knownTypes,
                    idents := C.idents,
                    rigidTypeVars := List.filterMap
                      (fun x => match x.snd with | LMonoTy.ftvar id => some id | x => none)
                      (List.flatten v_setup.2.snd) }
                  (v_post.snd.updateSubst v_unify) P (some proc) ss v_body.fst v_body.snd
                  hb_wf h_fwf hb_ne hb_mono h_rigid_inv h_closed h_tc
              refine ⟨?_, ?_⟩
              · intro v hv
                simp only [HasVarsImp.modifiedVars, subst_block_modifiedVars, h_bm] at hv
                exact h_notold v (Or.inl (by rw [h_body]; exact hv))
              · intro v hv
                simp only [HasVarsImp.definedVars, subst_block_definedVars, h_bd] at hv
                exact h_notold v (Or.inr (by rw [h_body]; exact hv))
            · simp at h

/-- Annotated `bodyTyped`: the output body is well-typed as a statement list under the
    annotated judgment. Delegates to `Statement.typeCheck_annotated_sound` + a context
    bridge (weak2 `CtxAgreeA` congruence). -/
theorem Procedure.typeCheck_bodyTyped_annotated (C : LContext CoreLParams) (Env : TEnv Unit)
    (P : Program) (proc proc' : Procedure) (Env' : TEnv Unit) (md : MetaData Expression)
    (h : Procedure.typeCheck C Env P proc md = .ok (proc', Env'))
    (h_wf : TEnvWF (T := CoreLParams) Env)
    (h_fwf : FactoryWF C.functions)
    (h_resolved : TContext.AliasesResolved Env.context)
    (h_mono : ContextMono Env.context)
    -- Ambient bindings are closed, so both body substitutions fix them and the context tails
    -- agree. Vacuous at the `Program` level (Core has no global variable declarations).
    (h_ambient_closed : ∀ ty, ty ∈ Maps.values Env.context.types → LTy.freeVars ty = [])
    -- The ambient carries no rigid type vars, so the body derivation transports back to `C`.
    -- Vacuous at the `Program` level (`C.rigidTypeVars` is empty there).
    (h_ambient_no_rigid : C.rigidTypeVars = [])
    (h_closed : CalledProcsClosed P) :
    ProcBodyHasType' LMonoTy P C (procBodyContext Env'.context proc') proc'.body := by
  -- Extract the body's `NotOld` mod/def facts before peeling `h` (which destroys the equation).
  have h_mdno_facts := Procedure.typeCheck_bodyModDefNotOld C Env P proc proc' Env' md h
    h_wf h_fwf h_resolved h_mono h_closed
  simp only [Procedure.typeCheck, Procedure.checkNoDuplicates, bind, Except.bind,
    pure, Except.pure] at h
  split at h
  · simp at h
  rename_i h_in_guard
  elim_err h with h_ta
  elim_err h
  elim_err h
  rename_i v_setup h_setup
  elim_err h
  rename_i v_pre h_pre
  elim_err h
  rename_i v_out h_out
  elim_err h
  rename_i v_post h_post
  split at h
  · rename_i ss h_body
    elim_err h
    rename_i v_unify h_unify
    split at h
    · simp at h
    rename_i h_rigid_none
    elim_err h
    rename_i v_body h_stc
    -- The guard's `none` branch gives `rigid_inv` directly (as in `Function.typeCheck`).
    have h_rigid_inv : ∀ v, v ∈ (List.filterMap
          (fun x => match x.snd with | LMonoTy.ftvar id => some id | x => none)
          (List.flatten v_setup.2.snd)) →
        LMonoTy.subst (v_post.snd.updateSubst v_unify).stateSubstInfo.subst (.ftvar v) = .ftvar v := by
      intro v hv
      have h_all := List.find?_eq_none.mp h_rigid_none v hv
      simpa only [bne_iff_ne, ne_eq, Decidable.not_not] using h_all
    injection h with h_pair
    injection h_pair with h_proc h_env'
    subst h_proc
    have h_stc' := Core.WF.Except.mapError_ok h_stc
    have h_ra := Lambda.Except.mapError_ok_h' h_out
    have h_penv := postEnv_wf C Env proc _ v_setup v_pre v_out h_ta h_setup h_pre h_ra
      h_wf h_fwf h_resolved
    have h_E4mono := E4_ContextMono C Env proc _ v_setup v_pre v_out h_setup h_pre h_ra
      h_wf h_fwf h_mono
    have h_cs_fresh := procBody_cs_fresh C Env proc _ v_setup v_pre v_out v_post
      h_ta h_setup h_pre h_ra h_post h_wf h_fwf h_resolved
    have h_unify' := Lambda.Except.mapError_ok_h' h_unify
    have h_bwf := procBodyEnv_wf C _ proc v_post _ v_unify h_post h_unify' h_cs_fresh
      h_penv.1 h_penv.2.1 h_E4mono h_penv.2.2 h_fwf
    -- Apply annotated statement soundness; all WF args now discharged.
    obtain ⟨C_out, h_body_typed⟩ := Statement.typeCheck_annotated_sound _ _ P
      (some proc) ss v_body.1 v_body.2 h_stc'
      h_bwf.1        -- TEnvWF envForBody
      h_fwf          -- FactoryWF C_body.functions (= C.functions)
      h_bwf.2.1      -- envForBody.context.types ≠ []
      h_bwf.2.2.1    -- ContextMono envForBody.context
      h_bwf.2.2.2    -- AliasesResolved envForBody.context
      h_rigid_inv    -- from the checker's rigid-refinement guard (`find? = none`)
      h_closed       -- CalledProcsClosed P (threaded)
    -- The userSubst rename (fresh → declared), the rigid var set, and the inverse renaming.
    let userSubst : Lambda.Subst :=
      [List.filterMap (fun x => match x.snd with
        | LMonoTy.ftvar fresh => some (fresh, LMonoTy.ftvar x.fst) | _ => none)
        (List.flatten v_setup.2.snd)]
    let rigidVars : List Lambda.TyIdentifier :=
      List.filterMap (fun x => match x.snd with | LMonoTy.ftvar id => some id | _ => none)
        (List.flatten v_setup.2.snd)
    let invSubst : Lambda.Subst :=
      [List.filterMap (fun x => match x.snd with
        | LMonoTy.ftvar fresh => some (x.fst, LMonoTy.ftvar fresh) | _ => none)
        (List.flatten v_setup.2.snd)]
    -- The checker's body input context (fresh-instantiated, subst'd by the body's final subst).
    let bodyΓ : TContext Unit :=
      (v_post.snd.updateSubst v_unify).context.subst v_body.snd.stateSubstInfo.subst
    -- SubstReq for userSubst: renaming + left-inverse + rigid-image-disjoint + aliasesWF.
    have h_SR : SubstReq ({ C with rigidTypeVars := rigidVars }) bodyΓ userSubst invSubst := by
      obtain ⟨freshtvs, h_len, h_S, h_gf, h_nodup, h_genn⟩ :=
        setupInputEnv_shape_fresh C Env proc _ v_setup h_setup
      have h_ta_nodup : proc.header.typeArgs.Nodup := (checkTypeArgsWF_props proc _ () h_ta).1
      have h_us : userSubst = [freshtvs.zip (proc.header.typeArgs.map LMonoTy.ftvar)] := by
        show [_] = _
        rw [h_S]; congr 1
        exact filterMap_userSubst proc.header.typeArgs freshtvs h_len.symm
      have h_rig : rigidVars = freshtvs := by
        show List.filterMap _ _ = _
        rw [h_S]; exact filterMap_rigid proc.header.typeArgs freshtvs h_len.symm
      have h_inv : invSubst = [proc.header.typeArgs.zip (freshtvs.map LMonoTy.ftvar)] := by
        show [_] = _
        rw [h_S]; congr 1
        exact filterMap_invSubst proc.header.typeArgs freshtvs h_len.symm
      -- Disjoint since freshtvs are gen-named but typeArgs are not gen-prefixed.
      have h_disj : ∀ f ∈ freshtvs, f ∉ proc.header.typeArgs := by
        intro f hf hmem
        obtain ⟨k, h_fk⟩ := h_genn f hf
        exact not_prefix_ne_gen f ((checkTypeArgsWF_props proc _ () h_ta).2.2 f hmem) k h_fk
      refine {
        ren := ?_, rig_notin_range := ?_, inv_on_rigid := ?_, aliasesWF := ?_ }
      · intro v; rw [h_us]; exact userSubst_ren proc.header.typeArgs freshtvs v
      · intro v hv x
        show v ∉ LMonoTy.freeVars (LMonoTy.subst userSubst (.ftvar x))
        rw [h_us]
        have hv' : v ∈ freshtvs := h_rig ▸ hv
        exact userSubst_rig_notin proc.header.typeArgs freshtvs h_len.symm h_disj v hv' x
      · intro v hv
        show LMonoTy.subst invSubst (LMonoTy.subst userSubst (.ftvar v)) = .ftvar v
        rw [h_us, h_inv]
        have hv' : v ∈ freshtvs := h_rig ▸ hv
        exact userSubst_inv proc.header.typeArgs freshtvs h_len.symm h_ta_nodup v hv'
      · -- aliasesWF: bodyΓ.aliases = (updateSubst).context.aliases; WF from h_bwf.1.
        show ∀ a, a ∈ bodyΓ.aliases → TypeAlias.WF a
        show ∀ a, a ∈ (TContext.subst (v_post.snd.updateSubst v_unify).context
          v_body.snd.stateSubstInfo.subst).aliases → TypeAlias.WF a
        rw [TContext.subst_aliases]
        exact h_bwf.1.aliasesWF
    have h_IC : StmtsInitClosed ({ C with rigidTypeVars := rigidVars }).rigidTypeVars v_body.1 :=
      statement_typeCheck_InitClosed ({ C with rigidTypeVars := rigidVars })
        (v_post.snd.updateSubst v_unify) P (some proc) ss v_body.1 v_body.2 h_stc'
        h_bwf.1 h_fwf h_bwf.2.1 h_bwf.2.2.1 h_rigid_inv h_closed
    have h_subst := StmtsHasTypeA_subst_gen P ({ C with rigidTypeVars := rigidVars })
      bodyΓ [] v_body.1 C_out v_body.2.context userSubst invSubst h_body_typed h_SR h_IC
    -- Transport the derivation from `{C with rig := rigidVars}` back to ambient `C`.
    have h_C : StmtsHasTypeA P C
        (TContext.subst bodyΓ userSubst) []
        (List.map (Statement.subst userSubst) v_body.fst)
        ({ C_out with rigidTypeVars := C.rigidTypeVars })
        (TContext.subst v_body.snd.context userSubst) := by
      have h_sub : C.rigidTypeVars ⊆ rigidVars := by
        rw [h_ambient_no_rigid]; exact List.nil_subset _
      have h_drop := StmtsHasTypeA_rig_drop P C.rigidTypeVars ({ C with rigidTypeVars := rigidVars })
        (TContext.subst bodyΓ userSubst) []
        (List.map (Statement.subst userSubst) v_body.fst) C_out
        (TContext.subst v_body.snd.context userSubst) h_subst h_sub
      -- `{{C with rig := rigidVars} with rig := C.rigidTypeVars} = C` by structure eta.
      exact h_drop
    have h_expr_congr : ∀ (Γa Γb : TContext Unit) (Cx : LContext CoreLParams)
        (e : Expression.Expr) (t : LMonoTy),
        (∀ x, Γb.types.find? x = Γa.types.find? x) → Γb.aliases = Γa.aliases →
        instHasTypeA.exprTyped Cx Γa e t → instHasTypeA.exprTyped Cx Γb e t :=
      fun _ _ _ _ _ _ _ h_e => h_e
    have h_env'_shape : Env'.context.types
        = TContext.types.subst (Maps.pop (v_post.snd.updateSubst v_unify).context.types)
            v_body.snd.stateSubstInfo.subst := by
      rw [← h_env']
      exact statement_typeCheck_popContext_types _ (v_post.snd.updateSubst v_unify) P (some proc)
        ss v_body.1 v_body.2 h_stc' h_bwf.1 h_fwf h_bwf.2.1 h_bwf.2.2.1 h_rigid_inv h_closed
    have h_ef_pop : Maps.pop (v_post.snd.updateSubst v_unify).context.types = Env.context.types :=
      envForBody_pop_context_types C Env proc _ v_setup v_pre v_out v_post v_unify
        h_setup h_pre h_ra h_post h_ta h_wf h_fwf h_resolved
    have h_ub : (v_post.snd.updateSubst v_unify).context.types
        = Maps.newest (v_post.snd.updateSubst v_unify).context.types :: Env.context.types := by
      have h_nc := maps_eq_newest_cons_pop _ h_bwf.2.1
      rw [h_ef_pop] at h_nc
      exact h_nc
    -- Close `bodyTyped` via `find_congr`, leaving the two body-context bridge goals below.
    refine ProcBodyHasType'.structured _ ({ C_out with rigidTypeVars := C.rigidTypeVars }) _
      (StmtsHasType'_find_congr h_expr_congr h_C _ ?bridge2b ?bridge2a).choose_spec.2.2
    case bridge2b =>
      -- Reduce to `body_context_find_agree`'s four hypotheses.
      apply body_context_find_agree (S' := v_body.snd.stateSubstInfo.subst)
          (ambient := Env.context.types)
          (freshScope := Maps.newest (v_post.snd.updateSubst v_unify).context.types)
          (h_closed := fun ty hty => h_ambient_closed ty hty)
      case h_pbc =>
        rw [procBodyContext_types, h_env'_shape, h_ef_pop]; rfl
      case h_bodyΓ_types =>
        show TContext.types.subst (v_post.snd.updateSubst v_unify).context.types
            v_body.snd.stateSubstInfo.subst = _
        rw [h_ub]; rfl
      case h_newest =>
        -- `S'` collapses on the instantiated sub-scopes (free vars ⊆ freshtvs) and the outer
        -- `userSubst` rename matches `proc'`'s declared types.
        obtain ⟨freshtvs, h_len, h_S, h_gf, h_nodup, h_genn⟩ :=
          setupInputEnv_shape_fresh C Env proc _ v_setup h_setup
        have h_ta_props := checkTypeArgsWF_props proc _ () h_ta
        have h_S'_fix : ∀ v ∈ freshtvs,
            LMonoTy.subst v_body.snd.stateSubstInfo.subst (LMonoTy.ftvar v) = LMonoTy.ftvar v := by
          have h_rig : rigidVars = freshtvs := by
            show List.filterMap _ _ = _
            rw [h_S]; exact filterMap_rigid proc.header.typeArgs freshtvs h_len.symm
          have h_ri : ∀ v ∈ rigidVars,
              LMonoTy.subst v_body.snd.stateSubstInfo.subst (LMonoTy.ftvar v) = LMonoTy.ftvar v := by
            have h_go := h_stc'
            unfold Statement.typeCheck Statement.typeCheckAux at h_go
            simp only [bind, Except.bind] at h_go
            split at h_go
            · exact absurd h_go (by simp)
            · rename_i v_aux h_goeq
              obtain ⟨ss_aux, Env_aux, C_aux⟩ := v_aux
              simp only [Except.ok.injEq] at h_go
              have h_pres := typeCheckAux_go_preserves _ (v_post.snd.updateSubst v_unify) P (some proc)
                ss [] [] ss_aux Env_aux C_aux h_goeq h_bwf.1 h_fwf h_bwf.2.1 h_bwf.2.2.1 h_rigid_inv h_closed
              intro v hv
              rw [← h_go]
              exact h_pres.rigid_inv v hv
          intro v hv; exact h_ri v (h_rig ▸ hv)
        have h_in_closed : ∀ w ∈ LMonoTys.freeVars (ListMap.values v_setup.1), w ∈ freshtvs :=
          setupInputEnv_values_closed C Env proc _ v_setup freshtvs h_setup h_wf h_len h_S
            (fun x hx => h_ta_props.2.1 x (List.mem_append_left _ hx))
        have h_out_closed : ∀ w ∈ LMonoTys.freeVars (ListMap.values ((proc.header.outputs.keys).zip v_out.fst)),
            w ∈ freshtvs := by
          have h_aw : TContext.AliasesWF v_pre.2.context :=
            pre_env_AliasesWF C Env proc _ v_setup v_pre h_setup h_pre h_wf h_fwf
          intro w hw
          have hw_list : w ∈ LMonoTys.freeVars v_out.1 := by
            obtain ⟨elt, h_elt, h_v⟩ := LMonoTys.freeVars_exists hw
            have h_sub : ListMap.values ((proc.header.outputs.keys).zip v_out.fst) ⊆ v_out.1 := by
              rw [ListMap.values_eq_map_snd]
              exact (List.map_snd_zip_sublist (proc.header.outputs.keys) v_out.fst).subset
            exact LMonoTys.freeVars_mem_subset (h_sub h_elt) h_v
          have hw_pre : w ∈ LMonoTys.freeVars
              (List.map (LMonoTy.subst v_setup.2.snd) (ListMap.values proc.header.outputs)) :=
            LMonoTys_resolveAliases_freeVars_subset (T := CoreLParams)
              (List.map (LMonoTy.subst v_setup.2.snd) (ListMap.values proc.header.outputs))
              v_pre.2 v_out.1 v_out.2 h_ra h_aw w hw_list
          rw [← LMonoTys_subst_eq_map, h_S] at hw_pre
          exact LMonoTys.freeVars_subst_closed proc.header.typeArgs freshtvs h_len
            (ListMap.values proc.header.outputs)
            (fun tv htv => h_ta_props.2.1 tv (List.mem_append_right _ htv)) w hw_pre
        -- old-scope values are a sublist of the input values, so also closed under freshtvs.
        have h_old_closed : ∀ w ∈ LMonoTys.freeVars
            (ListMap.values (v_setup.1.filter (fun x => (ListMap.keys proc.header.outputs).contains x.1))),
            w ∈ freshtvs := by
          intro w hw
          apply h_in_closed w
          obtain ⟨elt, h_elt, h_v⟩ := LMonoTys.freeVars_exists hw
          have h_sub : ListMap.values (v_setup.1.filter (fun x => (ListMap.keys proc.header.outputs).contains x.1))
              ⊆ ListMap.values v_setup.1 := by
            rw [ListMap.values_eq_map_snd, ListMap.values_eq_map_snd]
            exact (List.filter_sublist.map Prod.snd).subset
          exact LMonoTys.freeVars_mem_subset (h_sub h_elt) h_v
        -- Rewrite the RHS newest scope into inputs++outputs++old and match each sub-scope.
        rw [envForBody_newest_context_types C Env proc _ v_setup v_pre v_out v_post v_unify
          h_setup h_pre h_ra h_post h_ta h_wf h_fwf h_resolved]
        simp only [List.append_eq, subst_go_append]
        rw [TContext_types_subst_go_append, TContext_types_subst_go_append]
        congr 1
        · congr 1
          · exact (subst_go_collapse_rename userSubst v_body.snd.stateSubstInfo.subst freshtvs
              v_setup.fst h_in_closed h_S'_fix).symm
          · exact (subst_go_collapse_rename userSubst v_body.snd.stateSubstInfo.subst freshtvs
              ((proc.header.outputs.keys).zip v_out.fst) h_out_closed h_S'_fix).symm
        · -- Old-inout scope: matched via `old_scope_eq`, since the `userSubst` rename fixes output
          -- keys (so both sides filter on the same key set).
          have h_len_out : (ListMap.keys proc.header.outputs).length ≤ v_out.fst.length := by
            have h_len_ra := resolveAliasesList_length _ _ _ _ h_ra
            rw [h_len_ra, List.length_map, ListMap.keys_eq_map_fst,
              ListMap.values_eq_map_snd, List.length_map, List.length_map]
            exact Nat.le_refl _
          have h_okeys : ListMap.keys (List.map
              (fun x => (x.fst, LMonoTy.subst userSubst x.snd))
              ((ListMap.keys proc.header.outputs).zip v_out.fst))
              = ListMap.keys proc.header.outputs := by
            rw [ListMap.keys_eq_map_fst, List.map_map]
            have h_ml := List.map_congr_left
              (l := (ListMap.keys proc.header.outputs).zip v_out.fst)
              (f := (Prod.fst ∘ fun x : CoreIdent × LMonoTy =>
                (x.fst, LMonoTy.subst userSubst x.snd)))
              (g := Prod.fst) (fun p _ => rfl)
            rw [h_ml, List.map_fst_zip h_len_out]
          show List.map (fun x => (CoreIdent.mkOld x.fst.name, LTy.forAll [] x.snd))
              (Procedure.Header.getInoutParams _) = _
          rw [Procedure.Header.getInoutParams]
          show List.map (fun x => (CoreIdent.mkOld x.fst.name, LTy.forAll [] x.snd))
              (List.filter (fun p => (ListMap.keys (List.map
                (fun x => (x.fst, LMonoTy.subst userSubst x.snd))
                ((ListMap.keys proc.header.outputs).zip v_out.fst))).contains p.1)
                (List.map (fun x => (x.fst, LMonoTy.subst userSubst x.snd)) v_setup.fst)) = _
          rw [h_okeys]
          -- `S'` fixes every free var of the retained inout values.
          refine old_scope_eq v_setup.fst (ListMap.keys proc.header.outputs) userSubst
            v_body.snd.stateSubstInfo.subst ?_
          intro x hx v hv
          apply h_S'_fix
          apply h_in_closed
          rw [ListMap.values_eq_map_snd]
          exact LMonoTys.freeVars_mem_subset (List.mem_map_of_mem hx) hv
    case bridge2a =>
      -- Aliases agreement.
      rw [procBodyContext_aliases, TContext.subst_aliases]
      show Env'.context.aliases = bodyΓ.aliases
      rw [show bodyΓ = (v_post.snd.updateSubst v_unify).context.subst
          v_body.snd.stateSubstInfo.subst from rfl, TContext.subst_aliases]
      rw [← h_env', popContext_context_eq]
      show v_body.snd.context.aliases = bodyΓ.aliases
      exact StmtsHasType'_aliases h_body_typed
  · simp only [reduceCtorEq] at h


/-- Annotated soundness: a successful `Procedure.typeCheck` implies the output procedure `proc'`
    satisfies `ProcHasTypeA` at the ambient type-scope `Env'.context` in which the checker typed
    the body. It concludes at `Env'.context` specifically because `bodyTyped`'s scope is
    Γ-dependent (unlike the Γ-free pre/postcondition fields). -/
theorem Procedure.typeCheck_annotated_sound (C : LContext CoreLParams) (Env : TEnv Unit)
    (P : Program) (proc proc' : Procedure) (Env' : TEnv Unit) (md : MetaData Expression)
    (h : Procedure.typeCheck C Env P proc md = .ok (proc', Env'))
    (h_wf : TEnvWF (T := CoreLParams) Env)
    (h_fwf : FactoryWF C.functions)
    (h_resolved : TContext.AliasesResolved Env.context)
    (h_mono : ContextMono Env.context)
    (h_ambient_closed : ∀ ty, ty ∈ Maps.values Env.context.types → LTy.freeVars ty = [])
    (h_ambient_no_rigid : C.rigidTypeVars = [])
    (h_closed : CalledProcsClosed P) :
    ProcHasTypeA P C Env'.context proc' := by
  exact {
    inputsNodup := Procedure.typeCheck_inputsNodup C Env P proc proc' Env' md h
    outputsNodup := Procedure.typeCheck_outputsNodup C Env P proc proc' Env' md h
    typeArgsNodup := Procedure.typeCheck_typeArgsNodup C Env P proc proc' Env' md h
    noUndeclaredVars := Procedure.typeCheck_noUndeclaredVars C Env P proc proc' Env' md h h_wf h_fwf
    modRights := Procedure.typeCheck_modRights C Env P proc proc' Env' md h h_wf h_fwf h_resolved
      h_mono h_closed
    preconditionsTyped :=
      Procedure.typeCheck_preconditionsTyped_annotated C Env P proc proc' Env' md h h_wf h_fwf h_resolved
        Env'.context
    postconditionsTyped :=
      Procedure.typeCheck_postconditionsTyped_annotated C Env P proc proc' Env' md h h_wf h_fwf h_resolved
        Env'.context
    bodyTyped :=
      Procedure.typeCheck_bodyTyped_annotated C Env P proc proc' Env' md h h_wf h_fwf h_resolved
        h_mono h_ambient_closed h_ambient_no_rigid h_closed
  }

set_option warningAsError false in
/-- Polymorphic soundness: a successful `Procedure.typeCheck` implies the INPUT procedure `proc`
    satisfies `ProcHasType` in the ambient type-scope `Env.context`. Currently `sorry`. -/
theorem Procedure.typeCheck_sound (C : LContext CoreLParams) (Env : TEnv Unit)
    (P : Program) (proc proc' : Procedure) (Env' : TEnv Unit) (md : MetaData Expression)
    (h : Procedure.typeCheck C Env P proc md = .ok (proc', Env'))
    (h_wf : TEnvWF (T := CoreLParams) Env)
    (h_fwf : FactoryWF C.functions)
    (h_resolved : TContext.AliasesResolved Env.context)
    (h_aliases_not_known : ∀ a ∈ Env.context.aliases, a.name ≠ "arrow")
    (h_ali_nd : AliasesNonDropping Env.context.aliases)
    (h_arrow_wf : ArrowKnownBinary C)
    (h_ambient_rigid : ∀ x ty, Env.context.types.find? x = some ty →
      ∀ v ∈ LTy.freeVars ty, v ∈ C.rigidTypeVars)
    (h_ambient_mono : ∀ ty ∈ Maps.values Env.context.types, LTy.boundVars ty = [])
    (h_ambient_no_rigid : C.rigidTypeVars = [])
    (h_closed : CalledProcsClosed P) :
    ProcHasType P C Env.context proc := by
  sorry

end TypeSpec
end Core
