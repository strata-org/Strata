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
import all Strata.DL.Lambda.LExprTypeEnv

/-! ## Soundness of the Procedure Typechecker

Relates the executable procedure typechecker `Core.Procedure.typeCheck` to the
declarative relation `ProcHasType'` from `ProcedureTypeSpec.lean`. Procedure-level
analogue of `FunctionTypeSpecProps.lean` / `StatementTypeSpecProps.lean`.

* **Annotated** `Procedure.typeCheck_annotated_sound`: success ⇒ the OUTPUT
  procedure `proc'` satisfies `ProcHasTypeA` (for any ambient `Γ`, since the
  annotated judgment is context-free).
* **Polymorphic** `Procedure.typeCheck_sound`: success ⇒ the INPUT procedure
  `proc` satisfies `ProcHasType` in the ambient `Env.context`.

The body obligation delegates to the already-proved statement soundness theorems
(`Statement.typeCheck_{annotated_sound,sound}`) plus a context bridge; see
`PROC_TYPE_SOUND_PLAN.md`.
-/

namespace Core
namespace TypeSpec

open Lambda LExpr Imperative
open Core.Statement

/-! ### Group P — procedure-entry well-formedness preservation

Lemmas showing the body-typing environment `envForBody` inside `Procedure.typeCheck`
is well-formed, built by composing the per-step preservation primitives across
`setupInputEnv` / `typeCheckConditions` / etc. These discharge the WF hypotheses of
`Statement.typeCheck_{sound,annotated_sound}` when it is invoked on the procedure body. -/

-- TEnvWF preserved through typeCheckConditions.go (structural recursion over conditions).
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

-- resolve preserves the full context when the input context is nonempty
-- (the empty-init guard `if types.isEmpty then ... else Env` is a no-op).
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

-- typeCheckConditions.go preserves the whole context (hence types≠[], ContextMono, AliasesResolved).
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

-- Top-level typeCheckConditions wrappers (strip the `go` accumulator).
theorem typeCheckConditions_TEnvWF (C : Core.Expression.TyContext) (Env : Core.Expression.TyEnv)
    (conditions : ListMap CoreLabel Core.Procedure.Check) (procName : CoreIdent)
    (res : Array Expression.Expr × Core.Expression.TyEnv)
    (h : Core.Procedure.typeCheckConditions C Env conditions procName = .ok res)
    (h_wf : TEnvWF (T := CoreLParams) Env)
    (h_fwf : FactoryWF C.functions) :
    TEnvWF (T := CoreLParams) res.2 := by
  simp only [Core.Procedure.typeCheckConditions] at h
  exact typeCheckConditions_go_TEnvWF C procName conditions #[] Env res h h_wf h_fwf

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

-- setupInputEnv: TEnvWF preservation (pushEmptyContext → instantiateWithSubst → addInNewestContext).
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

/-! ### Group P (cont.) — body-env WF cluster (postEnv_wf / procBodyEnv_wf) and
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

-- (2) AliasesWF preservation through setupInputEnv (aliases unchanged from Env).
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

-- (3) Corollary: exact discharge for the noUndeclaredVars call site.
-- Mirrors the in-scope hyps at ProcedureTypeSpecProps.lean:519.
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

-- A list is a prefix of itself appended with anything (for the gen-prefix bridge).
private theorem list_isPrefixOf_append_left {α} [BEq α] [LawfulBEq α] (xs ys : List α) :
    xs.isPrefixOf (xs ++ ys) = true := by
  induction xs with
  | nil => simp [List.isPrefixOf]
  | cons a rest ih =>
    simp only [List.cons_append, List.isPrefixOf, beq_self_eq_true, Bool.true_and]; exact ih

-- Bridge: a name that is not gen-prefixed cannot equal any `tyPrefix ++ toString n`.
private theorem not_prefix_ne_gen (ta : String)
    (h : ¬ Lambda.TState.tyPrefix.toList.isPrefixOf ta.toList) :
    ∀ n : Nat, ta ≠ Lambda.TState.tyPrefix ++ toString n := by
  intro n heq
  apply h
  rw [heq, String.toList_append]
  exact list_isPrefixOf_append_left _ _

theorem setupInputEnv_shape_fresh
    (C : Core.Expression.TyContext) (Env : Core.Expression.TyEnv)
    (proc : Procedure) (fr : Strata.FileRange)
    (v_setup : @Lambda.LMonoTySignature Unit × Core.Expression.TyEnv × Lambda.Subst)
    (h_setup : Core.Procedure.setupInputEnv C Env proc fr = .ok v_setup) :
    ∃ freshtvs : List TyIdentifier,
      freshtvs.length = proc.header.typeArgs.length ∧
      v_setup.2.snd = [proc.header.typeArgs.zip (freshtvs.map LMonoTy.ftvar)] ∧
      (∀ tv, tv ∈ freshtvs →
        ∀ n, n ≥ v_setup.2.fst.genEnv.genState.tyGen → tv ≠ TState.tyPrefix ++ toString n) := by
  -- Decompose setupInputEnv: pushEmptyContext (gen unchanged), instantiateWithSubst, addInNewest.
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
    -- Peel instantiateWithSubst into instantiateEnvWithSubst (genTyVars) + go loop.
    simp only [Lambda.LMonoTySignature.instantiateWithSubst, Bind.bind, Except.bind] at h_inst
    elim_err h_inst with v_env h_env; obtain ⟨mtys, Env_e, S⟩ := v_env
    elim_err h_inst with v_go h_go; obtain ⟨newtys, Env₂⟩ := v_go
    simp only [Except.ok.injEq, Prod.mk.injEq] at h_inst
    obtain ⟨h_sig, h_env2, h_S2⟩ := h_inst
    obtain ⟨freshtvs, genEnv', h_gen, _, h_S, _, h_genEnv⟩ :=
      instantiateEnvWithSubst_decompose proc.header.typeArgs (ListMap.values proc.header.inputs)
        Env.pushEmptyContext (mtys, Env_e, S) h_env
    simp only at h_S h_genEnv
    refine ⟨freshtvs, ?_len, ?_shape, ?_fresh⟩
    case _len =>
      exact TGenEnv.genTyVars_length proc.header.typeArgs.length Env.pushEmptyContext.genEnv
        freshtvs genEnv' h_gen
    case _shape =>
      show tyArgSubst = _
      rw [← h_S2]; exact h_S
    case _fresh =>
      -- v_setup.2.1 = Env₁.addInNewestContext _ (gen unchanged), and Env₁ = Env₂ from the go loop.
      -- gen chain: genEnv'.gen ≤ Env₂.gen = v_setup.2.1.gen.
      show ∀ tv, tv ∈ freshtvs →
        ∀ n, n ≥ (inp_mty_sig, Env₁.addInNewestContext
          (Lambda.LMonoTySignature.toTrivialLTy inp_mty_sig), tyArgSubst).2.1.genEnv.genState.tyGen →
          tv ≠ TState.tyPrefix ++ toString n
      intro tv h_tv n hn
      -- addInNewestContext preserves genState.
      have h_gen_add : (Env₁.addInNewestContext
          (Lambda.LMonoTySignature.toTrivialLTy inp_mty_sig)).genEnv.genState = Env₁.genEnv.genState := rfl
      -- Env₁ = Env₂ (from instantiateWithSubst go-loop output).
      have h_env1_eq : Env₁ = Env₂ := by rw [← h_env2]
      -- gen mono across go loop: Env₂.gen ≥ Env_e.gen; and Env_e.genEnv = genEnv'.
      have h_go_mono : Env₂.genEnv.genState.tyGen ≥ Env_e.genEnv.genState.tyGen :=
        instantiateWithSubst_go_genState_mono C _ Env_e (newtys, Env₂) h_go
      -- Env_e.genEnv = genEnv' (from decompose: result.2.1.genEnv = genEnv').
      have h_ene_gen : Env_e.genEnv = genEnv' := h_genEnv
      -- genTyVars fresh at genEnv'.genState.
      have h_gf : ∀ tv', tv' ∈ freshtvs →
          ∀ m, m ≥ genEnv'.genState.tyGen → tv' ≠ TState.tyPrefix ++ toString m :=
        genTyVars_genFresh' (T := CoreLParams) proc.header.typeArgs.length Env.pushEmptyContext.genEnv
          freshtvs genEnv' h_gen
      -- Assemble: n ≥ v_setup.gen = Env₁.gen = Env₂.gen ≥ Env_e.gen = genEnv'.gen.
      simp only [h_gen_add] at hn
      have h_n_gen : n ≥ genEnv'.genState.tyGen := by
        rw [h_env1_eq] at hn
        rw [h_ene_gen] at h_go_mono
        omega
      exact h_gf tv h_tv n h_n_gen

-- typeCheckConditions.go never decreases the gen counter.
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

-- typeCheckConditions never decreases the gen counter.
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

theorem freshnessA
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
  -- Shape of the tyArgSubst PLUS gen-freshness of the fresh vars.
  obtain ⟨freshtvs, h_len, h_S, h_fresh_setup⟩ :=
    setupInputEnv_shape_fresh C Env proc fr v_setup h_setup
  -- v_out.2 = v_pre.2 (resolveAliases leaves env unchanged).
  have h_vout_env : v_out.2 = v_pre.2 :=
    LMonoTys_resolveAliases_env_local _ v_pre.2 v_out.1 v_out.2 h_ra
  -- outputs freeVars ⊆ typeArgs.
  have h_ta_props := checkTypeArgsWF_props proc fr () h_ta
  intro p hp v hv n hn
  -- p.2 ∈ v_out.1.
  have hp_snd : p.2 ∈ v_out.1 := (List.of_mem_zip hp).2
  -- Closedness: v ∈ freeVars p.2 ⊆ freshtvs (replicate noUndeclaredVars lines 822-847).
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
  -- gen chain: setup.gen ≤ v_pre.gen = v_out.gen ≤ n.
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

/-! ### Freshness B -/

theorem freshnessB
    (proc : Procedure) (fr : Strata.FileRange)
    (envWithOutputs : Core.Expression.TyEnv)
    (h_ta : proc.checkTypeArgsWF fr = .ok ())
    (h_typeArgs_no_prefix : ∀ ta ∈ proc.header.typeArgs, ∀ n : Nat, ta ≠ TState.tyPrefix ++ toString n) :
    ∀ p ∈ proc.header.getInoutParams.toList.map
        (fun (x : CoreIdent × LMonoTy) => (CoreIdent.mkOld x.1.name, x.2)),
      ∀ v ∈ LMonoTy.freeVars p.2,
      ∀ n, n ≥ envWithOutputs.genEnv.genState.tyGen → v ≠ TState.tyPrefix ++ toString n := by
  have h_ta_props := checkTypeArgsWF_props proc fr () h_ta
  intro p hp v hv n _
  -- p.2 is an original inout monotype = an input value; its freeVars ⊆ typeArgs.
  have h_v_ta : v ∈ proc.header.typeArgs := by
    -- p = (mkOld x.1.name, x.2) for some x ∈ getInoutParams.toList.
    rw [List.mem_map] at hp
    obtain ⟨x, hx_mem, hx_eq⟩ := hp
    -- p.2 = x.2.
    have hp2 : p.2 = x.2 := by rw [← hx_eq]
    rw [hp2] at hv
    -- getInoutParams = inputs.filter pred, so x ∈ inputs.toList.
    simp only [Procedure.Header.getInoutParams, ListMap.toList, List.mem_filter] at hx_mem
    have hx_in : x ∈ ListMap.toList proc.header.inputs := hx_mem.1
    -- x.2 ∈ inputs.values.
    have hx2_val : x.2 ∈ ListMap.values proc.header.inputs := by
      rw [ListMap.values_eq_map_snd, List.mem_map]
      exact ⟨x, hx_in, rfl⟩
    -- freeVars x.2 ⊆ freeVars inputs.values ⊆ typeArgs.
    have hv_inputs : v ∈ LMonoTys.freeVars (ListMap.values proc.header.inputs) :=
      LMonoTys.freeVars_mem_subset hx2_val hv
    exact h_ta_props.2.1 v (List.mem_append_left _ hv_inputs)
  exact h_typeArgs_no_prefix v h_v_ta n

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
      proc.header.getInoutParams.toList.map fun (id, ty) =>
        (CoreIdent.mkOld id.name, .forAll [] ty)
    let E4 := Lambda.TEnv.addInNewestContext (T := CoreLParams) envWithOutputs oldInoutBindings
    TEnvWF (T := CoreLParams) E4 ∧
    E4.context.types ≠ [] ∧
    TContext.AliasesResolved E4.context := by
  intro out_mty_sig out_lty_sig envWithOutputs oldInoutBindings E4
  -- v_out.2 = v_pre.2 : resolveAliases leaves the Env unchanged.
  have h_vout_env : v_out.2 = v_pre.2 :=
    LMonoTys_resolveAliases_env_local _ v_pre.2 v_out.1 v_out.2 h_ra
  -- WF chain up to v_pre.2 (= v_out.2).
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
  -- E4 conjuncts.
  refine ⟨?_tenvwf, ?_types_ne, ?_resolved⟩
  case _tenvwf =>
    show TEnvWF (T := CoreLParams) E4
    -- Layer 1: envWithOutputs = addInNewestContext v_out.2 (toTrivialLTy out_mty_sig).
    -- toTrivialLTy s = s.map (fun p => (p.1, .forAll [] p.2)), so of_addInNewestContext_mono applies.
    have h_out_eq : out_lty_sig = out_mty_sig.map (fun p => (p.1, LTy.forAll [] p.2)) := rfl
    have h_envWithOutputs_wf : TEnvWF (T := CoreLParams) envWithOutputs := by
      show TEnvWF (T := CoreLParams) (Lambda.TEnv.addInNewestContext (T := CoreLParams) v_out.2 out_lty_sig)
      rw [h_out_eq]
      refine TEnvWF.of_addInNewestContext_mono (T := CoreLParams) v_out.2 out_mty_sig
        (by rw [h_vout_env]; exact h_pre_wf) ?_out_fresh
      case _out_fresh =>
        -- freshness A: free vars of the resolved-substituted output types are the setup fresh
        -- vars (< setup gen ≤ v_out.2 gen), so never `$__tyN` for N ≥ v_out.2 gen.
        have h_aw : TContext.AliasesWF v_pre.2.context :=
          pre_env_AliasesWF C Env proc fr v_setup v_pre h_setup h_pre h_wf h_fwf
        exact freshnessA C Env proc fr v_setup v_pre v_out h_ta h_setup h_pre h_ra h_wf h_fwf h_aw
    -- Layer 2: E4 = addInNewestContext envWithOutputs oldInoutBindings.
    -- oldInoutBindings = (map (mkOld,ty) getInoutParams), already `.forAll [] ty` shape.
    have h_old_eq : oldInoutBindings =
        (proc.header.getInoutParams.toList.map fun (id, ty) => (CoreIdent.mkOld id.name, ty)).map
          (fun p => (p.1, LTy.forAll [] p.2)) := by
      simp only [oldInoutBindings, List.map_map]
      rfl
    show TEnvWF (T := CoreLParams)
      (Lambda.TEnv.addInNewestContext (T := CoreLParams) envWithOutputs oldInoutBindings)
    rw [h_old_eq]
    refine TEnvWF.of_addInNewestContext_mono (T := CoreLParams) envWithOutputs _
      h_envWithOutputs_wf ?_old_fresh
    case _old_fresh =>
      -- freshness B: old-binding types are the user-declared inout monotypes; their free vars are
      -- in `typeArgs` (checkTypeArgsWF), which — since the checker's gen-prefix guard rejects any
      -- `$__ty`-prefixed typeArg — are never `$__tyN`.
      have h_no_prefix : ∀ ta ∈ proc.header.typeArgs, ∀ n : Nat,
          ta ≠ Lambda.TState.tyPrefix ++ toString n := by
        intro ta hta n
        exact not_prefix_ne_gen ta ((checkTypeArgsWF_props proc fr () h_ta).2.2 ta hta) n
      exact freshnessB proc fr envWithOutputs h_ta h_no_prefix
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
  -- typeCheckConditions preserves the whole context (given TEnvWF + types≠[] + FactoryWF).
  have h_post_ctx : v_post.2.context = E4.context :=
    typeCheckConditions_context C E4 proc.spec.postconditions proc.header.name v_post h_post
      h_E4_wf h_E4_ne h_fwf
  have h_post_wf : TEnvWF (T := CoreLParams) v_post.2 :=
    typeCheckConditions_TEnvWF C E4 proc.spec.postconditions proc.header.name v_post h_post
      h_E4_wf h_fwf
  -- updateSubst leaves the context untouched.
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

/-! ### `ContextMono` of the body env, chained from `ContextMono Env.context`.
    `find?` on the body env falls through the pushed `forAll []` scopes to the ambient
    context, so `ContextMono` of the body env genuinely needs `ContextMono Env.context`
    (a documented Core invariant, exposed as a hypothesis of the annotated deliverable). -/

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
          (ListMap.toList proc.header.getInoutParams))).context := by
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
      (ListMap.toList proc.header.getInoutParams))
      = (List.map (fun x : CoreIdent × LMonoTy => (CoreIdent.mkOld x.fst.name, x.snd))
          (ListMap.toList proc.header.getInoutParams)).map (fun p => (p.1, LTy.forAll [] p.2)) := by
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
    env's generator counter — the freshness precondition of `procBodyEnv_wf`'s
    `updateSubst` step. Declared typeArgs are never gen-prefixed (`checkTypeArgsWF_props`);
    the fresh instantiation vars are gen-fresh at setup (`setupInputEnv_shape_fresh`), and
    the counter only grows through pre/resolveAliases/post. -/
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
          (ListMap.toList proc.header.getInoutParams)))
      proc.spec.postconditions proc.header.name = .ok v_post)
    (h_wf : TEnvWF (T := CoreLParams) Env)
    (h_fwf : FactoryWF C.functions)
    (h_resolved : TContext.AliasesResolved Env.context) :
    ∀ v, v ∈ Lambda.Constraints.freeVars
        (List.map (fun x => (LMonoTy.ftvar x.fst, x.snd)) (List.flatten v_setup.2.snd)) →
      ∀ n, n ≥ v_post.2.genEnv.genState.tyGen → v ≠ Lambda.TState.tyPrefix ++ toString n := by
  have h_penv := postEnv_wf C Env proc fr v_setup v_pre v_out h_ta h_setup h_pre h_ra
    h_wf h_fwf h_resolved
  obtain ⟨freshtvs, h_len, h_shape, h_fresh_setup⟩ :=
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
        (ListMap.toList proc.header.getInoutParams))).genEnv.genState.tyGen
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

/-! ### Part I — Annotated soundness (about the output `proc'`)

Field lemmas feeding `Procedure.typeCheck_annotated_sound`. Each concludes about
`proc'` and takes only the lightweight hypotheses (the annotated `HasTypeA`
judgment needs no alias bridge). ALL currently `sorry` (layer-1 stubs). -/

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
  elim_err h                       -- checkTypeArgsWF
  elim_err h                       -- checkModificationRights
  elim_err h                       -- setupInputEnv
  rename_i v_setup h_setup
  elim_err h                       -- typeCheckConditions (pre)
  elim_err h                       -- resolveAliases
  elim_err h                       -- typeCheckConditions (post)
  split at h                       -- proc.body
  · rename_i ss h_body
    elim_err h                     -- unify
    split at h                     -- rigid-refinement guard
    · simp at h
    elim_err h                     -- Statement.typeCheck (guard's none branch)
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
  elim_err h                       -- checkTypeArgsWF
  elim_err h                       -- checkModificationRights
  elim_err h                       -- setupInputEnv
  rename_i v_setup h_setup
  elim_err h                       -- typeCheckConditions (pre)
  elim_err h                       -- resolveAliases
  rename_i v_out h_out
  elim_err h                       -- typeCheckConditions (post)
  split at h                       -- proc.body
  · rename_i ss h_body
    elim_err h                     -- unify
    split at h                     -- rigid-refinement guard
    · simp at h
    elim_err h                     -- Statement.typeCheck (guard's none branch)
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
    proc.header.typeArgs` (`ProcedureType.lean:171`), so this follows from the
    `checkTypeArgsWF` guard's `Nodup` check on the input. -/
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
  split at h                       -- proc.body
  · elim_err h                     -- pure ss (bodyStmts)
    elim_err h                     -- unify
    split at h                     -- rigid-refinement guard
    · simp at h
    elim_err h                     -- pure () (guard's none branch)
    elim_err h                     -- Statement.typeCheck
    cases h
    exact (checkTypeArgsWF_props proc _ _ h_ta).1
  · simp at h

/-- Annotated `noUndeclaredVars`. `proc'`'s input/output types are `userSubst`-renamed
    back to the declared names, and `proc'.typeArgs = proc.header.typeArgs` is preserved,
    so the `checkTypeArgsWF` guard (every signature type var ∈ typeArgs) transports to
    `proc'`. Requires relating `freeVars (subst userSubst mty)` back to the declared
    type args. -/
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
    -- decompose instantiateWithSubst to expose tyArgSubst shape
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

/-- Closedness of the instantiated input signature values under `freshtvs`:
    `instantiateWithSubst` computes `mtys = subst [zip typeArgs (map ftvar freshtvs)]
    sig.values` then runs the `go` loop (non-growing under AliasesWF). So if
    `sig.values` is closed under `typeArgs`, every output value free var is in
    `freshtvs`. Inputs analogue of the outputs branch's closedness step. -/
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
  -- `values inp_mty_sig` is a sublist of `newtys`, so `w ∈ freeVars newtys`.
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
  -- `freshtvs' = freshtvs`: the two substitution scopes agree, `map ftvar` is injective.
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
  elim_err h with h_ta          -- checkTypeArgsWF
  elim_err h
  elim_err h with h_setup       -- setupInputEnv
  rename_i v_setup
  elim_err h with h_pre
  rename_i v_pre
  elim_err h with h_ra_out      -- resolveAliases outputs
  rename_i v_out
  elim_err h with h_post
  split at h                    -- proc.body
  · elim_err h                  -- pure ss (bodyStmts)
    elim_err h                  -- unify
    split at h                  -- rigid-refinement guard
    · simp at h
    elim_err h                  -- pure () (guard's none branch)
    elim_err h with h_body      -- Statement.typeCheck
    cases h
    -- Common: expose the tyArgSubst shape and declared-vars closedness.
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
      -- INPUTS: v ∈ freeVars of (subst userSubst) applied to the instantiated inputs.
      -- Closedness of `v_setup.fst` values under `freshtvs`: the instantiate output
      -- is `resolveAliases (subst tyArgSubst input)` (non-growing under AliasesWF),
      -- and inputs are closed under `typeArgs` (`checkTypeArgsWF_props`).
      have h_in_closed : ∀ x, x ∈ LMonoTys.freeVars (ListMap.values proc.header.inputs) →
          x ∈ proc.header.typeArgs := by
        intro x hx
        exact h_ta_props.2.1 x (List.mem_append_left _ hx)
      have h_vals_closed : ∀ w, w ∈ LMonoTys.freeVars (ListMap.values v_setup.fst) →
          w ∈ freshtvs :=
        setupInputEnv_values_closed C Env proc _ v_setup freshtvs h_setup h_wf h_len h_S
          h_in_closed
      -- extract the element carrying `v` and finish via `freeVars_userSubst_mem_typeArgs`.
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
      -- OUTPUTS: v ∈ freeVars of (subst userSubst) applied to resolveAliases outputs.
      obtain ⟨elt, h_elt_mem, h_v_elt⟩ := LMonoTys.freeVars_exists hv_out
      simp only [List.mem_map, Function.comp_apply] at h_elt_mem
      obtain ⟨p, hp_mem, hp_eq⟩ := h_elt_mem
      -- p ∈ (keys proc.header.outputs).zip v_out.fst, so p.snd ∈ v_out.fst.
      have hp_snd : p.snd ∈ v_out.fst := (List.of_mem_zip hp_mem).2
      subst hp_eq
      -- Closedness of p.snd (a resolveAliases output value) under freshtvs.
      have h_closed_elt : ∀ w, w ∈ LMonoTy.freeVars p.snd → w ∈ freshtvs := by
        intro w hw
        -- w ∈ freeVars of the whole resolveAliases output list.
        have hw_list : w ∈ LMonoTys.freeVars v_out.fst :=
          LMonoTys.freeVars_mem_subset hp_snd hw
        -- resolveAliases doesn't grow free vars (needs AliasesWF of pre-env).
        have h_ra := Lambda.Except.mapError_ok_h' h_ra_out
        -- AliasesWF of the pre-conditions env: the pre-loop preserves the whole context
        -- (`typeCheckConditions_context`, needs FactoryWF + types≠[]) and setupInputEnv leaves
        -- aliases as `Env.context`'s, so `AliasesWF` transports from `h_wf`.
        have h_aw : TContext.AliasesWF v_pre.snd.context :=
          pre_env_AliasesWF C Env proc _ v_setup v_pre h_setup h_pre h_wf h_fwf
        have hw_pre : w ∈ LMonoTys.freeVars
            (List.map (LMonoTy.subst v_setup.2.snd) (ListMap.values proc.header.outputs)) :=
          LMonoTys_resolveAliases_freeVars_subset (T := CoreLParams)
            (List.map (LMonoTy.subst v_setup.2.snd) (ListMap.values proc.header.outputs))
            v_pre.snd v_out.fst v_out.snd h_ra h_aw w hw_list
        -- rewrite map (subst S) = LMonoTys.subst S, and S = [typeArgs.zip (freshtvs.map ftvar)]
        rw [← LMonoTys_subst_eq_map, h_S] at hw_pre
        -- now closedness via freeVars_subst_closed.
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

-- LEMMA A: Statement.subst preserves modifiedVars.
mutual
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

theorem subst_block_modifiedVars (S : Subst) (bss : List Statement) :
    Block.modifiedVars (List.map (Statement.subst S) bss) = Block.modifiedVars bss := by
  match bss with
  | [] => rfl
  | s :: rest =>
    simp only [List.map_cons, Block.modifiedVars]
    rw [subst_modifiedVars S s, subst_block_modifiedVars S rest]
end

-- LEMMA B: Statement.subst preserves definedVars.
mutual
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

theorem subst_block_definedVars (S : Subst) (bss : List Statement) (b : Bool) :
    Block.definedVars (List.map (Statement.subst S) bss) b = Block.definedVars bss b := by
  match bss with
  | [] => rfl
  | s :: rest =>
    rw [List.map_cons, Block.definedVars.eq_2, Block.definedVars.eq_2,
      subst_definedVars S s b, subst_block_definedVars S rest b]
end

-- LEMMA C: Imperative.Cmd.typeCheck preserves modifiedVars and definedVars.
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

-- LEMMA D: Statement.typeCheckCmd preserves modifiedVars and definedVars (Command level).
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

theorem block_modifiedVars_append (l1 l2 : List Statement) :
    Block.modifiedVars (l1 ++ l2) = Block.modifiedVars l1 ++ Block.modifiedVars l2 := by
  induction l1 with
  | nil => rfl
  | cons s rest ih =>
    simp only [List.cons_append, Block.modifiedVars.eq_2, ih, List.append_assoc]

theorem block_definedVars_append (l1 l2 : List Statement) (b : Bool) :
    Block.definedVars (l1 ++ l2) b = Block.definedVars l1 b ++ Block.definedVars l2 b := by
  induction l1 with
  | nil => simp only [List.nil_append, Block.definedVars.eq_1, List.nil_append]
  | cons s rest ih =>
    simp only [List.cons_append, Block.definedVars.eq_2, ih, List.append_assoc]

-- Abbreviation for the vars-preservation conclusion.
def VarsPreserved (ss' acc ss : List Statement) : Prop :=
  Block.modifiedVars ss' = Block.modifiedVars acc.reverse ++ Block.modifiedVars ss ∧
  (∀ b, Block.definedVars ss' b = Block.definedVars acc.reverse b ++ Block.definedVars ss b)

-- LEMMA E: typeCheckAux.go preserves modifiedVars/definedVars (modulo accumulator).
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
      -- goBlock preservation (threading) via the existing lemma.
      obtain ⟨h_head, h_Cblk⟩ :=
        goBlock_eq_GoPreserved P op C₀ Env₀ bss₀ [] (label₀ :: labels₀) bss' Env_blk C_blk
          h_blk hwf₀ hfwf₀ hne₀ hmono₀ hrigid₀ h_closed
      subst h_Cblk
      -- vars of block body via the goBlock motive IH.
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
    have h_lfwf : Lambda.LFuncWF func :=
      Function.typeCheck_LFuncWF C₀ Env₀ func0 func Env_mid h_ft hwf₀
    have h_absorbs : Subst.absorbs Env_mid.stateSubstInfo.subst Env₀.stateSubstInfo.subst :=
      Function.typeCheck_absorbs C₀ Env₀ func0 func Env_mid h_ft hwf₀ hfwf₀
    have h_head : GoPreserved C₀ (C₀.addFactoryFunction func) Env₀ Env_mid := by
      refine ⟨Function.typeCheck_TEnvWF C₀ Env₀ func0 func Env_mid h_ft hwf₀ hfwf₀,
        addFactoryFunction_FactoryWF C₀ func hfwf₀ h_lfwf, ?_, ?_, h_absorbs,
        addFactoryFunction_rigidTypeVars C₀ func, ?_, ?_, ?_,
        Function.typeCheck_tyGen_mono C₀ Env₀ func0 func Env_mid h_ft hwf₀ hfwf₀⟩
      · rw [h_ctx]; exact hne₀
      · rw [h_ctx]; exact hmono₀
      · exact Function.typeCheck_preserves_rigid_inv C₀ Env₀ func0 func Env_mid h_ft hwf₀ hfwf₀ hrigid₀
      · rw [h_ctx]
      · rw [h_ctx]
    have h_rigid_mid : ∀ v, v ∈ (C₀.addFactoryFunction func).rigidTypeVars →
        LMonoTy.subst Env_mid.stateSubstInfo.subst (.ftvar v) = .ftvar v := by
      rw [addFactoryFunction_rigidTypeVars]; exact h_head.rigid_inv
    obtain ⟨ih_m, ih_d⟩ :=
      ih_tail (Stmt.funcDecl decl' md₀) Env_mid (C₀.addFactoryFunction func) ss'₀ Env'₀ C'₀
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

-- LEMMA F: Statement.typeCheck (top level) preserves modifiedVars/definedVars.
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
    -- Vars of the type-annotated (pre-subst) statements.
    obtain ⟨hm_aux, hd_aux⟩ :=
      typeCheckAux_go_vars P op h_closed C Env ss [] [] ssA Env_aux C_aux
        h_wf h_fwf h_ne h_mono h_rigid_inv h_aux
    simp only [List.reverse_nil, Block.modifiedVars.eq_1, List.nil_append] at hm_aux
    -- `ss' = subst.go S ssA []`; subst preserves vars.
    refine ⟨?_, ?_⟩
    · rw [← h_ss', Statement.subst_go_nil, subst_block_modifiedVars, hm_aux]
    · intro b
      have hd_aux_b := hd_aux b
      simp only [List.reverse_nil, Block.definedVars.eq_1, List.nil_append] at hd_aux_b
      rw [← h_ss', Statement.subst_go_nil, subst_block_definedVars, hd_aux_b]


/-! ### `rigidVars_fixed_by_unify` — the fresh instantiation vars are fixed by the
    body-unify result (feeds `modRights`/`bodyTyped`'s rigid_inv). -/

/-- Per-step keys bound. When the LHS of the constraint is a type variable `a` that
    is NOT already a key of `S`, `unifyOne` cannot take the `some sty` branch (which is
    the only one that recurses with a possibly-different key set); it takes the reflexive
    branch (no new key) or the `none` branch (adds exactly key `a`). Either way the
    resulting keys are contained in `a :: keys S`. -/
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

/-- Core induction. Under the assumptions that every constraint's LHS is a type
    variable (`h_lhs_ftvar`), those LHS variables are pairwise distinct
    (`h_nodup`) and none of them is already a key of `S_in` (`h_lhs_fresh`), the
    ONLY new keys `unifyCore` can add are those LHS variables. Hence a variable `w`
    that is neither a key of `S_in` nor one of the LHS variables is not a key of the
    result.

    The `h_lhs_fresh` hypothesis is essential: it forces `Maps.find? S a = none` at
    each head, killing the `some sty` recursion branch of `unifyOne` (which would
    otherwise be able to add arbitrary keys, including `w`). -/
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
        -- a ∉ keys S_in
        have h_a_S : a ∉ Maps.keys S_in.subst :=
          h_fresh (LMonoTy.ftvar a, c2) (List.mem_cons_self) a rfl
        -- Per-step: keys(relS_one) ⊆ a :: keys S_in.
        have h_step := unifyOne_keys_ftvar_lhs a c2 S_in relS_one h_one h_a_S
        -- lhsVars ((ftvar a, c2) :: rest) = a :: lhsVars rest
        have h_lhs_cons : lhsVars ((LMonoTy.ftvar a, c2) :: rest) = a :: lhsVars rest := by
          simp only [lhsVars, List.filterMap_cons]
        rw [h_lhs_cons] at h_nodup
        -- Re-establish hypotheses for rest with S = relS_one.newS.
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

/-- Main deliverable. -/
theorem rigidVars_fixed_by_unify
    (S_in S_out : SubstInfo) (tyArgSubst : Subst)
    (h_unify : Constraints.unify (tyArgSubst.flatten.map (fun kv => (LMonoTy.ftvar kv.1, kv.2))) S_in
      = .ok S_out)
    -- Provenance (call-site discharge): fresh RHS vars are not keys of the incoming subst.
    (h_fresh_notin : ∀ id, (∃ k, (k, LMonoTy.ftvar id) ∈ tyArgSubst.flatten) →
      id ∉ Maps.keys S_in.subst)
    -- Provenance (call-site discharge): fresh RHS vars are distinct from the declared
    -- (LHS / first-component) vars.
    (h_fresh_ne_lhs : ∀ id, (∃ k, (k, LMonoTy.ftvar id) ∈ tyArgSubst.flatten) →
      ∀ k, (∃ t, (k, t) ∈ tyArgSubst.flatten) → id ≠ k)
    -- Provenance (call-site discharge): declared (LHS / first-component) vars are not
    -- keys of the incoming subst.
    (h_orig_notin_S : ∀ k, (∃ t, (k, t) ∈ tyArgSubst.flatten) → k ∉ Maps.keys S_in.subst)
    -- Provenance (call-site discharge): declared (LHS) vars are pairwise distinct.
    (h_orig_nodup : (tyArgSubst.flatten.map (fun kv => kv.1)).Nodup)
    (v : TyIdentifier)
    (h_v : v ∈ tyArgSubst.flatten.filterMap (fun kv => match kv.2 with
      | LMonoTy.ftvar id => some id | _ => none)) :
    LMonoTy.subst S_out.subst (LMonoTy.ftvar v) = LMonoTy.ftvar v := by
  -- v is a fresh RHS var: there is a key k with (k, ftvar v) ∈ flatten.
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
  -- v ∉ keys(S_in)
  have h_v_notin_S : v ∉ Maps.keys S_in.subst := h_fresh_notin v h_v_prov
  -- Every constraint's LHS is a type variable.
  have h_lhs_ftvar : ∀ p, p ∈ tyArgSubst.flatten.map (fun kv => (LMonoTy.ftvar kv.1, kv.2)) →
      ∃ a, p.1 = LMonoTy.ftvar a := by
    intro p hp
    obtain ⟨kv, _, h_p⟩ := List.mem_map.mp hp
    exact ⟨kv.1, by rw [← h_p]⟩
  -- Membership helper: an element of the constraint list comes from `(kv.1, kv.2) ∈ flatten`.
  have h_cs_mem : ∀ p, p ∈ tyArgSubst.flatten.map (fun kv => (LMonoTy.ftvar kv.1, kv.2)) →
      ∃ kv : TyIdentifier × LMonoTy, (kv.1, kv.2) ∈ tyArgSubst.flatten ∧
        p = (LMonoTy.ftvar kv.1, kv.2) := by
    intro p hp
    obtain ⟨kv, h_kv_mem, h_p⟩ := List.mem_map.mp hp
    exact ⟨kv, h_kv_mem, h_p.symm⟩
  -- LHS vars are not keys of S_in.
  have h_lhs_fresh : ∀ p, p ∈ tyArgSubst.flatten.map (fun kv => (LMonoTy.ftvar kv.1, kv.2)) →
      ∀ a, p.1 = LMonoTy.ftvar a → a ∉ Maps.keys S_in.subst := by
    intro p hp a ha
    obtain ⟨kv, h_kv_mem, h_peq⟩ := h_cs_mem p hp
    rw [h_peq] at ha; simp only [LMonoTy.ftvar.injEq] at ha; subst ha
    exact h_orig_notin_S kv.1 ⟨kv.2, h_kv_mem⟩
  -- lhsVars of the constraint list = map fst flatten (Nodup transfers).
  have h_lhsVars_eq : lhsVars (tyArgSubst.flatten.map (fun kv => (LMonoTy.ftvar kv.1, kv.2)))
      = tyArgSubst.flatten.map (fun kv => kv.1) := by
    simp only [lhsVars, List.filterMap_map, Function.comp_def]
    induction tyArgSubst.flatten with
    | nil => rfl
    | cons a l ih => simp only [List.filterMap_cons, List.map_cons, ih]
  have h_nodup : (lhsVars (tyArgSubst.flatten.map (fun kv => (LMonoTy.ftvar kv.1, kv.2)))).Nodup := by
    rw [h_lhsVars_eq]; exact h_orig_nodup
  -- v is not a LHS var of any constraint.
  have h_v_notin_lhs : ∀ p, p ∈ tyArgSubst.flatten.map (fun kv => (LMonoTy.ftvar kv.1, kv.2)) →
      ∀ a, p.1 = LMonoTy.ftvar a → v ≠ a := by
    intro p hp a ha
    obtain ⟨kv, h_kv_mem, h_peq⟩ := h_cs_mem p hp
    rw [h_peq] at ha; simp only [LMonoTy.ftvar.injEq] at ha; subst ha
    exact h_fresh_ne_lhs v h_v_prov kv.1 ⟨kv.2, h_kv_mem⟩
  -- v ∉ keys(S_out)
  have h_v_notkey : v ∉ Maps.keys S_out.subst :=
    unify_keys_orient _ S_in S_out h_unify h_lhs_ftvar h_lhs_fresh h_nodup
      v h_v_notin_S h_v_notin_lhs
  -- subst fixes vars not in the domain.
  apply LMonoTy.subst_no_relevant_keys
  intro x hx
  have h_xv : x = v := by
    simp only [LMonoTy.freeVars, List.mem_singleton] at hx; exact hx
  subst h_xv
  exact h_v_notkey


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
    · -- checkModificationRights: the guard we care about.
      split at h
      · simp only [reduceCtorEq] at h
      · rename_i _ _ h_mr
        -- `h_mr : (if filter_nonempty then error else ok unit) = ok v`, forces filter empty.
        split at h_mr
        · simp only [reduceCtorEq] at h_mr
        · rename_i h_empty_neg
          -- h_empty_neg : ¬((!(filter ...).isEmpty) = true), i.e. the filter is empty.
          have h_filter_empty : (List.filter
              (fun v => !(ListMap.keys proc.header.outputs ++
                (HasVarsImp.definedVars (P := Expression) proc.body false).eraseDups).contains v)
              (HasVarsImp.modifiedVars (P := Expression) proc.body).eraseDups) = [] := by
            rw [← List.isEmpty_iff]
            simpa using h_empty_neg
          rw [List.filter_eq_nil_iff] at h_filter_empty
          -- The guard as a membership implication on `proc.body`'s vars.
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
          clear h_empty_neg h_mr h_filter_empty
          -- Peel the remaining pipeline to expose proc'.
          elim_err h                       -- setupInputEnv
          rename_i v_setup h_setup
          elim_err h with v_pre h_pre      -- typeCheckConditions (pre)
          elim_err h                       -- resolveAliases
          rename_i v_out h_out
          elim_err h with v_post h_post    -- typeCheckConditions (post)
          split at h                       -- proc.body
          · rename_i ss h_body
            elim_err h with v_unify h_unify -- unify
            split at h                     -- rigid-refinement guard
            · simp at h
            rename_i h_rigid_none            -- rigidVars.find? (subst ≠ id) = none
            elim_err h with v_body h_stc   -- Statement.typeCheck (via mapError)
            injection h with h_pair
            injection h_pair with h_proc _
            subst h_proc
            -- Strip the mapError wrapper on `Statement.typeCheck`.
            have h_tc := Lambda.Except.mapError_ok_h' h_stc
            -- Strip the mapError wrapper on `resolveAliases` for the outputs.
            have h_ra := Lambda.Except.mapError_ok_h' h_out
            -- WF of the body env via `procBodyEnv_wf` + the guard's `rigid_inv`.
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
            -- Vars of the type-annotated body equal vars of the input body `ss`.
            obtain ⟨h_bm, h_bd⟩ :=
              statement_typeCheck_vars
                { functions := C.functions, datatypes := C.datatypes, knownTypes := C.knownTypes,
                  idents := C.idents,
                  rigidTypeVars := List.filterMap
                    (fun x => match x.snd with | LMonoTy.ftvar id => some id | x => none)
                    (List.flatten v_setup.2.snd) }
                (v_post.snd.updateSubst v_unify) P (some proc) ss v_body.fst v_body.snd
                hb_wf hb_fwf hb_ne hb_mono hb_rigid hb_closed h_tc
            -- outputs.keys is preserved: keys.length ≤ length of resolved outputs.
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
            -- Assemble. Reduce proc'.body's modified/defined vars to `ss`'s.
            intro v hv
            simp only [HasVarsImp.modifiedVars, HasVarsImp.definedVars,
              subst_block_modifiedVars, subst_block_definedVars, h_bm, h_bd] at hv ⊢
            -- proc.body = .structured ss, so proc's modified/defined vars are `ss`'s.
            have h_gm : v ∈ HasVarsImp.modifiedVars (P := Expression) proc.body := by
              rw [h_body]; exact hv
            have h_res := h_guard v h_gm
            rw [h_body] at h_res
            -- h_res : v ∈ proc.header.outputs.keys ++ Block.definedVars ss false;
            -- rewrite outputs.keys forward to the annotated (subst-renamed) keys.
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
    `bool` (`HasTypeA [] e bool`), provided the accumulator's elements already are.
    The guard `annotatedExpr.toLMonoTy != mty[bool]` forces the resolved type to be
    `bool`, and `resolve_HasTypeA` gives the judgment. -/
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
  elim_err h                       -- checkNoDuplicates
  elim_err h                       -- checkTypeArgsWF
  elim_err h                       -- checkModificationRights
  elim_err h with h_setup          -- setupInputEnv
  rename_i v_setup
  elim_err h with h_pre            -- typeCheckConditions (pre)
  rename_i v_pre
  elim_err h                       -- resolveAliases
  elim_err h                       -- typeCheckConditions (post)
  split at h                       -- match proc.body
  · rename_i ss h_body
    elim_err h                     -- pure ss (bodyStmts)
    elim_err h                     -- unify
    split at h                     -- rigid-refinement guard
    · simp at h
    elim_err h                     -- pure () (guard's none branch)
    elim_err h                     -- Statement.typeCheck
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
    annotated judgment. The two remaining `sorry`s are the shared layer-2
    `procBodyEnv_wf` obligation (`TEnvWF` + `AliasesResolved` of the postcondition
    env, after `setupInputEnv` → pre → resolveAliases → addInNewest×2). -/
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
  elim_err h                       -- checkNoDuplicates
  elim_err h with h_ta             -- checkTypeArgsWF
  elim_err h                       -- checkModificationRights
  elim_err h with h_setup          -- setupInputEnv
  rename_i v_setup
  elim_err h with h_pre            -- typeCheckConditions (pre)
  rename_i v_pre
  elim_err h with h_out            -- resolveAliases
  rename_i v_out
  elim_err h with h_post           -- typeCheckConditions (post)
  rename_i v_post
  split at h                       -- match proc.body
  · rename_i ss h_body
    elim_err h                     -- pure ss (bodyStmts)
    elim_err h                     -- unify
    split at h                     -- rigid-refinement guard
    · simp at h
    elim_err h                     -- pure () (guard's none branch)
    elim_err h                     -- Statement.typeCheck
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
    -- WF + AliasesResolved of the postcondition env (E4) via `postEnv_wf`.
    have h_ra := Lambda.Except.mapError_ok_h' h_out
    have h_penv := postEnv_wf C Env proc _ v_setup v_pre v_out h_ta h_setup h_pre h_ra
      h_wf h_fwf h_resolved
    exact typeCheckConditions_HasTypeA C _ proc.spec.postconditions proc.header.name
      v_post h_post h_penv.1 h_fwf h_penv.2.2 c.expr h_mem
  · exact absurd h (by simp only [reduceCtorEq, not_false_eq_true])

/-! #### Layer-2 dependencies of the body spine (stated here; proved below/deferred). -/

/-- `StmtsHasTypeA` is preserved under `Statement.subst` (a type-variable renaming): the
    annotated typing judgment `HasTypeA [] e mty` is stable under renaming type variables
    in binder annotations. This lifts the expression-level `applySubstT_unresolved_HasTypeA`
    to statement lists. Layer-2 leaf (Group-S, annotated). -/
theorem StmtsHasTypeA_subst (P : Program) (C : LContext CoreLParams)
    (Γ : TContext Unit) (L : List String) (ss : List Statement)
    (C' : LContext CoreLParams) (Γ' : TContext Unit) (S : Lambda.Subst)
    (h : StmtsHasTypeA P C Γ L ss C' Γ') :
    StmtsHasTypeA P C Γ L (ss.map (Core.Statement.Statement.subst S)) C' Γ' := by
  sorry

/-- Annotated `bodyTyped`: the output body is well-typed as a statement list under the
    annotated judgment. Delegates to `Statement.typeCheck_annotated_sound` + a context
    bridge (`StmtsHasType'_find_congr`). THE SPINE of the annotated deliverable. -/
theorem Procedure.typeCheck_bodyTyped_annotated (C : LContext CoreLParams) (Env : TEnv Unit)
    (P : Program) (proc proc' : Procedure) (Env' : TEnv Unit) (md : MetaData Expression)
    (h : Procedure.typeCheck C Env P proc md = .ok (proc', Env'))
    (h_wf : TEnvWF (T := CoreLParams) Env)
    (h_fwf : FactoryWF C.functions)
    (h_resolved : TContext.AliasesResolved Env.context)
    (h_mono : ContextMono Env.context)
    (h_closed : CalledProcsClosed P) :
    ∀ Γ, ProcBodyHasType' LMonoTy P C (procBodyContext Γ proc') proc'.body := by
  intro Γ
  -- Peel Procedure.typeCheck to expose the body call and proc'.body's shape.
  simp only [Procedure.typeCheck, Procedure.checkNoDuplicates, bind, Except.bind,
    pure, Except.pure] at h
  split at h
  · simp at h
  rename_i h_in_guard
  elim_err h with h_ta             -- checkTypeArgsWF
  elim_err h                       -- checkModificationRights
  elim_err h                       -- setupInputEnv
  rename_i v_setup h_setup
  elim_err h                       -- typeCheckConditions (pre)
  rename_i v_pre h_pre
  elim_err h                       -- resolveAliases
  rename_i v_out h_out
  elim_err h                       -- typeCheckConditions (post)
  rename_i v_post h_post
  split at h                       -- proc.body
  · rename_i ss h_body
    elim_err h                     -- unify
    rename_i v_unify h_unify
    split at h                     -- rigid-refinement guard
    · simp at h
    rename_i h_rigid_none           -- rigidVars.find? (subst ≠ id) = none
    elim_err h                     -- Statement.typeCheck (the body call)
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
    injection h_pair with h_proc _
    subst h_proc
    -- Strip the mapError wrapper from h_stc.
    have h_stc' := Core.WF.Except.mapError_ok h_stc
    -- WF of the body env via `procBodyEnv_wf` (postEnv_wf + E4_ContextMono + procBody_cs_fresh).
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
    -- Apply Statement.subst userSubst preservation, then bridge context.
    have h_subst := StmtsHasTypeA_subst P _ _ [] v_body.1 C_out v_body.2.context
      [List.filterMap (fun x => match x.snd with
        | LMonoTy.ftvar fresh => some (fresh, LMonoTy.ftvar x.fst) | _ => none)
        (List.flatten v_setup.2.snd)] h_body_typed
    let checkerCtx : TContext Unit :=
      (v_post.snd.updateSubst v_unify).context.subst v_body.snd.stateSubstInfo.subst
    -- BRIDGE 1 (C rigidTypeVars): transport the derivation from C_body to ambient C.
    have h_C : StmtsHasTypeA P C checkerCtx []
        (List.map (Statement.subst
          [List.filterMap (fun x => match x.snd with
            | LMonoTy.ftvar fresh => some (fresh, LMonoTy.ftvar x.fst) | _ => none)
            (List.flatten v_setup.2.snd)]) v_body.fst) C_out v_body.snd.context := by
      sorry -- ESCALATE layer-2: StmtsHasTypeA rigidTypeVars-irrelevance (C_body → C)
    -- BRIDGE 2 (context): checkerCtx vs procBodyContext Γ proc' agree on find?/aliases.
    have h_expr_congr : ∀ (Γa Γb : TContext Unit) (Cx : LContext CoreLParams)
        (e : Expression.Expr) (t : LMonoTy),
        (∀ x, Γb.types.find? x = Γa.types.find? x) → Γb.aliases = Γa.aliases →
        instHasTypeA.exprTyped Cx Γa e t → instHasTypeA.exprTyped Cx Γb e t :=
      fun _ _ _ _ _ _ _ h_e => h_e
    apply ProcBodyHasType'.structured _ C_out
    exact (StmtsHasType'_find_congr h_expr_congr h_C _
        (by
          intro x
          sorry) -- ESCALATE layer-2: fresh↔declared find?-agreement (procBodyContext vs subst envForBody.context)
        (by sorry) -- ESCALATE layer-2: aliases agreement (procBodyContext vs subst envForBody.context)
      ).choose_spec.2.2
  · simp only [reduceCtorEq] at h

/-- **Annotated soundness (deliverable 1).** A successful `Procedure.typeCheck`
    implies the output procedure `proc'` satisfies `ProcHasTypeA` at any ambient `Γ`. -/
theorem Procedure.typeCheck_annotated_sound (C : LContext CoreLParams) (Env : TEnv Unit)
    (P : Program) (proc proc' : Procedure) (Env' : TEnv Unit) (md : MetaData Expression)
    (h : Procedure.typeCheck C Env P proc md = .ok (proc', Env'))
    (h_wf : TEnvWF (T := CoreLParams) Env)
    (h_fwf : FactoryWF C.functions)
    (h_resolved : TContext.AliasesResolved Env.context)
    (h_mono : ContextMono Env.context)
    (h_closed : CalledProcsClosed P) :
    ∀ Γ, ProcHasTypeA P C Γ proc' := by
  intro Γ
  exact {
    inputsNodup := Procedure.typeCheck_inputsNodup C Env P proc proc' Env' md h
    outputsNodup := Procedure.typeCheck_outputsNodup C Env P proc proc' Env' md h
    typeArgsNodup := Procedure.typeCheck_typeArgsNodup C Env P proc proc' Env' md h
    noUndeclaredVars := Procedure.typeCheck_noUndeclaredVars C Env P proc proc' Env' md h h_wf h_fwf
    modRights := Procedure.typeCheck_modRights C Env P proc proc' Env' md h h_wf h_fwf h_resolved
      h_mono h_closed
    preconditionsTyped :=
      Procedure.typeCheck_preconditionsTyped_annotated C Env P proc proc' Env' md h h_wf h_fwf h_resolved Γ
    postconditionsTyped :=
      Procedure.typeCheck_postconditionsTyped_annotated C Env P proc proc' Env' md h h_wf h_fwf h_resolved Γ
    bodyTyped :=
      Procedure.typeCheck_bodyTyped_annotated C Env P proc proc' Env' md h h_wf h_fwf h_resolved
        h_mono h_closed Γ
  }

end TypeSpec
end Core
