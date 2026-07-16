/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

import Strata.Languages.Core.StatementTypeSpec
import all Strata.Languages.Core.FunctionTypeSpec
import all Strata.Languages.Core.CommandTypeSpecProps
import all Strata.Languages.Core.StatementType
import all Strata.Languages.Core.FunctionType
import all Strata.Languages.Core.FunctionTypeSpecProps
import all Strata.DL.Lambda.LExprTypeEnv

/-! ## Soundness of the Statement Typechecker

Relates the executable statement typechecker `Statement.typeCheckAux` /
`Statement.typeCheck` to the declarative relations `StmtsHasType` / `StmtsHasTypeA`
from `StatementTypeSpec.lean`. Statement-level analogue of `CommandTypeSpecProps.lean`.

* **Part I (unannotated)** `Statement.typeCheck_sound`: success ⇒ the original
  statements satisfy `StmtsHasType` between the substituted input/output contexts.
* **Part II (annotated)** `Statement.typeCheck_annotated_sound`: success ⇒ the
  output statements (with the final substitution applied) satisfy `StmtsHasTypeA`.

The `funcDecl` case rests on `Function.typeCheck_HasType_output` (the output function
satisfies `FuncHasType`), which is currently `sorry`. -/

namespace Core
namespace TypeSpec

open Lambda LExpr Imperative


/-! ### Part I — Core `go`/`goBlock` induction (unannotated)

The central reusable lemmas: a mutual induction matching the `typeCheckAux.go` /
`goBlock` recursion. The top-level theorem reduces to these. -/

/-- The bundle of threading invariants preserved by a `typeCheckAux` `go` run from
    input `(C, Env)` to output `(C', Env')`. Collecting them in one structure keeps
    the soundness `cons` step and the `go.induct` IH premises readable (named-field
    access instead of long projection chains). -/
structure GoPreserved (C C' : LContext CoreLParams) (Env Env' : TEnv Unit) : Prop where
  /-- The output environment is still well-formed. -/
  wf : TEnvWF (T := CoreLParams) Env'
  /-- The output factory is still well-formed. -/
  fwf : FactoryWF C'.functions
  /-- The output type-scope is non-empty (needed by the resolve/infer machinery). -/
  ne : Env'.context.types ≠ []
  /-- The output context still satisfies the monotonicity invariant. -/
  mono : ContextMono Env'.context
  /-- The *final* substitution refines the input one: it absorbs every binding the
      input substitution already knew. This is what lets a `cons` head be typed at
      the list-final substitution. -/
  absorbs : Subst.absorbs Env'.stateSubstInfo.subst Env.stateSubstInfo.subst
  /-- The rigid type-variable set is unchanged (`addFactoryFunction` /
      `addKnownTypeWithError` do not touch it). -/
  rigid_eq : C'.rigidTypeVars = C.rigidTypeVars
  /-- Rigid-identity is preserved at the *output* substitution. -/
  rigid_inv : ∀ v, v ∈ C.rigidTypeVars →
    LMonoTy.subst Env'.stateSubstInfo.subst (.ftvar v) = .ftvar v
  /-- **Structural stack-tail preservation** (no well-scoping assumed): a `go` run
      only grows the *newest* `types` scope, so popping it recovers the input tail.
      This is what lets `block`/`goBlock` restore the input context after `popContext`. -/
  types_pop : Maps.pop Env'.context.types = Maps.pop Env.context.types
  /-- The alias list is unchanged by a `go` run (only `addTypeAlias`, not used here,
      touches it). -/
  aliases_eq : Env'.context.aliases = Env.context.aliases
  /-- The type-variable generator counter is monotone (fresh-name allocation only
      increases it). Needed to re-route `ctxFreshForGen`/`boundVarsFresh` after a pop. -/
  tyGen_mono : Env'.genEnv.genState.tyGen ≥ Env.genEnv.genState.tyGen

/-- `GoPreserved` composes along a `go` step: a preserved head (`C → C_mid`,
    `Env → Env_mid`) followed by a preserved tail (`C_mid → C'`, `Env_mid → Env'`)
    yields a preserved whole (`C → C'`, `Env → Env'`). The substitution refinement
    chains by `Subst.absorbs_trans`; the rigid set/identity chain through both. -/
theorem GoPreserved.trans {C C_mid C' : LContext CoreLParams}
    {Env Env_mid Env' : TEnv Unit}
    (h_head : GoPreserved C C_mid Env Env_mid)
    (h_tail : GoPreserved C_mid C' Env_mid Env') :
    GoPreserved C C' Env Env' where
  wf := h_tail.wf
  fwf := h_tail.fwf
  ne := h_tail.ne
  mono := h_tail.mono
  absorbs := Subst.absorbs_trans _ _ _ h_head.absorbs h_tail.absorbs
  rigid_eq := h_tail.rigid_eq.trans h_head.rigid_eq
  rigid_inv := fun v hv => by
    -- `v ∈ C.rigidTypeVars = C_mid.rigidTypeVars`, so the tail's rigid-inv applies.
    have hv' : v ∈ C_mid.rigidTypeVars := by rw [h_head.rigid_eq]; exact hv
    exact h_tail.rigid_inv v hv'
  types_pop := h_tail.types_pop.trans h_head.types_pop
  aliases_eq := h_tail.aliases_eq.trans h_head.aliases_eq
  tyGen_mono := Nat.le_trans h_head.tyGen_mono h_tail.tyGen_mono

/-- `pushEmptyContext` (pushing an empty newest type
    scope) leaves every variable lookup unchanged — the empty scope is transparent. -/
theorem pushEmptyContext_find? (Env : TEnv Unit) (y : CoreIdent) :
    Maps.find? Env.pushEmptyContext.context.types y = Maps.find? Env.context.types y := by
  simp only [TEnv.pushEmptyContext, TEnv.updateContext, TEnv.context, Maps.push, Maps.find?,
    Map.find?]

/-- `find?`-agreement of `pushEmptyContext` is preserved
    after applying a substitution scope-by-scope: `subst` of the pushed context just
    prepends an empty (substituted-`[]`) scope, transparent to `find?`. Needed to bridge
    the block body's input Γ (typed at `subst (push Env).context S`) to the spec's plain
    `subst Env.context S`. -/
theorem subst_pushEmptyContext_find? (Env : TEnv Unit) (S : Subst) (y : CoreIdent) :
    Maps.find? (TContext.subst Env.pushEmptyContext.context S).types y
      = Maps.find? (TContext.subst Env.context S).types y := by
  simp only [TContext.subst, TEnv.pushEmptyContext, TEnv.updateContext, TEnv.context, Maps.push,
    TContext.types.subst, TContext.types.subst.go, Maps.find?, Map.find?]

/-- `pushEmptyContext` does not change the set of
    known type variables (the pushed scope is empty). -/
theorem pushEmptyContext_knownTypeVars (Env : TEnv Unit) :
    TContext.knownTypeVars Env.pushEmptyContext.context = TContext.knownTypeVars Env.context := by
  simp only [TEnv.pushEmptyContext, TEnv.updateContext, TEnv.context, TContext.knownTypeVars,
    TContext.types.knownTypeVars, Maps.push]
  rfl

/-- `pushEmptyContext` preserves `TEnvWF`: it only pushes an empty
    newest type scope, leaving `stateSubstInfo`/`genState`/`aliases` untouched, and
    `find?`/`knownTypeVars` unchanged. No well-scoping. -/
theorem pushEmptyContext_TEnvWF (Env : TEnv Unit) (h_wf : TEnvWF (T := CoreLParams) Env) :
    TEnvWF (T := CoreLParams) Env.pushEmptyContext := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · -- aliasesWF: aliases unchanged.
    show TContext.AliasesWF Env.pushEmptyContext.context
    have h_al : Env.pushEmptyContext.context.aliases = Env.context.aliases := by
      simp only [TEnv.pushEmptyContext, TEnv.updateContext, TEnv.context]
    simp only [TContext.AliasesWF, h_al]; exact h_wf.aliasesWF
  · exact h_wf.substFreshForGen
  · -- ctxFreshForGen: knownTypeVars + genState unchanged.
    show ContextFreshForGen (T := CoreLParams) Env.pushEmptyContext.context
      Env.pushEmptyContext.genEnv.genState
    intro v hv; rw [pushEmptyContext_knownTypeVars] at hv
    exact h_wf.ctxFreshForGen v hv
  · -- boundVarsNodup: find? unchanged.
    intro y ty h_find; rw [pushEmptyContext_find?] at h_find
    exact h_wf.boundVarsNodup y ty h_find
  · -- boundVarsFresh: find? + genState unchanged.
    intro y ty h_find; rw [pushEmptyContext_find?] at h_find
    exact h_wf.boundVarsFresh y ty h_find

/-- `pushEmptyContext` preserves `ContextMono` (lookups unchanged). -/
theorem pushEmptyContext_ContextMono (Env : TEnv Unit) (h_mono : ContextMono Env.context) :
    ContextMono Env.pushEmptyContext.context := by
  intro x ty h_find; rw [pushEmptyContext_find?] at h_find
  exact h_mono x ty h_find

/-- **Block push/pop bridge.** If a `go` run on a block body (started from
    `Env.pushEmptyContext`) preserves the threading invariants down to `Env_body`, then
    `Env_body.popContext` (what `goBlock` returns) recovers the input context entirely and
    preserves `GoPreserved` relative to the original `Env`. Structural: push/pop touch only
    `context.types`, and the `C`-side is the input `C` (block-local decls are discarded). -/
theorem goBlock_GoPreserved {C C_body : LContext CoreLParams} {Env Env_body : TEnv Unit}
    (h_body : GoPreserved C C_body Env.pushEmptyContext Env_body)
    (h_wf : TEnvWF (T := CoreLParams) Env)
    (h_fwf : FactoryWF C.functions)
    (h_ne : Env.context.types ≠ [])
    (h_mono : ContextMono Env.context) :
    GoPreserved C C Env (Env_body.popContext) := by
  -- `pushEmptyContext`/`popContext` leave `stateSubstInfo` and `genState` untouched.
  have h_push_subst : Env.pushEmptyContext.stateSubstInfo = Env.stateSubstInfo := rfl
  have h_pop_subst : (Env_body.popContext).stateSubstInfo = Env_body.stateSubstInfo := rfl
  have h_push_gen : Env.pushEmptyContext.genEnv.genState = Env.genEnv.genState := rfl
  have h_pop_gen : (Env_body.popContext).genEnv.genState = Env_body.genEnv.genState := rfl
  -- KEY: the popped context equals the input context.
  -- `(popContext Env_body).types = Maps.pop Env_body.types` and
  -- `Maps.pop Env_body.types = Maps.pop (push Env.types []) = Env.types` (body `types_pop`).
  have h_pop_types : (Env_body.popContext).context.types = Env.context.types := by
    have h_body_pop := h_body.types_pop
    -- `Maps.pop Env.pushEmptyContext.context.types = Env.context.types`.
    have h_push_pop : Maps.pop Env.pushEmptyContext.context.types = Env.context.types := by
      simp only [TEnv.pushEmptyContext, TEnv.updateContext, TEnv.context, Maps.push, Maps.pop]
    -- `(popContext Env_body).types = Maps.pop Env_body.types`.
    have h_pop_def : (Env_body.popContext).context.types = Maps.pop Env_body.context.types := by
      simp only [TEnv.popContext, TEnv.updateContext, TEnv.context]
    rw [h_pop_def, h_body_pop, h_push_pop]
  have h_pop_aliases : (Env_body.popContext).context.aliases = Env.context.aliases := by
    have h_body_al := h_body.aliases_eq
    have h_pop_al : (Env_body.popContext).context.aliases = Env_body.context.aliases := by
      simp only [TEnv.popContext, TEnv.updateContext, TEnv.context]
    have h_push_al : Env.pushEmptyContext.context.aliases = Env.context.aliases := by
      simp only [TEnv.pushEmptyContext, TEnv.updateContext, TEnv.context]
    rw [h_pop_al, h_body_al, h_push_al]
  -- The popped context equals the input context (both fields).
  have h_pop_ctx : (Env_body.popContext).context = Env.context := by
    have h_eq : ∀ (a b : TContext Unit), a.types = b.types → a.aliases = b.aliases → a = b := by
      intro a b ht ha; cases a; cases b; simp_all
    exact h_eq _ _ h_pop_types h_pop_aliases
  -- The gen-counter is monotone: `Env_body ≥ pushEmptyContext = Env`.
  have h_gen_mono : Env_body.genEnv.genState.tyGen ≥ Env.genEnv.genState.tyGen := by
    have := h_body.tyGen_mono; rw [h_push_gen] at this; exact this
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- TEnvWF: context-side fields from `h_wf` (popped ctx = input ctx), subst-side from body.
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · rw [h_pop_ctx]; exact h_wf.aliasesWF
    · rw [h_pop_subst, h_pop_gen]; exact h_body.wf.substFreshForGen
    · rw [h_pop_ctx, h_pop_gen]; intro v hv n hn
      exact h_wf.ctxFreshForGen v hv n (Nat.le_trans h_gen_mono hn)
    · rw [h_pop_ctx]; exact h_wf.boundVarsNodup
    · rw [h_pop_ctx, h_pop_gen]; intro y ty h_find v hv n hn
      exact h_wf.boundVarsFresh y ty h_find v hv n (Nat.le_trans h_gen_mono hn)
  · exact h_fwf
  · rw [h_pop_ctx]; exact h_ne
  · rw [h_pop_ctx]; exact h_mono
  · -- absorbs: body's subst (unchanged by pop) refines `pushEmptyContext`'s (= input).
    have h_abs := h_body.absorbs
    rw [h_push_subst] at h_abs
    rw [h_pop_subst]; exact h_abs
  · rfl
  · -- rigid_inv at the popped subst = body's subst.
    rw [h_pop_subst]; exact h_body.rigid_inv
  · -- types_pop: `pop (popContext Env_body).types = pop Env.types`.
    rw [h_pop_ctx]
  · rw [h_pop_ctx]
  · rw [h_pop_gen]; exact h_gen_mono

/-- **`goBlock` returns the input `C`.** Structurally (no preservation needed):
    `goBlock` runs the body under `pushEmptyContext` and returns the *input* `C` as its
    third output (block-local type declarations are discarded). Lifts the inline fact
    used in `case_block` so the `ite`/`loop` `_preserves` cases can chain blocks via
    `GoPreserved.trans` without the (circular) `goBlock_eq_GoPreserved`. -/
theorem goBlock_returns_input_C (P : Program) (op : Option Procedure)
    (C C_blk : LContext CoreLParams) (Env Env_blk : TEnv Unit) (bss acc : List Statement)
    (labels : List String) (bss' : List Statement)
    (h : Statement.typeCheckAux.goBlock P op C Env bss acc labels = .ok (bss', Env_blk, C_blk)) :
    C_blk = C := by
  unfold Statement.typeCheckAux.goBlock at h
  simp only [Bind.bind, Except.bind] at h
  cases h_run : Statement.typeCheckAux.go P op C Env.pushEmptyContext bss acc labels with
  | error e => rw [h_run] at h; simp only [reduceCtorEq] at h
  | ok w =>
    obtain ⟨w1, w2, w3⟩ := w
    rw [h_run] at h
    simp only [Except.ok.injEq, Prod.mk.injEq] at h
    exact h.2.2.symm

/-- **Resolve step preservation.** A successful `resolve` (paired with the
    `rigid_inv` fact at its output env, which the typechecker secures via
    `checkAnnotCompat`) preserves every `GoPreserved` invariant, leaving `C`
    unchanged: it preserves the context (so `ne`/`mono`/`types_pop`/`aliases_eq`
    follow), refines the substitution (`absorbs`), keeps `TEnvWF`, and is monotone
    in the generator counter. Reused by `ite`/`loop` `_preserves` for the guard/
    measure resolves. -/
theorem resolve_GoPreserved (C : LContext CoreLParams) (Env Env' : TEnv Unit)
    (e : LExpr CoreLParams.mono) (et : LExprT CoreLParams.mono)
    (h : LExpr.resolve C Env e = .ok (et, Env'))
    (h_wf : TEnvWF (T := CoreLParams) Env)
    (h_fwf : FactoryWF C.functions)
    (h_ne : Env.context.types ≠ [])
    (h_mono : ContextMono Env.context)
    (h_rigid_inv' : ∀ v, v ∈ C.rigidTypeVars →
      LMonoTy.subst Env'.stateSubstInfo.subst (.ftvar v) = .ftvar v) :
    GoPreserved C C Env Env' := by
  have h_ctx : Env'.context = Env.context :=
    resolve_preserves_context e et C Env Env' h h_wf h_ne h_fwf
  refine ⟨resolve_TEnvWF e et C Env Env' h h_wf h_fwf, h_fwf, ?_, ?_,
    resolve_absorbs e et C Env Env' h h_wf h_ne h_fwf, rfl, h_rigid_inv', ?_, ?_,
    resolve_genState_mono C Env Env' e et h h_wf h_fwf⟩
  · rw [h_ctx]; exact h_ne
  · rw [h_ctx]; exact h_mono
  · rw [h_ctx]
  · rw [h_ctx]

/-- `addKnownTypeWithError` only updates the `knownTypes` field, leaving
    `functions` and `rigidTypeVars` untouched. So a successful result shares both
    with the input context. -/
theorem addKnownTypeWithError_preserves (C C' : LContext CoreLParams)
    (k : KnownType) (f : Strata.DiagnosticModel)
    (h : C.addKnownTypeWithError k f = .ok C') :
    C'.functions = C.functions ∧ C'.rigidTypeVars = C.rigidTypeVars := by
  simp only [LContext.addKnownTypeWithError, Bind.bind, Except.bind] at h
  split at h
  · simp only [reduceCtorEq] at h
  · simp only [Except.ok.injEq] at h
    subst h
    exact ⟨rfl, rfl⟩

/-- **Diagnostic-irrelevance of `addKnownTypeWithError` success.** Whether
    `addKnownTypeWithError` succeeds — and what `LContext` it returns — depends only
    on the `containsThenInsertIfNew` boolean, never on the diagnostic `f` (which is
    used solely in the `.error` branch). So success under any `f` gives the same
    success (same `C'`) under any other `f'`. This bridges the typechecker (which
    passes a real diagnostic) to the spec constructor (which uses `default`). -/
theorem addKnownTypeWithError_diag_irrel (C C' : LContext CoreLParams)
    (k : KnownType) (f f' : Strata.DiagnosticModel)
    (h : C.addKnownTypeWithError k f = .ok C') :
    C.addKnownTypeWithError k f' = .ok C' := by
  simp only [LContext.addKnownTypeWithError, KnownTypes.addWithError, Identifiers.addWithError,
    Bind.bind, Except.bind, Std.HashMap.containsThenInsertIfNew_fst,
    Std.HashMap.containsThenInsertIfNew_snd] at h ⊢
  -- Both `if`s share the condition `k.name ∈ C.knownTypes`; only the `.error` payload
  -- differs across `f`/`f'`, so the success result is identical.
  cases hc : Std.HashMap.contains C.knownTypes k.name with
  | true => simp only [hc, if_true, reduceCtorEq] at h
  | false => simp only [hc] at h ⊢; exact h

/-- **Generic `foldlM` env-threading.** A monadic left-fold whose state pairs an
    accumulator with a `TEnv`, where every successful step (a) preserves the type
    context, (b) refines the substitution (`absorbs`), (c) preserves well-formedness,
    (d) is monotone in the generator counter, and (e) establishes a per-element
    relation `R E_in E_out e` between its input and output envs, threads those facts to
    the whole fold: the final env preserves the start context, refines the start subst,
    stays well-formed, is gen-monotone, and for every element there are input/output
    envs (the input sharing the start context) with `R` holding and the final subst
    refining the output's. Abstract in the step `f` and relation `R` — no typechecker
    term, no hardcoded type. -/
theorem Statement.typeCheckAux_go_funcDecl_inv
    (P : Program) (op : Option Procedure)
    (C : LContext CoreLParams) (Env : TEnv Unit)
    (decl : PureFunc Expression) (md : Imperative.MetaData Expression)
    (srest acc : List Statement) (labels : List String)
    (ss' : List Statement) (Env' : TEnv Unit) (C' : LContext CoreLParams)
    (h_goeq : Statement.typeCheckAux.go P op C Env (.funcDecl decl md :: srest) acc labels
      = .ok (ss', Env', C')) :
    ∃ (func0 func : Function) (Env_mid : TEnv Unit) (decl' : PureFunc Expression),
      decl.isRecursive = false ∧
      Function.ofPureFunc decl = .ok func0 ∧
      Function.typeCheck C Env func0 = .ok (func, Env_mid) ∧
      Statement.typeCheckAux.go P op (C.addFactoryFunction func) Env_mid srest
        (.funcDecl decl' md :: acc) labels = .ok (ss', Env', C') := by
  unfold Statement.typeCheckAux.go at h_goeq
  simp only [Bind.bind, Except.bind, tryCatchThe, tryCatch, MonadExcept.tryCatch,
    MonadExceptOf.tryCatch, Except.tryCatch] at h_goeq
  cases h_rec : decl.isRecursive with
  | true => rw [h_rec] at h_goeq; simp only [if_true, reduceCtorEq] at h_goeq
  | false =>
    rw [h_rec] at h_goeq
    simp only [if_false, Bool.false_eq_true] at h_goeq
    cases h_pf : PureFunc.typeCheck C Env decl with
    | error e =>
      rw [h_pf] at h_goeq
      simp only [Except.mapError, pure, Except.pure, reduceCtorEq] at h_goeq
    | ok v =>
      obtain ⟨decl', func, Env_mid⟩ := v
      rw [h_pf] at h_goeq
      simp only [Except.mapError] at h_goeq
      -- Decompose `PureFunc.typeCheck` into `ofPureFunc` and `Function.typeCheck`.
      unfold PureFunc.typeCheck at h_pf
      simp only [Bind.bind, Except.bind] at h_pf
      cases h_of : Function.ofPureFunc decl with
      | error e => rw [h_of] at h_pf; simp only [reduceCtorEq] at h_pf
      | ok func0 =>
        rw [h_of] at h_pf
        simp only at h_pf
        cases h_ft : Function.typeCheck C Env func0 with
        | error e => rw [h_ft] at h_pf; simp only [reduceCtorEq] at h_pf
        | ok w =>
          obtain ⟨func', Env2⟩ := w
          rw [h_ft] at h_pf
          simp only [Except.ok.injEq, Prod.mk.injEq] at h_pf
          obtain ⟨h_decl'_eq, h_func_eq, h_env_eq⟩ := h_pf
          subst h_func_eq
          subst h_env_eq
          refine ⟨func0, func', Env2, decl', rfl, rfl, h_ft, ?_⟩
          exact h_goeq

theorem foldlM_env_threading {Acc Elt : Type}
    (f : (Acc × TEnv Unit) → Elt → Except DiagnosticModel (Acc × TEnv Unit))
    (R : TEnv Unit → TEnv Unit → Elt → Prop)
    (h_step : ∀ acc E e acc' E', TEnvWF (T := CoreLParams) E → E.context.types ≠ [] →
      f (acc, E) e = .ok (acc', E') →
      E'.context = E.context ∧
      Subst.absorbs E'.stateSubstInfo.subst E.stateSubstInfo.subst ∧
      TEnvWF (T := CoreLParams) E' ∧
      E'.genEnv.genState.tyGen ≥ E.genEnv.genState.tyGen ∧ R E E' e)
    (l : List Elt) (acc_start : Acc) (E_start E_end : TEnv Unit) (acc_end : Acc)
    (h_wf : TEnvWF (T := CoreLParams) E_start) (h_ne : E_start.context.types ≠ [])
    (h_fold : List.foldlM f (acc_start, E_start) l = .ok (acc_end, E_end)) :
    E_end.context = E_start.context ∧
    Subst.absorbs E_end.stateSubstInfo.subst E_start.stateSubstInfo.subst ∧
    TEnvWF (T := CoreLParams) E_end ∧
    E_end.genEnv.genState.tyGen ≥ E_start.genEnv.genState.tyGen ∧
    (∀ e, e ∈ l → ∃ E_in E_out, TEnvWF (T := CoreLParams) E_in ∧
      E_in.context = E_start.context ∧
      Subst.absorbs E_end.stateSubstInfo.subst E_out.stateSubstInfo.subst ∧ R E_in E_out e) := by
  induction l generalizing acc_start E_start with
  | nil =>
    simp only [List.foldlM_nil, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h_fold
    obtain ⟨_, h_eq⟩ := h_fold
    subst h_eq
    exact ⟨rfl, Subst.absorbs_refl _ E_start.stateSubstInfo.isWF, h_wf, Nat.le_refl _, by
      intro e h_mem; exact absurd h_mem (List.not_mem_nil)⟩
  | cons hd tl ih =>
    rw [List.foldlM_cons] at h_fold
    simp only [Bind.bind, Except.bind] at h_fold
    -- Peel the head step.
    cases h_hd : f (acc_start, E_start) hd with
    | error e => rw [h_hd] at h_fold; simp only [reduceCtorEq] at h_fold
    | ok st1 =>
      obtain ⟨acc1, E1⟩ := st1
      rw [h_hd] at h_fold
      simp only at h_fold
      obtain ⟨h_ctx1, h_abs1, h_wf1, h_gen1, h_R_hd⟩ :=
        h_step acc_start E_start hd acc1 E1 h_wf h_ne h_hd
      -- The next start env keeps a non-empty type scope (context preserved).
      have h_ne1 : E1.context.types ≠ [] := by rw [h_ctx1]; exact h_ne
      -- Recurse on the tail from `E1`.
      obtain ⟨h_ctx_t, h_abs_t, h_wf_t, h_gen_t, h_tail⟩ := ih acc1 E1 h_wf1 h_ne1 h_fold
      refine ⟨h_ctx_t.trans h_ctx1,
        Subst.absorbs_trans _ _ _ h_abs1 h_abs_t,
        h_wf_t, Nat.le_trans h_gen1 h_gen_t, ?_⟩
      intro e h_mem
      rw [List.mem_cons] at h_mem
      cases h_mem with
      | inl h_eq =>
        subst h_eq
        -- Head: input `E_start` (WF), output `E1`; tail threading refines `E1`'s subst.
        exact ⟨E_start, E1, h_wf, rfl, h_abs_t, h_R_hd⟩
      | inr h_mem_t =>
        obtain ⟨E_in, E_out, h_wf_e, h_ctx_e, h_abs_e, h_R_e⟩ := h_tail e h_mem_t
        exact ⟨E_in, E_out, h_wf_e, h_ctx_e.trans h_ctx1, h_abs_e, h_R_e⟩

/-- Output-element threading for an append-only `foldlM` over `TEnv`: when each
    step appends exactly one output element satisfying `Q` (and preserves the
    context + WF so the next step's premises hold), every element of the final
    output list (started from `[]`) satisfies `Q`. Used for the loop invariant
    fold, whose `StmtHasTypeA` obligation ranges over the **output** invariant
    list (`it`), not the input `invariant₀`. -/
theorem foldlM_output_facts {OutElt Elt : Type}
    (f : List OutElt × TEnv Unit → Elt → Except DiagnosticModel (List OutElt × TEnv Unit))
    (Q : OutElt → Prop)
    (h_step : ∀ acc E e acc' E', TEnvWF (T := CoreLParams) E → E.context.types ≠ [] →
      TContext.AliasesResolved E.context →
      f (acc, E) e = .ok (acc', E') →
      E'.context = E.context ∧ TEnvWF (T := CoreLParams) E' ∧
        ∃ o, acc' = acc ++ [o] ∧ Q o)
    (l : List Elt) (acc_start out : List OutElt) (E_start E_end : TEnv Unit)
    (h_wf : TEnvWF (T := CoreLParams) E_start) (h_ne : E_start.context.types ≠ [])
    (h_res : TContext.AliasesResolved E_start.context)
    (h_fold : List.foldlM f (acc_start, E_start) l = .ok (out, E_end)) :
    ∀ o, o ∈ out → o ∈ acc_start ∨ Q o := by
  induction l generalizing acc_start E_start with
  | nil =>
    simp only [List.foldlM_nil, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h_fold
    obtain ⟨h_acc, _⟩ := h_fold
    subst h_acc
    intro o ho; left; exact ho
  | cons hd tl ih =>
    rw [List.foldlM_cons] at h_fold
    simp only [Bind.bind, Except.bind] at h_fold
    cases h_hd : f (acc_start, E_start) hd with
    | error e => rw [h_hd] at h_fold; simp only [reduceCtorEq] at h_fold
    | ok st1 =>
      obtain ⟨acc1, E1⟩ := st1
      rw [h_hd] at h_fold
      simp only at h_fold
      obtain ⟨h_ctx1, h_wf1, o, h_acc1, h_Qo⟩ :=
        h_step acc_start E_start hd acc1 E1 h_wf h_ne h_res h_hd
      have h_ne1 : E1.context.types ≠ [] := by rw [h_ctx1]; exact h_ne
      have h_res1 : TContext.AliasesResolved E1.context := by
        unfold TContext.AliasesResolved at h_res ⊢; rw [h_ctx1]; exact h_res
      have h_tail := ih acc1 E1 h_wf1 h_ne1 h_res1 h_fold
      intro o' ho'
      rcases h_tail o' ho' with h_in | h_q
      · rw [h_acc1, List.mem_append] at h_in
        rcases h_in with h_in | h_in
        · left; exact h_in
        · simp only [List.mem_singleton] at h_in; subst h_in; right; exact h_Qo
      · right; exact h_q

/-- The `ite`/`loop` guard-type dispatch succeeds only when the resolved monotype is
    exactly `bool`: from success, the scrutinee was `bool` and the bool-arm was taken. -/
theorem condty_bool_match_ok {α : Type} (ty : LMonoTy)
    (fb : Except DiagnosticModel α) (errf : LMonoTy → DiagnosticModel)
    (g : DiagnosticModel → DiagnosticModel) (r : α)
    (h : (match (match ty with
                 | .tcons "bool" [] => fb
                 | x => Except.error (errf x)) with
          | Except.ok a => Except.ok a
          | Except.error e => Except.error (g e)) = Except.ok r) :
    ty = .tcons "bool" [] ∧ fb = .ok r := by
  split at h
  · rename_i a heq
    have h_ar : a = r := by injection h
    subst h_ar
    split at heq
    · exact ⟨rfl, heq⟩
    · simp only [reduceCtorEq] at heq
  · simp only [reduceCtorEq] at h

/-- A `try`/`catch` wrapper that only rewrites the error payload (`catch e =>
    .error (g e)`) succeeds iff the wrapped computation succeeds with the same value.
    Used to peel the `loop`/`exit`/etc. `try … catch` shells. -/
theorem trycatch_ok {α : Type} (X : Except DiagnosticModel α)
    (g : DiagnosticModel → DiagnosticModel) (r : α)
    (h : (match X with
          | Except.ok a => Except.ok a
          | Except.error e => Except.error (g e)) = Except.ok r) :
    X = Except.ok r := by
  cases X with
  | ok a => simp only [Except.ok.injEq] at h; subst h; rfl
  | error e => simp only [reduceCtorEq] at h

/-- The `loop` guard-type dispatch (`if (ty != bool) then error else k`): success
    forces `ty = bool` and reduces to the else-branch `k`. The `!=`-then-`error`
    shape is the loop analogue of `condty_bool_match_ok`'s match shape. -/
theorem guard_bool_if_ok {α : Type} (ty : LMonoTy)
    (err : DiagnosticModel) (fb : Except DiagnosticModel α) (r : α)
    (h : (if (ty != LMonoTy.tcons "bool" []) = true then Except.error err else fb) = Except.ok r) :
    ty = LMonoTy.tcons "bool" [] ∧ fb = .ok r := by
  split at h
  · simp only [reduceCtorEq] at h
  · rename_i h_neg
    simp only [bne_iff_ne, ne_eq, Decidable.not_not] at h_neg
    exact ⟨h_neg, h⟩

/-- **Combined threading-preservation for a `go` run.** Running the `typeCheckAux` loop on
    `ss` (from input `C`/`Env`) to a result `(ss', Env', C')` preserves every invariant the
    soundness induction threads (`GoPreserved`). -/
theorem typeCheckAux_go_preserves (C : LContext CoreLParams) (Env : TEnv Unit)
    (P : Program) (op : Option Procedure) (ss acc : List Statement) (labels : List String)
    (ss' : List Statement) (Env' : TEnv Unit) (C' : LContext CoreLParams)
    (h : Statement.typeCheckAux.go P op C Env ss acc labels = .ok (ss', Env', C'))
    (h_wf : TEnvWF (T := CoreLParams) Env)
    (h_fwf : FactoryWF C.functions)
    (h_ne : Env.context.types ≠ [])
    (h_mono : ContextMono Env.context)
    (h_rigid_inv : ∀ v, v ∈ C.rigidTypeVars →
      LMonoTy.subst Env.stateSubstInfo.subst (.ftvar v) = .ftvar v)
    (h_closed : CalledProcsClosed P) :
    GoPreserved C C' Env Env' := by
  -- Mutual `go`/`goBlock` induction, both motives concluding `GoPreserved`. The output
  -- triple `(ss', Env', C')` is generalized (`∀`) inside each motive so the body IH can be
  -- instantiated at the inner `go` run's own output (which differs from the outer triple).
  refine (Statement.typeCheckAux.go.induct P op
    (motive1 := fun C Env ss acc labels =>
      ∀ ss' Env' C',
      Statement.typeCheckAux.go P op C Env ss acc labels = .ok (ss', Env', C') →
      TEnvWF (T := CoreLParams) Env → FactoryWF C.functions →
      Env.context.types ≠ [] → ContextMono Env.context →
      (∀ v, v ∈ C.rigidTypeVars →
        LMonoTy.subst Env.stateSubstInfo.subst (.ftvar v) = .ftvar v) →
      GoPreserved C C' Env Env')
    (motive2 := fun C Env bss acc labels =>
      ∀ ss' Env' C',
      Statement.typeCheckAux.goBlock P op C Env bss acc labels = .ok (ss', Env', C') →
      TEnvWF (T := CoreLParams) Env → FactoryWF C.functions →
      Env.context.types ≠ [] → ContextMono Env.context →
      (∀ v, v ∈ C.rigidTypeVars →
        LMonoTy.subst Env.stateSubstInfo.subst (.ftvar v) = .ftvar v) →
      GoPreserved C C' Env Env')
    ?case_nil ?case_cmd ?case_block_clash ?case_block ?case_ite ?case_loop
    ?case_exit ?case_funcDecl ?case_typeDecl ?case_goBlock
    C Env ss acc labels) ss' Env' C' h h_wf h_fwf h_ne h_mono h_rigid_inv
  case case_nil =>
    intro C₀ Env₀ acc₀ labels₀ ss'₀ Env'₀ C'₀ h₀ hwf₀ hfwf₀ hne₀ hmono₀ hrigid₀
    -- `go … [] …` returns `(acc.reverse, Env₀, C₀)`, so `Env'₀ = Env₀`, `C'₀ = C₀`.
    simp only [Statement.typeCheckAux.go, Except.ok.injEq, Prod.mk.injEq] at h₀
    obtain ⟨_, hEnv, hC⟩ := h₀
    subst hEnv; subst hC
    exact ⟨hwf₀, hfwf₀, hne₀, hmono₀,
      Subst.absorbs_refl _ Env₀.stateSubstInfo.isWF, rfl, hrigid₀, rfl, rfl, Nat.le_refl _⟩
  case case_cmd =>
    intro C₀ Env₀ acc₀ labels₀ srest₀ cmd₀ ih ss'₀ Env'₀ C'₀ h₀ hwf₀ hfwf₀ hne₀ hmono₀ hrigid₀
    simp only [Statement.typeCheckAux.go, Bind.bind, Except.bind] at h₀
    -- The `cmd` step: `typeCheckCmd C₀ Env₀ P cmd₀ = ok (c', Env_mid)`, `C` unchanged.
    cases h_tc : Statement.typeCheckCmd C₀ Env₀ P cmd₀ with
    | error e => rw [h_tc] at h₀; simp at h₀
    | ok v =>
      obtain ⟨c', Env_mid⟩ := v
      rw [h_tc] at h₀
      simp only at h₀
      -- Head preservation from the command-level lemma (C₀ unchanged by commands).
      obtain ⟨h_wf_mid, h_ne_mid, h_mono_mid, h_abs_mid, h_rigid_mid, h_pop_mid, h_al_mid, h_gen_mid⟩ :=
        typeCheckCmd_preserves C₀ Env₀ P cmd₀ c' Env_mid h_tc hwf₀ hfwf₀ hne₀ hmono₀ hrigid₀ h_closed
      have h_head : GoPreserved C₀ C₀ Env₀ Env_mid :=
        ⟨h_wf_mid, hfwf₀, h_ne_mid, h_mono_mid, h_abs_mid, rfl, h_rigid_mid,
          h_pop_mid, h_al_mid, h_gen_mid⟩
      -- Tail via IH (now instantiated at the generalized output triple). `C` unchanged.
      have h_tail := ih (Stmt.cmd c') Env_mid C₀ ss'₀ Env'₀ C'₀ h₀ h_wf_mid hfwf₀ h_ne_mid h_mono_mid h_rigid_mid
      exact h_head.trans h_tail
  case case_block_clash =>
    intro C₀ Env₀ acc₀ labels₀ srest₀ label₀ bss₀ md₀ h_clash ih_tail ih_block
      ss'₀ Env'₀ C'₀ h_goeq hwf₀ hfwf₀ hne₀ hmono₀ hrigid₀
    -- The label clashes, so the `block` head `throw`s; `go = ok` is contradictory.
    rw [Statement.typeCheckAux.go] at h_goeq
    simp only [h_clash, if_true, Bind.bind, Except.bind] at h_goeq
    exact absurd h_goeq (by simp)
  case case_block =>
    intro C₀ Env₀ acc₀ labels₀ srest₀ label₀ bss₀ md₀ h_noclash ih_tail ih_block
      ss'₀ Env'₀ C'₀ h_goeq hwf₀ hfwf₀ hne₀ hmono₀ hrigid₀
    -- `block` (no label clash): `(bss', Env_blk, C₀) ← goBlock …; go C₀ Env_blk srest (s'::acc)`.
    rw [Statement.typeCheckAux.go] at h_goeq
    simp only [h_noclash, if_false, Bool.false_eq_true, Bind.bind, Except.bind] at h_goeq
    cases h_blk : Statement.typeCheckAux.goBlock P op C₀ Env₀ bss₀ [] (label₀ :: labels₀) with
    | error e => rw [h_blk] at h_goeq; simp [pure, Except.pure] at h_goeq
    | ok v =>
      obtain ⟨bss', Env_blk, C_blk⟩ := v
      rw [h_blk] at h_goeq
      simp only [pure, Except.pure] at h_goeq
      -- Head: the block (`goBlock`) preserves the invariants and returns the input `C₀`.
      have h_head : GoPreserved C₀ C_blk Env₀ Env_blk :=
        ih_block bss' Env_blk C_blk h_blk hwf₀ hfwf₀ hne₀ hmono₀ hrigid₀
      -- `goBlock` returns the input `C₀` as its `C`-output.
      have h_Cblk : C_blk = C₀ := by
        have h_blk' := h_blk
        unfold Statement.typeCheckAux.goBlock at h_blk'
        simp only [Bind.bind, Except.bind] at h_blk'
        cases h_run : Statement.typeCheckAux.go P op C₀ Env₀.pushEmptyContext bss₀ [] (label₀ :: labels₀) with
        | error e => rw [h_run] at h_blk'; simp only [reduceCtorEq] at h_blk'
        | ok w =>
          obtain ⟨w1, w2, w3⟩ := w
          rw [h_run] at h_blk'
          simp only [Except.ok.injEq, Prod.mk.injEq] at h_blk'
          exact h_blk'.2.2.symm
      subst h_Cblk
      -- Tail via IH from the block's output env.
      have h_tail := ih_tail (Stmt.block label₀ bss' md₀) Env_blk C_blk ss'₀ Env'₀ C'₀ h_goeq
        h_head.wf h_head.fwf h_head.ne h_head.mono h_head.rigid_inv
      exact h_head.trans h_tail
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
            -- `rigid_inv` at `Env_r` from `checkAnnotCompat`; this lifts the guard
            -- resolve to a `GoPreserved` head.
            have h_rigid_r : ∀ w, w ∈ C₀.rigidTypeVars →
                LMonoTy.subst Env_r.stateSubstInfo.subst (.ftvar w) = .ftvar w :=
              CmdType.checkAnnotCompat_rigid C₀ Env_r h_cac
            have h_res_pres : GoPreserved C₀ C₀ Env₀ Env_r :=
              resolve_GoPreserved C₀ Env₀ Env_r c conda h_res hwf₀ hfwf₀ hne₀ hmono₀ h_rigid_r
            -- Then-block run: the branch IH gives its `GoPreserved` directly.
            cases h_t : Statement.typeCheckAux.goBlock P op C₀ Env_r tss₀ [] labels₀ with
            | error e => rw [h_t] at h_blocks; simp only [reduceCtorEq] at h_blocks
            | ok vt =>
              obtain ⟨tss', Env_t, C_t⟩ := vt
              rw [h_t] at h_blocks
              simp only at h_blocks
              have h_t_pres : GoPreserved C₀ C_t Env_r Env_t :=
                ih_then Env_r tss' Env_t C_t h_t h_res_pres.wf h_res_pres.fwf h_res_pres.ne
                  h_res_pres.mono h_res_pres.rigid_inv
              have h_Ct : C_t = C₀ := goBlock_returns_input_C P op C₀ C_t Env_r Env_t tss₀ [] labels₀ tss' h_t
              rw [h_Ct] at h_t_pres h_blocks
              -- Else-block run from `Env_t`.
              cases h_e : Statement.typeCheckAux.goBlock P op C₀ Env_t ess₀ [] labels₀ with
              | error e => rw [h_e] at h_blocks; simp only [reduceCtorEq] at h_blocks
              | ok ve =>
                obtain ⟨ess', Env_e, C_e⟩ := ve
                rw [h_e] at h_blocks
                simp only [Except.ok.injEq] at h_blocks
                have h_e_pres : GoPreserved C₀ C_e Env_t Env_e :=
                  ih_else Env_t C₀ ess' Env_e C_e h_e h_t_pres.wf h_t_pres.fwf h_t_pres.ne
                    h_t_pres.mono h_t_pres.rigid_inv
                have h_Ce : C_e = C₀ := goBlock_returns_input_C P op C₀ C_e Env_t Env_e ess₀ [] labels₀ ess' h_e
                rw [h_Ce] at h_e_pres
                -- `h_blocks : (ite-stmt, Env_e, C₀) = v`, so the tail `go` runs from `Env_e`.
                subst h_blocks
                simp only at h_goeq
                rw [h_Ce] at h_goeq
                have h_tail : GoPreserved C₀ C'₀ Env_e Env'₀ :=
                  ih_tail (Stmt.ite (.det (unresolved conda)) tss' ess' md₀) Env_e C₀
                    ss'₀ Env'₀ C'₀ h_goeq h_e_pres.wf h_e_pres.fwf h_e_pres.ne h_e_pres.mono
                    h_e_pres.rigid_inv
                exact (h_res_pres.trans h_t_pres).trans (h_e_pres.trans h_tail)
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
          have h_t_pres : GoPreserved C₀ C_t Env₀ Env_t :=
            ih_then tss' Env_t C_t h_t hwf₀ hfwf₀ hne₀ hmono₀ hrigid₀
          have h_Ct : C_t = C₀ := goBlock_returns_input_C P op C₀ C_t Env₀ Env_t tss₀ [] labels₀ tss' h_t
          rw [h_Ct] at h_t_pres h_e
          have h_e_pres : GoPreserved C₀ C_e Env_t Env_e :=
            ih_else Env_t C₀ ess' Env_e C_e h_e h_t_pres.wf h_t_pres.fwf h_t_pres.ne
              h_t_pres.mono h_t_pres.rigid_inv
          have h_Ce : C_e = C₀ := goBlock_returns_input_C P op C₀ C_e Env_t Env_e ess₀ [] labels₀ ess' h_e
          rw [h_Ce] at h_e_pres h_goeq
          have h_tail : GoPreserved C₀ C'₀ Env_e Env'₀ :=
            ih_tail (Stmt.ite .nondet tss' ess' md₀) Env_e C₀ ss'₀ Env'₀ C'₀ h_goeq
              h_e_pres.wf h_e_pres.fwf h_e_pres.ne h_e_pres.mono h_e_pres.rigid_inv
          exact (h_t_pres.trans h_e_pres).trans h_tail
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
      -- Guard threading.
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
      -- Measure threading (and gen monotonicity).
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
      -- The measure-type dispatch and the loop-body goBlock.
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
      -- Invariant-fold threading (start env `Env_m`).
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
      -- `checkAnnotCompat` forces rigid identity at `Env_inv`.
      have h_rigid_inv : ∀ w, w ∈ C₀.rigidTypeVars →
          LMonoTy.subst Env_inv.stateSubstInfo.subst (.ftvar w) = .ftvar w :=
        CmdType.checkAnnotCompat_rigid C₀ Env_inv cac_eq
      -- Context recovery: `Env_inv ≡ Env_m ≡ Env_g ≡ Env₀`.
      have h_ctx_inv0 : Env_inv.context = Env₀.context := by
        rw [h_ctx_inv, h_ctx_m, h_ctx_g]
      have h_ne_inv : Env_inv.context.types ≠ [] := by rw [h_ctx_inv0]; exact hne₀
      have h_mono_inv : ContextMono Env_inv.context := by rw [h_ctx_inv0]; exact hmono₀
      -- Head `GoPreserved C₀ C₀ Env₀ Env_inv` (guard + measure + invariant resolves).
      have h_head : GoPreserved C₀ C₀ Env₀ Env_inv := by
        refine ⟨h_wf_inv, hfwf₀, h_ne_inv, h_mono_inv, ?_, rfl, h_rigid_inv, ?_, ?_, ?_⟩
        · -- absorbs: chain `Env_inv ⊒ Env_m ⊒ Env_g ⊒ Env₀`.
          exact Subst.absorbs_trans _ _ _ h_abs_g
            (Subst.absorbs_trans _ _ _ h_abs_m h_abs_inv)
        · -- types_pop: contexts all equal.
          rw [h_ctx_inv0]
        · rw [h_ctx_inv0]
        · -- tyGen: chain `Env_inv ≥ Env_m ≥ Env_g ≥ Env₀`.
          exact Nat.le_trans h_gen_g (Nat.le_trans h_gen_m h_gen_inv)
      -- Body block run: the body IH gives its `GoPreserved` directly; returns input `C₀`.
      have h_body_pres : GoPreserved C₀ C_loop Env_inv Env_loop :=
        ih_body Env_inv tb Env_loop C_loop h_gb_eq h_wf_inv hfwf₀ h_ne_inv h_mono_inv h_rigid_inv
      have h_Cloop : C_loop = C₀ :=
        goBlock_returns_input_C P op C₀ C_loop Env_inv Env_loop bss₀ [] labels₀ tb h_gb_eq
      rw [h_Cloop] at h_body_pres h_goeq
      -- Tail run from `Env_loop`.
      have h_tail : GoPreserved C₀ C'₀ Env_loop Env'₀ :=
        ih_tail (Stmt.loop (ExprOrNondet.det (unresolved ga)) (Option.map unresolved mtOpt)
            (List.map (fun x => (x.fst, unresolved x.snd)) it) tb md₀) Env_loop C₀
          ss'₀ Env'₀ C'₀ h_goeq h_body_pres.wf h_body_pres.fwf h_body_pres.ne h_body_pres.mono
          h_body_pres.rigid_inv
      exact (h_head.trans h_body_pres).trans h_tail
    | nondet =>
      simp only [pure, Except.pure] at h_body
      -- The guard is nondet: `pure (none, Env₀)`, so no guard resolve.
      elim_err h_body with mres mres_eq
      obtain ⟨mtOpt, Env_m⟩ := mres
      elim_err h_body with fres fres_eq
      obtain ⟨it, Env_inv⟩ := fres
      elim_err h_body with cac_v cac_eq
      simp only at fres_eq cac_eq h_body
      -- Measure threading from `Env₀` (and gen monotonicity).
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
      have h_head : GoPreserved C₀ C₀ Env₀ Env_inv := by
        refine ⟨h_wf_inv, hfwf₀, h_ne_inv, h_mono_inv, ?_, rfl, h_rigid_inv, ?_, ?_, ?_⟩
        · exact Subst.absorbs_trans _ _ _ h_abs_m h_abs_inv
        · rw [h_ctx_inv0]
        · rw [h_ctx_inv0]
        · exact Nat.le_trans h_gen_m h_gen_inv
      have h_body_pres : GoPreserved C₀ C_loop Env_inv Env_loop :=
        ih_body Env_inv tb Env_loop C_loop h_gb_eq h_wf_inv hfwf₀ h_ne_inv h_mono_inv h_rigid_inv
      have h_Cloop : C_loop = C₀ :=
        goBlock_returns_input_C P op C₀ C_loop Env_inv Env_loop bss₀ [] labels₀ tb h_gb_eq
      rw [h_Cloop] at h_body_pres h_goeq
      have h_tail : GoPreserved C₀ C'₀ Env_loop Env'₀ :=
        ih_tail (Stmt.loop ExprOrNondet.nondet (Option.map unresolved mtOpt)
            (List.map (fun x => (x.fst, unresolved x.snd)) it) tb md₀) Env_loop C₀
          ss'₀ Env'₀ C'₀ h_goeq h_body_pres.wf h_body_pres.fwf h_body_pres.ne h_body_pres.mono
          h_body_pres.rigid_inv
      exact (h_head.trans h_body_pres).trans h_tail
  case case_exit =>
    intro C₀ Env₀ acc₀ labels₀ srest₀ l₀ md₀ ih_tail ss'₀ Env'₀ C'₀ h_goeq hwf₀ hfwf₀ hne₀ hmono₀ hrigid₀
    -- The `exit` head leaves `Env`/`C` unchanged; the whole step is the tail IH.
    unfold Statement.typeCheckAux.go at h_goeq
    simp only [Bind.bind, Except.bind, tryCatchThe, tryCatch, MonadExcept.tryCatch,
      MonadExceptOf.tryCatch, Except.tryCatch] at h_goeq
    -- Case on `op` and the label check; only `op = some ∧ label match` produces
    -- `ok`, leaving the head output `(exit, Env₀, C₀)` and recursing on `srest`.
    cases op with
    | none => simp only [reduceCtorEq] at h_goeq
    | some proc =>
      by_cases h_lbl : labels₀.contains l₀
      · simp only [h_lbl, if_true] at h_goeq
        exact ih_tail (Stmt.exit l₀ md₀) Env₀ C₀ ss'₀ Env'₀ C'₀ h_goeq hwf₀ hfwf₀ hne₀ hmono₀ hrigid₀
      · simp only [h_lbl, if_false, Bool.false_eq_true, reduceCtorEq] at h_goeq
  case case_funcDecl =>
    intro C₀ Env₀ acc₀ labels₀ srest₀ decl₀ md₀ ih_tail ss'₀ Env'₀ C'₀ h_goeq hwf₀ hfwf₀ hne₀ hmono₀ hrigid₀
    -- The head runs `PureFunc.typeCheck` = `ofPureFunc` + `Function.typeCheck`, then adds
    -- the checked function to `C` via `addFactoryFunction`. S0 inverts the `go` success.
    obtain ⟨func0, func, Env_mid, decl', h_rec, h_of, h_ft, h_tail_eq⟩ :=
      Statement.typeCheckAux_go_funcDecl_inv P op C₀ Env₀ decl₀ md₀ srest₀ acc₀ labels₀
        ss'₀ Env'₀ C'₀ h_goeq
    -- Head `GoPreserved C₀ (addFactoryFunction func) Env₀ Env_mid` from the A-lemmas.
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
      · -- rigid_inv at Env_mid's subst: the checker's rigid-refinement guard fixes the
        -- output subst on rigid vars (body branch); bodiless keeps the input subst.
        exact Function.typeCheck_preserves_rigid_inv C₀ Env₀ func0 func Env_mid h_ft hwf₀ hfwf₀ hrigid₀
      · rw [h_ctx]
      · rw [h_ctx]
    -- Tail via IH at `C_mid = addFactoryFunction func`, `Env_mid`.
    have h_rigid_mid : ∀ v, v ∈ (C₀.addFactoryFunction func).rigidTypeVars →
        LMonoTy.subst Env_mid.stateSubstInfo.subst (.ftvar v) = .ftvar v := by
      rw [addFactoryFunction_rigidTypeVars]; exact h_head.rigid_inv
    have h_tail : GoPreserved (C₀.addFactoryFunction func) C'₀ Env_mid Env'₀ :=
      ih_tail (Stmt.funcDecl decl' md₀) Env_mid (C₀.addFactoryFunction func) ss'₀ Env'₀ C'₀
        h_tail_eq h_head.wf h_head.fwf h_head.ne h_head.mono h_rigid_mid
    exact h_head.trans h_tail
  case case_typeDecl =>
    intro C₀ Env₀ acc₀ labels₀ srest₀ tc₀ md₀ ih_tail ss'₀ Env'₀ C'₀ h_goeq hwf₀ hfwf₀ hne₀ hmono₀ hrigid₀
    unfold Statement.typeCheckAux.go at h_goeq
    simp only [Bind.bind, Except.bind, tryCatchThe, tryCatch, MonadExcept.tryCatch,
      MonadExceptOf.tryCatch, Except.tryCatch] at h_goeq
    -- The head adds a known type: `addKnownTypeWithError → ok C_mid`, `Env` unchanged.
    cases h_add : C₀.addKnownTypeWithError { name := tc₀.name, metadata := tc₀.numargs }
        (md₀.toDiagnosticF (Std.format "Type '" ++ Std.format tc₀.name ++ Std.format "' is already declared")) with
    | error e => rw [h_add] at h_goeq; simp only [reduceCtorEq] at h_goeq
    | ok C_mid =>
      rw [h_add] at h_goeq
      simp only at h_goeq
      -- `addKnownTypeWithError` preserves `functions` and `rigidTypeVars`.
      obtain ⟨h_fns, h_rig⟩ := addKnownTypeWithError_preserves C₀ C_mid _ _ h_add
      -- Head `GoPreserved`: `Env` unchanged, `C` only gains a known type.
      have h_head : GoPreserved C₀ C_mid Env₀ Env₀ :=
        ⟨hwf₀, h_fns ▸ hfwf₀, hne₀, hmono₀,
          Subst.absorbs_refl _ Env₀.stateSubstInfo.isWF, h_rig, hrigid₀, rfl, rfl, Nat.le_refl _⟩
      have h_tail := ih_tail (Stmt.typeDecl tc₀ md₀) Env₀ C_mid ss'₀ Env'₀ C'₀ h_goeq hwf₀ (h_fns ▸ hfwf₀)
        hne₀ hmono₀ (by rw [h_rig]; exact hrigid₀)
      exact h_head.trans h_tail
  case case_goBlock =>
    intro C₀ Env₀ bss₀ acc₀ labels₀ Env₁ ih_body ss'₀ Env'₀ C'₀ h_goeq hwf₀ hfwf₀ hne₀ hmono₀ hrigid₀
    -- `goBlock` = `push; (bss', Env_body, C_body) ← go C₀ (push Env₀) bss₀ acc₀ labels₀;
    --             ok (bss', Env_body.popContext, C₀)`.
    unfold Statement.typeCheckAux.goBlock at h_goeq
    simp only [Bind.bind, Except.bind] at h_goeq
    cases h_body_run : Statement.typeCheckAux.go P op C₀ Env₀.pushEmptyContext bss₀ acc₀ labels₀ with
    | error e => rw [h_body_run] at h_goeq; simp only [reduceCtorEq] at h_goeq
    | ok v =>
      obtain ⟨bss', Env_body, C_body⟩ := v
      rw [h_body_run] at h_goeq
      simp only [Except.ok.injEq, Prod.mk.injEq] at h_goeq
      obtain ⟨_, hEnv, hC⟩ := h_goeq
      subst hEnv; subst hC
      -- `pushEmptyContext` preserves the threading premises needed by the body IH.
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
      -- Body sub-derivation via the body IH (motive1) at the body's actual output.
      have h_body : GoPreserved C₀ C_body Env₀.pushEmptyContext Env_body :=
        ih_body bss' Env_body C_body h_body_run h_push_wf hfwf₀ h_push_ne h_push_mono h_push_rigid
      -- Pop the body's innermost scope; recovers the input context.
      exact goBlock_GoPreserved h_body hwf₀ hfwf₀ hne₀ hmono₀

/-- **Block context recovery.** A successful `goBlock` returns an environment whose
    `context` is exactly the input `Env`'s context: the body runs under
    `pushEmptyContext` and the result is `popContext`-ed, and (structurally, no
    well-scoping) the body's `go` run preserves the `types` stack-tail and `aliases`,
    so the pushed scope pops off cleanly. -/
theorem goBlock_preserves_context (P : Program) (op : Option Procedure)
    (C : LContext CoreLParams) (Env : TEnv Unit) (bss : List Statement) (acc : List Statement)
    (labels : List String) (bss' : List Statement) (Env_blk : TEnv Unit) (C_blk : LContext CoreLParams)
    (h : Statement.typeCheckAux.goBlock P op C Env bss acc labels = .ok (bss', Env_blk, C_blk))
    (h_wf : TEnvWF (T := CoreLParams) Env)
    (h_fwf : FactoryWF C.functions)
    (h_mono : ContextMono Env.context)
    (h_rigid_inv : ∀ v, v ∈ C.rigidTypeVars →
      LMonoTy.subst Env.stateSubstInfo.subst (.ftvar v) = .ftvar v)
    (h_closed : CalledProcsClosed P) :
    Env_blk.context = Env.context := by
  -- `goBlock` runs the body then `popContext`s; the result's context equals input.
  have h' := h
  unfold Statement.typeCheckAux.goBlock at h'
  simp only [Bind.bind, Except.bind] at h'
  cases h_run : Statement.typeCheckAux.go P op C Env.pushEmptyContext bss acc labels with
  | error e => rw [h_run] at h'; simp only [reduceCtorEq] at h'
  | ok w =>
    obtain ⟨w1, Env_body, w3⟩ := w
    rw [h_run] at h'
    simp only [Except.ok.injEq, Prod.mk.injEq] at h'
    obtain ⟨_, h_envblk, _⟩ := h'
    -- `Env_blk = Env_body.popContext`.
    rw [← h_envblk]
    have h_push_wf : TEnvWF (T := CoreLParams) Env.pushEmptyContext :=
      pushEmptyContext_TEnvWF Env h_wf
    have h_push_ne : Env.pushEmptyContext.context.types ≠ [] := by
      simp only [TEnv.pushEmptyContext, TEnv.updateContext, TEnv.context, Maps.push]
      exact List.cons_ne_nil _ _
    have h_push_mono : ContextMono Env.pushEmptyContext.context :=
      pushEmptyContext_ContextMono Env h_mono
    have h_body_pres : GoPreserved C w3 Env.pushEmptyContext Env_body :=
      typeCheckAux_go_preserves C Env.pushEmptyContext P op bss acc labels
        w1 Env_body w3 h_run h_push_wf h_fwf h_push_ne h_push_mono h_rigid_inv h_closed
    -- The pop recovers the input context (same reasoning as `goBlock_GoPreserved`).
    have h_pop_types : (Env_body.popContext).context.types = Env.context.types := by
      have h_push_pop : Maps.pop Env.pushEmptyContext.context.types = Env.context.types := by
        simp only [TEnv.pushEmptyContext, TEnv.updateContext, TEnv.context, Maps.push, Maps.pop]
      have h_pop_def : (Env_body.popContext).context.types = Maps.pop Env_body.context.types := by
        simp only [TEnv.popContext, TEnv.updateContext, TEnv.context]
      rw [h_pop_def, h_body_pres.types_pop, h_push_pop]
    have h_pop_aliases : (Env_body.popContext).context.aliases = Env.context.aliases := by
      have h_pop_al : (Env_body.popContext).context.aliases = Env_body.context.aliases := by
        simp only [TEnv.popContext, TEnv.updateContext, TEnv.context]
      have h_push_al : Env.pushEmptyContext.context.aliases = Env.context.aliases := by
        simp only [TEnv.pushEmptyContext, TEnv.updateContext, TEnv.context]
      rw [h_pop_al, h_body_pres.aliases_eq, h_push_al]
    have h_eq : ∀ (a b : TContext Unit), a.types = b.types → a.aliases = b.aliases → a = b := by
      intro a b ht ha; cases a; cases b; simp_all
    exact h_eq _ _ h_pop_types h_pop_aliases

/-- **Block step preservation.** A successful `goBlock` preserves all `GoPreserved`
    invariants and returns the *input* `LContext` (block-local declarations do not
    leak). Reusable head-`GoPreserved` for `block`/`ite`/`loop`: the body runs under
    `pushEmptyContext`, the inner `go` preserves invariants (`typeCheckAux_go_preserves`),
    and `goBlock_GoPreserved` recovers the input context after `popContext`. -/
theorem goBlock_eq_GoPreserved (P : Program) (op : Option Procedure)
    (C : LContext CoreLParams) (Env : TEnv Unit) (bss : List Statement) (acc : List Statement)
    (labels : List String) (bss' : List Statement) (Env_blk : TEnv Unit) (C_blk : LContext CoreLParams)
    (h : Statement.typeCheckAux.goBlock P op C Env bss acc labels = .ok (bss', Env_blk, C_blk))
    (h_wf : TEnvWF (T := CoreLParams) Env)
    (h_fwf : FactoryWF C.functions)
    (h_ne : Env.context.types ≠ [])
    (h_mono : ContextMono Env.context)
    (h_rigid_inv : ∀ v, v ∈ C.rigidTypeVars →
      LMonoTy.subst Env.stateSubstInfo.subst (.ftvar v) = .ftvar v)
    (h_closed : CalledProcsClosed P) :
    GoPreserved C C Env Env_blk ∧ C_blk = C := by
  have h' := h
  unfold Statement.typeCheckAux.goBlock at h'
  simp only [Bind.bind, Except.bind] at h'
  cases h_run : Statement.typeCheckAux.go P op C Env.pushEmptyContext bss acc labels with
  | error e => rw [h_run] at h'; simp only [reduceCtorEq] at h'
  | ok w =>
    obtain ⟨w1, Env_body, w3⟩ := w
    rw [h_run] at h'
    simp only [Except.ok.injEq, Prod.mk.injEq] at h'
    obtain ⟨_, h_envblk, h_Cblk⟩ := h'
    have h_push_wf : TEnvWF (T := CoreLParams) Env.pushEmptyContext :=
      pushEmptyContext_TEnvWF Env h_wf
    have h_push_ne : Env.pushEmptyContext.context.types ≠ [] := by
      simp only [TEnv.pushEmptyContext, TEnv.updateContext, TEnv.context, Maps.push]
      exact List.cons_ne_nil _ _
    have h_push_mono : ContextMono Env.pushEmptyContext.context :=
      pushEmptyContext_ContextMono Env h_mono
    have h_body_pres : GoPreserved C w3 Env.pushEmptyContext Env_body :=
      typeCheckAux_go_preserves C Env.pushEmptyContext P op bss acc labels
        w1 Env_body w3 h_run h_push_wf h_fwf h_push_ne h_push_mono h_rigid_inv h_closed
    refine ⟨?_, h_Cblk.symm⟩
    rw [← h_envblk]
    exact goBlock_GoPreserved h_body_pres h_wf h_fwf h_ne h_mono

/-! ### Γ-congruence lift to the statement spec relations

The `_sound` block/branch/loop cases need to convert a body typing derived under the
*pushed* `Γ` (`[]::Γ₀`, from `goBlock`'s `pushEmptyContext`) into one under the *plain*
`Γ₀`. The two agree exactly on `Γ.types.find?` (`pushEmptyContext_find?`) and `aliases`.
The expression-layer congruence is `HasType.find_congr`; here we lift it through the
`CmdHasType'`/`CmdExtHasType'`/`StmtHasType'`/`StmtsHasType'` relations. Each lift is
**output-congruent**: it produces an output `Γ₂'` agreeing with `Γ₁'` on `find?`/`aliases`
(the only Γ-mutating constructors — `init` and the binder cases — insert the *same*
binding on both sides). The lifts are generic over the `ExprTypingSpec`, taking an
`exprTyped`-congruence hypothesis so both Part I (`HasType.find_congr`) and Part II
(`HasTypeA` ignores Γ) reuse them. -/

/-- `CmdHasType'` is Γ-congruent (output-congruent), given expression-layer congruence. -/
theorem CmdHasType'_find_congr {τ : Type} [S : ExprTypingSpec τ]
    {C : LContext CoreLParams} {Γ₁ Γ₁' : TContext Unit} {c : Cmd Expression}
    (h_expr_congr : ∀ (Γa Γb : TContext Unit) e t,
      (∀ x, Γb.types.find? x = Γa.types.find? x) → Γb.aliases = Γa.aliases →
      S.exprTyped C Γa e t → S.exprTyped C Γb e t)
    (h : CmdHasType' (τ := τ) C Γ₁ c Γ₁') :
    ∀ (Γ₂ : TContext Unit),
      (∀ x, Γ₂.types.find? x = Γ₁.types.find? x) → Γ₂.aliases = Γ₁.aliases →
      ∃ Γ₂', (∀ x, Γ₂'.types.find? x = Γ₁'.types.find? x) ∧ Γ₂'.aliases = Γ₁'.aliases ∧
        CmdHasType' (τ := τ) C Γ₂ c Γ₂' := by
  -- `induction` fixes the input index as `Γ₁`; case binders are the constructor's
  -- remaining explicit args + hypotheses (no leading `Γ`).
  induction h with
  | init_det x xty e mty tys md h_find h_notin h_len h_rigid h_e =>
    intro Γ₂ h_eq h_al
    -- Output inserts `(x, forAll [] mty)` into the newest scope; do the same on `Γ₂`.
    refine ⟨{ Γ₂ with types := Γ₂.types.insert x (.forAll [] mty) }, ?_, h_al, ?_⟩
    · -- The extended outputs agree on `find?`.
      intro y
      by_cases h_xy : y = x
      · rw [h_xy]
        show (Maps.insert Γ₂.types x _).find? x = (Maps.insert Γ₁.types x _).find? x
        rw [Maps.find?_insert_self, Maps.find?_insert_self]
      · show (Maps.insert Γ₂.types x _).find? y = (Maps.insert Γ₁.types x _).find? y
        rw [Maps.find?_insert_ne _ _ _ _ h_xy, Maps.find?_insert_ne _ _ _ _ h_xy]; exact h_eq y
    · exact CmdHasType'.init_det Γ₂ x xty e mty tys md (by rw [h_eq]; exact h_find) h_notin h_len
        (by rw [h_al]; exact h_rigid) (h_expr_congr Γ₁ Γ₂ e _ h_eq h_al h_e)
  | init_nondet x xty mty tys md h_find h_len h_rigid =>
    intro Γ₂ h_eq h_al
    refine ⟨{ Γ₂ with types := Γ₂.types.insert x (.forAll [] mty) }, ?_, h_al, ?_⟩
    · intro y
      by_cases h_xy : y = x
      · rw [h_xy]
        show (Maps.insert Γ₂.types x _).find? x = (Maps.insert Γ₁.types x _).find? x
        rw [Maps.find?_insert_self, Maps.find?_insert_self]
      · show (Maps.insert Γ₂.types x _).find? y = (Maps.insert Γ₁.types x _).find? y
        rw [Maps.find?_insert_ne _ _ _ _ h_xy, Maps.find?_insert_ne _ _ _ _ h_xy]; exact h_eq y
    · exact CmdHasType'.init_nondet Γ₂ x xty mty tys md (by rw [h_eq]; exact h_find) h_len
        (by rw [h_al]; exact h_rigid)
  | set_det x mty e md h_find h_e =>
    intro Γ₂ h_eq h_al
    exact ⟨Γ₂, h_eq, h_al, CmdHasType'.set_det Γ₂ x mty e md (by rw [h_eq]; exact h_find)
      (h_expr_congr Γ₁ Γ₂ e _ h_eq h_al h_e)⟩
  | set_nondet x mty md h_find =>
    intro Γ₂ h_eq h_al
    exact ⟨Γ₂, h_eq, h_al, CmdHasType'.set_nondet Γ₂ x mty md (by rw [h_eq]; exact h_find)⟩
  | assert l e md h_e =>
    intro Γ₂ h_eq h_al
    exact ⟨Γ₂, h_eq, h_al, CmdHasType'.assert Γ₂ l e md (h_expr_congr Γ₁ Γ₂ e _ h_eq h_al h_e)⟩
  | assume l e md h_e =>
    intro Γ₂ h_eq h_al
    exact ⟨Γ₂, h_eq, h_al, CmdHasType'.assume Γ₂ l e md (h_expr_congr Γ₁ Γ₂ e _ h_eq h_al h_e)⟩
  | cover l e md h_e =>
    intro Γ₂ h_eq h_al
    exact ⟨Γ₂, h_eq, h_al, CmdHasType'.cover Γ₂ l e md (h_expr_congr Γ₁ Γ₂ e _ h_eq h_al h_e)⟩

/-- `CmdExtHasType'` is Γ-congruent (output-congruent), given expression-layer
    congruence. The `cmd` case delegates to `CmdHasType'_find_congr`; the `call` case
    has fixed output Γ and transports each premise (which reads `find?`/`aliases`/
    `exprTyped`) along the agreement. -/
theorem CmdExtHasType'_find_congr {τ : Type} [S : ExprTypingSpec τ]
    {C : LContext CoreLParams} {P : Program} {Γ₁ Γ₁' : TContext Unit} {c : Command}
    (h_expr_congr : ∀ (Γa Γb : TContext Unit) e t,
      (∀ x, Γb.types.find? x = Γa.types.find? x) → Γb.aliases = Γa.aliases →
      S.exprTyped C Γa e t → S.exprTyped C Γb e t)
    (h : CmdExtHasType' (τ := τ) C P Γ₁ c Γ₁') :
    ∀ (Γ₂ : TContext Unit),
      (∀ x, Γ₂.types.find? x = Γ₁.types.find? x) → Γ₂.aliases = Γ₁.aliases →
      ∃ Γ₂', (∀ x, Γ₂'.types.find? x = Γ₁'.types.find? x) ∧ Γ₂'.aliases = Γ₁'.aliases ∧
        CmdExtHasType' (τ := τ) C P Γ₂ c Γ₂' := by
  induction h with
  | cmd Γ' cc h_cmd =>
    intro Γ₂ h_eq h_al
    obtain ⟨Γ₂', h_eq', h_al', h_cmd'⟩ := CmdHasType'_find_congr h_expr_congr h_cmd Γ₂ h_eq h_al
    exact ⟨Γ₂', h_eq', h_al', CmdExtHasType'.cmd Γ₂ Γ₂' cc h_cmd'⟩
  | call pname callArgs proc md σ h_find h_il h_ol h_lhs h_inp h_out h_io =>
    intro Γ₂ h_eq h_al
    -- Output Γ = input Γ; transport every premise along the `find?`/`aliases` agreement.
    refine ⟨Γ₂, h_eq, h_al, CmdExtHasType'.call Γ₂ pname callArgs proc md σ h_find h_il h_ol
      ?_ ?_ ?_ h_io⟩
    · -- LHS variables exist in context (uses `find?`).
      intro v hv; rw [h_eq]; exact h_lhs v hv
    · -- Input positions (mixes `find?` and `exprTyped`, both transported).
      intro i hi hj
      obtain ⟨mty, h_ae, h_match⟩ := h_inp i hi hj
      refine ⟨mty, by rw [h_al]; exact h_ae, ?_⟩
      -- The match scrutinee is identical on both sides; split and transport each arm.
      split at h_match
      · -- `fvar _ _ none` arm: a context lookup, transported by `find?` agreement.
        rw [h_eq]; exact h_match
      · -- general arm: a self-typing expression, transported by `exprTyped` congruence.
        exact h_expr_congr Γ₁ Γ₂ _ _ h_eq h_al h_match
    · -- LHS types (uses `find?` + `aliases`).
      intro i hi hj
      obtain ⟨mty, h_ae, h_find_lhs⟩ := h_out i hi hj
      exact ⟨mty, by rw [h_al]; exact h_ae, by rw [h_eq]; exact h_find_lhs⟩

/-- `FuncHasType'` is Γ-congruent: two type-scopes agreeing pointwise on `find?`
    and on `aliases` give the same function-typing judgement. Only `bodyTyped`/
    `measureTyped` mention `Γ` (through `funcContext`, which pushes the same formals
    scope on both sides), so the obligation reduces to `exprTyped` congruence on the
    extended contexts, discharged by `h_expr_congr`. -/
theorem FuncHasType'_find_congr {τ : Type} [S : ExprTypingSpec τ]
    (h_expr_congr : ∀ (Γa Γb : TContext Unit) (Cx : LContext CoreLParams) e t,
      (∀ x, Γb.types.find? x = Γa.types.find? x) → Γb.aliases = Γa.aliases →
      S.exprTyped Cx Γa e t → S.exprTyped Cx Γb e t)
    {C : LContext CoreLParams} {Γa Γb : TContext Unit} {func : Function}
    (h_eq : ∀ x, Γb.types.find? x = Γa.types.find? x)
    (h_al : Γb.aliases = Γa.aliases)
    (h : FuncHasType' τ C Γa func) :
    FuncHasType' τ C Γb func := by
  have h_ctx_find : ∀ x,
      (funcContext Γb func).types.find? x = (funcContext Γa func).types.find? x := by
    intro x
    simp only [funcContext, Maps.push, Maps.find?]
    cases hf : Map.find? (func.inputs.map (fun p => (p.1, LTy.forAll [] p.2))) x with
    | none => simp only []; exact h_eq x
    | some v => simp only []
  have h_ctx_al : (funcContext Γb func).aliases = (funcContext Γa func).aliases := by
    simp only [funcContext]; exact h_al
  exact {
    inputsNodup := h.inputsNodup
    typeArgsNodup := h.typeArgsNodup
    noUndeclaredVars := h.noUndeclaredVars
    bodyTyped := fun body h_body =>
      h_expr_congr _ _ C body _ h_ctx_find h_ctx_al (h.bodyTyped body h_body)
    measureTyped := fun m h_m h_nv =>
      h_expr_congr _ _ C m _ h_ctx_find h_ctx_al (h.measureTyped m h_m h_nv) }

/-- `StmtsHasType'` is Γ-congruent (output-congruent), given expression-layer
    congruence. Proved together with the `StmtHasType'` version via the mutual
    recursor. The only Γ-mutating statement (`cmd` whose `CmdHasType'.init` inserts a
    binding) threads the agreement through `CmdExtHasType'_find_congr`; block/ite/loop
    leave Γ unchanged; `cons` chains the head's output agreement into the tail. -/
theorem StmtsHasType'_find_congr {τ : Type} [S : ExprTypingSpec τ]
    {P : Program}
    {C C' : LContext CoreLParams} {Γ₁ Γ₁' : TContext Unit} {ss : List Statement}
    (h_expr_congr : ∀ (Γa Γb : TContext Unit) (Cx : LContext CoreLParams) e t,
      (∀ x, Γb.types.find? x = Γa.types.find? x) → Γb.aliases = Γa.aliases →
      S.exprTyped Cx Γa e t → S.exprTyped Cx Γb e t)
    (h : StmtsHasType' τ P C Γ₁ ss C' Γ₁') :
    ∀ (Γ₂ : TContext Unit),
      (∀ x, Γ₂.types.find? x = Γ₁.types.find? x) → Γ₂.aliases = Γ₁.aliases →
      ∃ Γ₂', (∀ x, Γ₂'.types.find? x = Γ₁'.types.find? x) ∧ Γ₂'.aliases = Γ₁'.aliases ∧
        StmtsHasType' τ P C Γ₂ ss C' Γ₂' := by
  refine StmtsHasType'.rec
    (motive_1 := fun Ca Γa s Ca' Γa' _ =>
      ∀ Γ₂, (∀ x, Γ₂.types.find? x = Γa.types.find? x) → Γ₂.aliases = Γa.aliases →
        ∃ Γ₂', (∀ x, Γ₂'.types.find? x = Γa'.types.find? x) ∧ Γ₂'.aliases = Γa'.aliases ∧
          StmtHasType' τ P Ca Γ₂ s Ca' Γ₂')
    (motive_2 := fun Ca Γa ss Ca' Γa' _ =>
      ∀ Γ₂, (∀ x, Γ₂.types.find? x = Γa.types.find? x) → Γ₂.aliases = Γa.aliases →
        ∃ Γ₂', (∀ x, Γ₂'.types.find? x = Γa'.types.find? x) ∧ Γ₂'.aliases = Γa'.aliases ∧
          StmtsHasType' τ P Ca Γ₂ ss Ca' Γ₂')
    ?cmd ?block ?ite_det ?ite_nondet ?loop ?exit ?funcDecl ?typeDecl ?nil ?cons h
  case cmd =>
    intro Ca Γa Γa' c h_cmd Γ₂ h_eq h_al
    obtain ⟨Γ₂', h_eq', h_al', h_cmd'⟩ :=
      CmdExtHasType'_find_congr (fun Γa Γb e t => h_expr_congr Γa Γb Ca e t) h_cmd Γ₂ h_eq h_al
    exact ⟨Γ₂', h_eq', h_al', StmtHasType'.cmd Ca Γ₂ Γ₂' c h_cmd'⟩
  case block =>
    intro Ca Γa C_body Γ_body label body md _ ih_body Γ₂ h_eq h_al
    obtain ⟨Γ_body', _, _, h_body'⟩ := ih_body Γ₂ h_eq h_al
    exact ⟨Γ₂, h_eq, h_al, StmtHasType'.block Ca Γ₂ C_body Γ_body' label body md h_body'⟩
  case ite_det =>
    intro Ca Γa C_t Γ_t C_e Γ_e cond thenb elseb md h_cond _ _ ih_t ih_e Γ₂ h_eq h_al
    obtain ⟨Γ_t', _, _, h_thenb'⟩ := ih_t Γ₂ h_eq h_al
    obtain ⟨Γ_e', _, _, h_elseb'⟩ := ih_e Γ₂ h_eq h_al
    exact ⟨Γ₂, h_eq, h_al, StmtHasType'.ite_det Ca Γ₂ C_t Γ_t' C_e Γ_e' cond thenb elseb md
      (h_expr_congr Γa Γ₂ Ca cond _ h_eq h_al h_cond) h_thenb' h_elseb'⟩
  case ite_nondet =>
    intro Ca Γa C_t Γ_t C_e Γ_e thenb elseb md _ _ ih_t ih_e Γ₂ h_eq h_al
    obtain ⟨Γ_t', _, _, h_thenb'⟩ := ih_t Γ₂ h_eq h_al
    obtain ⟨Γ_e', _, _, h_elseb'⟩ := ih_e Γ₂ h_eq h_al
    exact ⟨Γ₂, h_eq, h_al, StmtHasType'.ite_nondet Ca Γ₂ C_t Γ_t' C_e Γ_e' thenb elseb md
      h_thenb' h_elseb'⟩
  case loop =>
    intro Ca Γa C_body Γ_body guard measure invariants body md h_g h_m h_i _ ih_body Γ₂ h_eq h_al
    obtain ⟨Γ_body', _, _, h_body'⟩ := ih_body Γ₂ h_eq h_al
    refine ⟨Γ₂, h_eq, h_al, StmtHasType'.loop Ca Γ₂ C_body Γ_body' guard measure invariants body md
      ?_ ?_ ?_ h_body'⟩
    · intro g h_gd; exact h_expr_congr Γa Γ₂ Ca g _ h_eq h_al (h_g g h_gd)
    · intro m h_md; exact h_expr_congr Γa Γ₂ Ca m _ h_eq h_al (h_m m h_md)
    · intro p h_pmem; exact h_expr_congr Γa Γ₂ Ca p.2 _ h_eq h_al (h_i p h_pmem)
  case exit =>
    intro Ca Γa label md Γ₂ h_eq h_al
    exact ⟨Γ₂, h_eq, h_al, StmtHasType'.exit Ca Γ₂ label md⟩
  case funcDecl =>
    intro Ca Γa decl func md h_nrec h_func Γ₂ h_eq h_al
    have h_func₂ : FuncHasType' τ Ca Γ₂ func :=
      FuncHasType'_find_congr h_expr_congr h_eq h_al h_func
    exact ⟨Γ₂, h_eq, h_al, StmtHasType'.funcDecl Ca Γ₂ decl func md h_nrec h_func₂⟩
  case typeDecl =>
    intro Ca Ca' Γa tc md h_add Γ₂ h_eq h_al
    exact ⟨Γ₂, h_eq, h_al, StmtHasType'.typeDecl Ca Ca' Γ₂ tc md h_add⟩
  case nil =>
    intro Ca Γa Γ₂ h_eq h_al
    exact ⟨Γ₂, h_eq, h_al, StmtsHasType'.nil Ca Γ₂⟩
  case cons =>
    intro Ca Cb Cc Γa Γb Γc s ss _ _ ih_s ih_ss Γ₂ h_eq h_al
    obtain ⟨Γb', h_eqb, h_alb, h_s'⟩ := ih_s Γ₂ h_eq h_al
    obtain ⟨Γc', h_eqc, h_alc, h_ss'⟩ := ih_ss Γb' h_eqb h_alb
    exact ⟨Γc', h_eqc, h_alc, StmtsHasType'.cons Ca Cb Cc Γ₂ Γb' Γc' s ss h_s' h_ss'⟩

/-- **Bool-guard extraction.** A free-var-checked condition `c` that `resolve`s to a
    `bool`-typed expression is `HasType`-bool under any substitution `S` absorbing the resolve
    output's substitution. The expression-level obligation for `ite`/`loop` guards/invariants. -/
theorem resolve_bool_HasType (C : LContext CoreLParams) (Env Env' : TEnv Unit)
    (c : LExpr CoreLParams.mono) (conda : Lambda.LExprT CoreLParams.mono) (S : Subst)
    (msg : Std.Format)
    (h_fvc : Env.freeVarCheck c msg = .ok ())
    (h_resolve : LExpr.resolve C Env c = .ok (conda, Env'))
    (h_bool : conda.toLMonoTy = LMonoTy.bool)
    (h_wf : TEnvWF (T := CoreLParams) Env)
    (h_fwf : FactoryWF C.functions)
    (h_mono : ContextMono Env.context)
    (hS_abs : Subst.absorbs S Env'.stateSubstInfo.subst)
    (hS_wf : SubstWF S) :
    Lambda.LExpr.HasType (T := CoreLParams) C (TContext.subst Env.context S) c
      (.forAll [] .bool) := by
  have h_ws : WellScoped c Env.context := fun x hx =>
    Lambda.TEnv.freeVarCheck_implies_fvars_in_knownVars Env c msg h_fvc x hx
  have h_core := resolve_HasType_core c conda C Env Env' h_resolve h_wf h_fwf h_ws
  have h_pkf : Subst.polyKeysFresh (T := CoreLParams) S Env.context := by
    intro a _ x ty h_find h_bv
    exact absurd (h_mono x ty h_find) h_bv
  have h_ht := h_core.1 S hS_abs hS_wf h_pkf
  rw [h_bool, Lambda.LMonoTy.subst_bool] at h_ht
  exact h_ht

/-- `int` analogue of `resolve_bool_HasType`, used for the loop measure: lifts a
    resolve whose resolved monotype is `int` to `HasType … (.forAll [] .int)` under
    any absorbing, well-formed `S`. -/
theorem resolve_int_HasType (C : LContext CoreLParams) (Env Env' : TEnv Unit)
    (c : LExpr CoreLParams.mono) (conda : Lambda.LExprT CoreLParams.mono) (S : Subst)
    (msg : Std.Format)
    (h_fvc : Env.freeVarCheck c msg = .ok ())
    (h_resolve : LExpr.resolve C Env c = .ok (conda, Env'))
    (h_int : conda.toLMonoTy = LMonoTy.int)
    (h_wf : TEnvWF (T := CoreLParams) Env)
    (h_fwf : FactoryWF C.functions)
    (h_mono : ContextMono Env.context)
    (hS_abs : Subst.absorbs S Env'.stateSubstInfo.subst)
    (hS_wf : SubstWF S) :
    Lambda.LExpr.HasType (T := CoreLParams) C (TContext.subst Env.context S) c
      (.forAll [] .int) := by
  have h_ws : WellScoped c Env.context := fun x hx =>
    Lambda.TEnv.freeVarCheck_implies_fvars_in_knownVars Env c msg h_fvc x hx
  have h_core := resolve_HasType_core c conda C Env Env' h_resolve h_wf h_fwf h_ws
  have h_pkf : Subst.polyKeysFresh (T := CoreLParams) S Env.context := by
    intro a _ x ty h_find h_bv
    exact absurd (h_mono x ty h_find) h_bv
  have h_ht := h_core.1 S hS_abs hS_wf h_pkf
  rw [h_int, Lambda.LMonoTy.subst_int] at h_ht
  exact h_ht

/-- **Annotated bool extraction.** The `HasTypeA` analogue of `resolve_bool_HasType`
    for the output (substituted) expression: a `resolve` yielding a `bool`-typed `conda` gives
    `HasTypeA [] (conda.unresolved.applySubst S) .bool`. For the annotated `ite`/`loop` guards. -/
theorem resolve_bool_HasTypeA (C : LContext CoreLParams) (Env Env' : TEnv Unit)
    (c : LExpr CoreLParams.mono) (conda : Lambda.LExprT CoreLParams.mono) (S : Subst)
    (h_resolve : LExpr.resolve C Env c = .ok (conda, Env'))
    (h_bool : conda.toLMonoTy = LMonoTy.bool)
    (h_wf : TEnvWF (T := CoreLParams) Env)
    (h_fwf : FactoryWF C.functions)
    (h_resolved : TContext.AliasesResolved Env.context) :
    Lambda.LExpr.HasTypeA [] (conda.unresolved.applySubst S) .bool := by
  have h_hta := resolve_HasTypeA c conda C Env Env' h_resolve h_wf h_fwf h_resolved
  rw [h_bool] at h_hta
  have h_subst := applySubst_typeCheck S h_hta
  rw [Lambda.LMonoTy.subst_bool] at h_subst
  simpa using h_subst

/-- `int` analogue of `resolve_bool_HasTypeA`, for the loop measure. -/
theorem resolve_int_HasTypeA (C : LContext CoreLParams) (Env Env' : TEnv Unit)
    (c : LExpr CoreLParams.mono) (conda : Lambda.LExprT CoreLParams.mono) (S : Subst)
    (h_resolve : LExpr.resolve C Env c = .ok (conda, Env'))
    (h_int : conda.toLMonoTy = LMonoTy.int)
    (h_wf : TEnvWF (T := CoreLParams) Env)
    (h_fwf : FactoryWF C.functions)
    (h_resolved : TContext.AliasesResolved Env.context) :
    Lambda.LExpr.HasTypeA [] (conda.unresolved.applySubst S) .int := by
  have h_hta := resolve_HasTypeA c conda C Env Env' h_resolve h_wf h_fwf h_resolved
  rw [h_int] at h_hta
  have h_subst := applySubst_typeCheck S h_hta
  rw [Lambda.LMonoTy.subst_int] at h_subst
  simpa using h_subst

/-! ### Γ-bridge helpers for the funcDecl case -/

/-- If `S` fixes every free type variable of a monotype, `subst S mty = mty`. -/
theorem LMonoTy.subst_eq_self_of_fixes (S : Subst) (mty : LMonoTy)
    (h : ∀ v, v ∈ LMonoTy.freeVars mty → LMonoTy.subst S (.ftvar v) = .ftvar v) :
    LMonoTy.subst S mty = mty := by
  -- If `S` and the empty subst agree on `mty`'s free vars, they agree on `mty`; the
  -- empty subst is the identity, and `h` says `S` fixes each free var (= the empty
  -- subst's action). So `subst S mty = subst [] mty = mty`.
  induction mty with
  | ftvar x => exact h x (by simp [LMonoTy.freeVars])
  | bitvec n => rw [LMonoTy.subst_unfold]
  | tcons name args ih =>
    rw [LMonoTy.subst_unfold]
    simp only [LMonoTy.freeVars] at h
    show LMonoTy.tcons name (List.map (LMonoTy.subst S) args) = LMonoTy.tcons name args
    congr 1
    have h_map : List.map (LMonoTy.subst S) args = List.map id args := by
      apply List.map_congr_left
      intro a ha
      exact ih a ha (fun v hv => h v (LMonoTys.freeVars_mem_subset ha hv))
    rw [h_map, List.map_id]

/-- If `S` fixes every free type variable of an `LTy` that is `forAll []`, `subst S ty = ty`. -/
theorem LTy.subst_eq_self_of_fixes_mono (S : Subst) (ty : LTy)
    (h_mono : LTy.boundVars ty = [])
    (h : ∀ v, v ∈ LTy.freeVars ty → LMonoTy.subst S (.ftvar v) = .ftvar v) :
    LTy.subst S ty = ty := by
  cases ty with
  | forAll xs mty =>
    simp only [LTy.boundVars] at h_mono
    subst h_mono
    rw [LTy.subst_forAll_nil]
    congr 1
    apply LMonoTy.subst_eq_self_of_fixes
    intro v hv
    apply h
    simpa [LTy.freeVars, List.removeAll] using hv

/-- The Γ-bridge helper: if every ambient binding of `Γ` is monomorphic and has
    only rigid free vars (fixed by `S`), then `subst Γ S` agrees with `Γ` on `find?`. -/
theorem subst_context_find_congr_of_ambient (Γ : TContext Unit) (S : Subst)
    (C : LContext CoreLParams)
    (h_ambient_mono : ∀ ty ∈ Maps.values Γ.types, LTy.boundVars ty = [])
    (h_ambient_rigid : ∀ x ty, Γ.types.find? x = some ty →
      ∀ v ∈ LTy.freeVars ty, v ∈ C.rigidTypeVars)
    (h_rigid : ∀ v, v ∈ C.rigidTypeVars → LMonoTy.subst S (.ftvar v) = .ftvar v)
    (x : CoreIdent) :
    (TContext.subst Γ S).types.find? x = Γ.types.find? x := by
  cases h_find : Γ.types.find? x with
  | none => rw [TContext.subst_find_none Γ S x h_find]
  | some ty =>
    rw [TContext.subst_find_some Γ S x ty h_find]
    have h_mono : LTy.boundVars ty = [] :=
      h_ambient_mono ty (Maps.find?_mem_values Γ.types h_find)
    have h_fix : ∀ v, v ∈ LTy.freeVars ty → LMonoTy.subst S (.ftvar v) = .ftvar v :=
      fun v hv => h_rigid v (h_ambient_rigid x ty h_find v hv)
    rw [LTy.subst_eq_self_of_fixes_mono S ty h_mono h_fix]


/-- Unannotated soundness for the `go` loop of `typeCheckAux`. The accumulator
    `acc` only affects the *output statement list*, not the `(C, Env)` threading,
    so the relation is stated on the remaining `ss`. The relation uses the
    **final** substitution `Env'.stateSubstInfo.subst` on every threaded context
    (cf. the `Cmd` layer); intermediate contexts are `subst _ S_final`. -/
theorem typeCheckAux_go_sound (C : LContext CoreLParams) (Env : TEnv Unit)
    (P : Program) (op : Option Procedure) (ss acc : List Statement) (labels : List String)
    (ss' : List Statement) (Env' : TEnv Unit) (C' : LContext CoreLParams)
    (h : Statement.typeCheckAux.go P op C Env ss acc labels = .ok (ss', Env', C'))
    (h_wf : TEnvWF (T := CoreLParams) Env)
    (h_fwf : FactoryWF C.functions)
    (h_ne : Env.context.types ≠ [])
    (h_mono : ContextMono Env.context)
    -- Well-formedness antecedents threaded to the `funcDecl` case, where they discharge
    -- `Function.typeCheck_HasType_output`'s hypotheses. All are monotone invariants
    -- preserved by every `go` step.
    (h_resolved : TContext.AliasesResolved Env.context)
    (h_aliases_not_known : ∀ a ∈ Env.context.aliases, a.name ≠ "arrow")
    (h_ali_nd : AliasesNonDropping Env.context.aliases)
    (h_arrow_wf : ArrowKnownBinary C)
    (h_ambient_rigid : ∀ x ty, Env.context.types.find? x = some ty →
      ∀ v ∈ LTy.freeVars ty, v ∈ C.rigidTypeVars)
    (h_ambient_mono : ∀ ty ∈ Maps.values Env.context.types, LTy.boundVars ty = [])
    (h_rigid_inv : ∀ v, v ∈ C.rigidTypeVars →
      LMonoTy.subst Env.stateSubstInfo.subst (.ftvar v) = .ftvar v)
    (h_closed : CalledProcsClosed P) :
    StmtsHasType P C (TContext.subst Env.context Env'.stateSubstInfo.subst) ss
      C' (TContext.subst Env'.context Env'.stateSubstInfo.subst) := by
  -- The final-subst rigid-fixing premise (to instantiate the motive at `S = Env'.subst`)
  -- comes from `GoPreserved.rigid_inv` of the whole run.
  have h_rigid_inv_final : ∀ v, v ∈ C.rigidTypeVars →
      LMonoTy.subst Env'.stateSubstInfo.subst (.ftvar v) = .ftvar v :=
    (typeCheckAux_go_preserves C Env P op ss acc labels ss' Env' C'
      h h_wf h_fwf h_ne h_mono h_rigid_inv h_closed).rigid_inv
  -- Motives are generalized over any substitution `S` absorbing the run's output subst
  -- (cf. `typeCheckCmd_sound_gen`); the theorem is the `S = Env'.subst` instance. This lets
  -- the `cons`/`block` assembly type at the whole-run final subst, not the per-step one.
  -- motive2 (goBlock) binds the body output context existentially (a declaring body changes `Γ`).
  refine (Statement.typeCheckAux.go.induct P op
    (motive1 := fun C Env ss acc labels =>
      ∀ ss' Env' C',
      Statement.typeCheckAux.go P op C Env ss acc labels = .ok (ss', Env', C') →
      TEnvWF (T := CoreLParams) Env → FactoryWF C.functions →
      Env.context.types ≠ [] → ContextMono Env.context →
      TContext.AliasesResolved Env.context →
      (∀ a ∈ Env.context.aliases, a.name ≠ "arrow") →
      AliasesNonDropping Env.context.aliases →
      ArrowKnownBinary C →
      (∀ x ty, Env.context.types.find? x = some ty →
        ∀ v ∈ LTy.freeVars ty, v ∈ C.rigidTypeVars) →
      (∀ ty ∈ Maps.values Env.context.types, LTy.boundVars ty = []) →
      (∀ v, v ∈ C.rigidTypeVars →
        LMonoTy.subst Env.stateSubstInfo.subst (.ftvar v) = .ftvar v) →
      ∀ S, Subst.absorbs S Env'.stateSubstInfo.subst → SubstWF S →
        (∀ v, v ∈ C.rigidTypeVars → LMonoTy.subst S (.ftvar v) = .ftvar v) →
      StmtsHasType P C (TContext.subst Env.context S) ss
        C' (TContext.subst Env'.context S))
    (motive2 := fun C Env bss acc labels =>
      ∀ ss' Env' C',
      Statement.typeCheckAux.goBlock P op C Env bss acc labels = .ok (ss', Env', C') →
      TEnvWF (T := CoreLParams) Env → FactoryWF C.functions →
      Env.context.types ≠ [] → ContextMono Env.context →
      TContext.AliasesResolved Env.context →
      (∀ a ∈ Env.context.aliases, a.name ≠ "arrow") →
      AliasesNonDropping Env.context.aliases →
      ArrowKnownBinary C →
      (∀ x ty, Env.context.types.find? x = some ty →
        ∀ v ∈ LTy.freeVars ty, v ∈ C.rigidTypeVars) →
      (∀ ty ∈ Maps.values Env.context.types, LTy.boundVars ty = []) →
      (∀ v, v ∈ C.rigidTypeVars →
        LMonoTy.subst Env.stateSubstInfo.subst (.ftvar v) = .ftvar v) →
      ∀ S, Subst.absorbs S Env'.stateSubstInfo.subst → SubstWF S →
        (∀ v, v ∈ C.rigidTypeVars → LMonoTy.subst S (.ftvar v) = .ftvar v) →
      ∃ C_body Γ_body, StmtsHasType P C (TContext.subst Env.context S) bss
        C_body Γ_body)
    ?case_nil ?case_cmd ?case_block_clash ?case_block ?case_ite ?case_loop
    ?case_exit ?case_funcDecl ?case_typeDecl ?case_goBlock
    C Env ss acc labels) ss' Env' C' h h_wf h_fwf h_ne h_mono
    h_resolved h_aliases_not_known h_ali_nd h_arrow_wf h_ambient_rigid h_ambient_mono h_rigid_inv
    Env'.stateSubstInfo.subst (Subst.absorbs_refl _ Env'.stateSubstInfo.isWF)
    Env'.stateSubstInfo.isWF h_rigid_inv_final
  case case_nil =>
    intro C₀ Env₀ acc₀ labels₀ ss'₀ Env'₀ C'₀ h₀ hwf₀ hfwf₀ hne₀ hmono₀ _ _ _ _ _ _ hrigid₀ S hS_abs hS_wf hS_rigid
    -- `go … [] …` returns `(acc.reverse, Env₀, C₀)`, so `Env'₀ = Env₀`, `C'₀ = C₀`.
    simp only [Statement.typeCheckAux.go, Except.ok.injEq, Prod.mk.injEq] at h₀
    obtain ⟨_, hEnv, hC⟩ := h₀
    subst hEnv; subst hC
    exact StmtsHasType'.nil _ _
  case case_cmd =>
    intro C₀ Env₀ acc₀ labels₀ srest₀ cmd₀ ih ss'₀ Env'₀ C'₀ h₀ hwf₀ hfwf₀ hne₀ hmono₀
      hres₀ hakn₀ halnd₀ harrow₀ hamr₀ hamm₀ hrigid₀
      S hS_abs hS_wf hS_rigid
    simp only [Statement.typeCheckAux.go, Bind.bind, Except.bind] at h₀
    cases h_tc : Statement.typeCheckCmd C₀ Env₀ P cmd₀ with
    | error e => rw [h_tc] at h₀; simp at h₀
    | ok v =>
      obtain ⟨c', Env_mid⟩ := v
      rw [h_tc] at h₀
      simp only at h₀
      -- Threading: command-step preservation (head) + whole-tail preservation.
      obtain ⟨h_wf_mid, h_ne_mid, h_mono_mid, h_abs_mid, h_rigid_mid, _, h_al_mid, _⟩ :=
        typeCheckCmd_preserves C₀ Env₀ P cmd₀ c' Env_mid h_tc hwf₀ hfwf₀ hne₀ hmono₀ hrigid₀ h_closed
      -- Commands leave `C` and the alias list unchanged; ambient invariants preserved by
      -- the dedicated `typeCheckCmd_preserves_ambient_*` lemmas.
      have hres_mid : TContext.AliasesResolved Env_mid.context := by
        unfold TContext.AliasesResolved at hres₀ ⊢; rw [h_al_mid]; exact hres₀
      have hakn_mid : ∀ a ∈ Env_mid.context.aliases, a.name ≠ "arrow" := by
        rw [h_al_mid]; exact hakn₀
      have halnd_mid : AliasesNonDropping Env_mid.context.aliases := by
        rw [h_al_mid]; exact halnd₀
      have hamr_mid : ∀ x ty, Env_mid.context.types.find? x = some ty →
          ∀ v ∈ LTy.freeVars ty, v ∈ C₀.rigidTypeVars :=
        typeCheckCmd_preserves_ambient_rigid C₀ Env₀ P cmd₀ c' Env_mid h_tc hwf₀ hfwf₀ hne₀ hamr₀
      have hamm_mid : ∀ ty ∈ Maps.values Env_mid.context.types, LTy.boundVars ty = [] :=
        typeCheckCmd_preserves_ambient_mono C₀ Env₀ P cmd₀ c' Env_mid h_tc hwf₀ hfwf₀ hne₀ hamm₀
      have h_tail_pres : GoPreserved C₀ C'₀ Env_mid Env'₀ :=
        typeCheckAux_go_preserves C₀ Env_mid P op srest₀ (Stmt.cmd c' :: acc₀) labels₀
          ss'₀ Env'₀ C'₀ h₀ h_wf_mid hfwf₀ h_ne_mid h_mono_mid h_rigid_mid h_closed
      -- `S` absorbs the command's intermediate subst (S ⊒ Env'₀ ⊒ Env_mid).
      have h_abs_S_mid : Subst.absorbs S Env_mid.stateSubstInfo.subst :=
        Subst.absorbs_trans _ _ _ h_tail_pres.absorbs hS_abs
      -- Head obligation at `S` via the universal-`S` command theorem.
      have h_head_cmd : CmdExtHasType C₀ P (TContext.subst Env₀.context S)
          cmd₀ (TContext.subst Env_mid.context S) :=
        Command.typeCheckCmd_sound_gen C₀ Env₀ P cmd₀ c' Env_mid h_tc hwf₀ hfwf₀ hne₀ hmono₀
          (fun proc pname callArgs md h_eq h_find => h_closed pname proc h_find)
          S h_abs_S_mid hS_wf hS_rigid
      -- Tail obligation at `S` via the IH (commands leave `C` and rigid set unchanged).
      have h_tail := ih (Stmt.cmd c') Env_mid C₀ ss'₀ Env'₀ C'₀ h₀ h_wf_mid hfwf₀ h_ne_mid h_mono_mid
        hres_mid hakn_mid halnd_mid harrow₀ hamr_mid hamm_mid
        h_rigid_mid S hS_abs hS_wf hS_rigid
      exact StmtsHasType'.cons _ _ _ _ _ _ _ _ (StmtHasType'.cmd _ _ _ _ h_head_cmd) h_tail
  case case_block_clash =>
    intro C₀ Env₀ acc₀ labels₀ srest₀ label₀ bss₀ md₀ h_clash ih_tail ih_block
      ss'₀ Env'₀ C'₀ h_goeq hwf₀ hfwf₀ hne₀ hmono₀ _ _ _ _ _ _ hrigid₀
    -- The label clashes, so the `block` head `throw`s; `go = ok` is contradictory.
    rw [Statement.typeCheckAux.go] at h_goeq
    simp only [h_clash, if_true, Bind.bind, Except.bind] at h_goeq
    exact absurd h_goeq (by simp)
  case case_block =>
    intro C₀ Env₀ acc₀ labels₀ srest₀ label₀ bss₀ md₀ h_noclash ih_tail ih_block
      ss'₀ Env'₀ C'₀ h_goeq hwf₀ hfwf₀ hne₀ hmono₀ hres₀ hakn₀ halnd₀ harrow₀ hamr₀ hamm₀ hrigid₀ S hS_abs hS_wf hS_rigid
    -- `block` (no label clash): `(bss', Env_blk, C₀) ← goBlock …; go C₀ Env_blk srest (s'::acc)`.
    rw [Statement.typeCheckAux.go] at h_goeq
    simp only [h_noclash, if_false, Bool.false_eq_true, Bind.bind, Except.bind] at h_goeq
    cases h_blk : Statement.typeCheckAux.goBlock P op C₀ Env₀ bss₀ [] (label₀ :: labels₀) with
    | error e => rw [h_blk] at h_goeq; simp [pure, Except.pure] at h_goeq
    | ok v =>
      obtain ⟨bss', Env_blk, C_blk⟩ := v
      rw [h_blk] at h_goeq
      simp only [pure, Except.pure] at h_goeq
      -- `goBlock` returns the input `C₀` as its `C`-output.
      have h_Cblk : C_blk = C₀ := by
        have h_blk' := h_blk
        unfold Statement.typeCheckAux.goBlock at h_blk'
        simp only [Bind.bind, Except.bind] at h_blk'
        cases h_run : Statement.typeCheckAux.go P op C₀ Env₀.pushEmptyContext bss₀ [] (label₀ :: labels₀) with
        | error e => rw [h_run] at h_blk'; simp only [reduceCtorEq] at h_blk'
        | ok w =>
          obtain ⟨w1, w2, w3⟩ := w
          rw [h_run] at h_blk'
          simp only [Except.ok.injEq, Prod.mk.injEq] at h_blk'
          exact h_blk'.2.2.symm
      -- `goBlock` returns the input `C₀`; rewrite its output `C_blk` to `C₀` in the
      -- hypotheses that mention it (keeps `C₀`, the motive's fixed head input).
      rw [h_Cblk] at h_blk h_goeq
      -- The block step's output context equals the input (`goBlock_preserves_context`).
      have h_ctx_blk : Env_blk.context = Env₀.context :=
        goBlock_preserves_context P op C₀ Env₀ bss₀ [] (label₀ :: labels₀) bss' Env_blk C₀
          h_blk hwf₀ hfwf₀ hmono₀ hrigid₀ h_closed
      -- The block step preserves the threading invariants (head: `goBlock`'s `GoPreserved`).
      -- Derive it from the body run for the WF/ne/mono/rigid facts the tail IH needs.
      have h_blk_pres : GoPreserved C₀ C₀ Env₀ Env_blk := by
        have h_blk' := h_blk
        unfold Statement.typeCheckAux.goBlock at h_blk'
        simp only [Bind.bind, Except.bind] at h_blk'
        cases h_run : Statement.typeCheckAux.go P op C₀ Env₀.pushEmptyContext bss₀ [] (label₀ :: labels₀) with
        | error e => rw [h_run] at h_blk'; simp only [reduceCtorEq] at h_blk'
        | ok w =>
          obtain ⟨w1, Env_body, w3⟩ := w
          rw [h_run] at h_blk'
          simp only [Except.ok.injEq, Prod.mk.injEq] at h_blk'
          obtain ⟨_, h_envblk, _⟩ := h_blk'
          have h_push_wf : TEnvWF (T := CoreLParams) Env₀.pushEmptyContext :=
            pushEmptyContext_TEnvWF Env₀ hwf₀
          have h_push_ne : Env₀.pushEmptyContext.context.types ≠ [] := by
            simp only [TEnv.pushEmptyContext, TEnv.updateContext, TEnv.context, Maps.push]
            exact List.cons_ne_nil _ _
          have h_push_mono : ContextMono Env₀.pushEmptyContext.context :=
            pushEmptyContext_ContextMono Env₀ hmono₀
          have h_body_pres : GoPreserved C₀ w3 Env₀.pushEmptyContext Env_body :=
            typeCheckAux_go_preserves C₀ Env₀.pushEmptyContext P op bss₀ [] (label₀ :: labels₀)
              w1 Env_body w3 h_run h_push_wf hfwf₀ h_push_ne h_push_mono hrigid₀ h_closed
          -- `Env_blk = Env_body.popContext`.
          rw [← h_envblk]
          exact goBlock_GoPreserved h_body_pres hwf₀ hfwf₀ hne₀ hmono₀
      -- Tail preservation (`Env_blk → Env'₀`) gives `S ⊒ Env'₀ ⊒ Env_blk`.
      have h_tail_pres : GoPreserved C₀ C'₀ Env_blk Env'₀ :=
        typeCheckAux_go_preserves C₀ Env_blk P op srest₀ (Stmt.block label₀ bss' md₀ :: acc₀)
          labels₀ ss'₀ Env'₀ C'₀ h_goeq h_blk_pres.wf h_blk_pres.fwf h_blk_pres.ne h_blk_pres.mono
          h_blk_pres.rigid_inv h_closed
      have hS_abs_blk : Subst.absorbs S Env_blk.stateSubstInfo.subst :=
        Subst.absorbs_trans _ _ _ h_tail_pres.absorbs hS_abs
      -- The block head's body typing (existential body output) via `ih_block` (motive2) at `S`.
      -- Block leaves `Env.context` (`h_ctx_blk`) and `C₀` unchanged, so the well-formedness
      -- invariants re-establish at `Env_blk`/`C₀` by rewriting the context.
      have hres_blk : TContext.AliasesResolved Env_blk.context := by
        unfold TContext.AliasesResolved at hres₀ ⊢; rw [h_ctx_blk]; exact hres₀
      have hakn_blk : ∀ a ∈ Env_blk.context.aliases, a.name ≠ "arrow" := by
        rw [h_ctx_blk]; exact hakn₀
      have halnd_blk : AliasesNonDropping Env_blk.context.aliases := by
        rw [h_ctx_blk]; exact halnd₀
      have hamr_blk : ∀ x ty, Env_blk.context.types.find? x = some ty →
          ∀ v ∈ LTy.freeVars ty, v ∈ C₀.rigidTypeVars := by rw [h_ctx_blk]; exact hamr₀
      have hamm_blk : ∀ ty ∈ Maps.values Env_blk.context.types, LTy.boundVars ty = [] := by
        rw [h_ctx_blk]; exact hamm₀
      obtain ⟨C_body, Γ_body, h_body⟩ :=
        ih_block bss' Env_blk C₀ h_blk hwf₀ hfwf₀ hne₀ hmono₀ hres₀ hakn₀ halnd₀ harrow₀
          hamr₀ hamm₀ hrigid₀ S hS_abs_blk hS_wf hS_rigid
      -- Tail from the block's output env, at subst `S` (block leaves `C`/rigid unchanged).
      have h_tail := ih_tail (Stmt.block label₀ bss' md₀) Env_blk C₀ ss'₀ Env'₀ C'₀ h_goeq
        h_blk_pres.wf h_blk_pres.fwf h_blk_pres.ne h_blk_pres.mono
        hres_blk hakn_blk halnd_blk harrow₀ hamr_blk hamm_blk h_blk_pres.rigid_inv
        S hS_abs hS_wf hS_rigid
      -- The tail starts at `subst Env_blk.context S = subst Env₀.context S` (context recovery).
      rw [h_ctx_blk] at h_tail
      -- Assemble: head `StmtHasType'.block` (body existential) + tail.
      exact StmtsHasType'.cons _ _ _ _ _ _ _ _
        (StmtHasType'.block C₀ (TContext.subst Env₀.context S) C_body Γ_body label₀ bss₀ md₀ h_body)
        h_tail
  case case_ite =>
    intro C₀ Env₀ acc₀ labels₀ srest₀ cond₀ tss₀ ess₀ md₀ ih_tail ih_branches
      ss'₀ Env'₀ C'₀ h_goeq hwf₀ hfwf₀ hne₀ hmono₀ hres₀ hakn₀ halnd₀ harrow₀ hamr₀ hamm₀ hrigid₀ S hS_abs hS_wf hS_rigid
    unfold Statement.typeCheckAux.go at h_goeq
    simp only [Bind.bind, Except.bind, tryCatchThe, tryCatch, MonadExcept.tryCatch,
      MonadExceptOf.tryCatch, Except.tryCatch, Except.mapError] at h_goeq
    cases cond₀ with
    | det c =>
      simp only at h_goeq ih_branches
      obtain ⟨ih_then, ih_else⟩ := ih_branches
      -- Decompose `freeVarCheck` (payload unused), then `resolve`/`checkAnnotCompat`
      -- as named `cases` since their equations feed the resolve-soundness lemmas.
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
            -- Peel the tail-`go` bind (`elim_err` discards the error branch); `heq` is
            -- the `condty` try/catch result. `condty_bool_match_ok` extracts
            -- `condty = bool` and the bool-arm body without unfolding `bool`.
            elim_err h_goeq with v heq
            obtain ⟨h_condty, h_blocks⟩ :=
              condty_bool_match_ok conda.toLMonoTy _ _ _ v heq
            -- Resolve preserves the context and absorbs; `Env_r.context = Env₀.context`.
            have h_ctx_r : Env_r.context = Env₀.context :=
              resolve_preserves_context c conda C₀ Env₀ Env_r h_res hwf₀ hne₀ hfwf₀
            have h_abs_r : Subst.absorbs Env_r.stateSubstInfo.subst Env₀.stateSubstInfo.subst :=
              resolve_absorbs c conda C₀ Env₀ Env_r h_res hwf₀ hne₀ hfwf₀
            have h_wf_r : TEnvWF (T := CoreLParams) Env_r :=
              resolve_TEnvWF c conda C₀ Env₀ Env_r h_res hwf₀ hfwf₀
            have h_ne_r : Env_r.context.types ≠ [] := by rw [h_ctx_r]; exact hne₀
            have h_mono_r : ContextMono Env_r.context := by rw [h_ctx_r]; exact hmono₀
            -- `rigid_inv` at `Env_r`: `checkAnnotCompat` forces rigid identity.
            have h_rigid_r : ∀ v, v ∈ C₀.rigidTypeVars →
                LMonoTy.subst Env_r.stateSubstInfo.subst (.ftvar v) = .ftvar v :=
              CmdType.checkAnnotCompat_rigid C₀ Env_r h_cac
            -- Head step 1 (`then` block) from `Env_r` — decompose the bool-arm body.
            cases h_t : Statement.typeCheckAux.goBlock P op C₀ Env_r tss₀ [] labels₀ with
            | error e => rw [h_t] at h_blocks; simp only [reduceCtorEq] at h_blocks
            | ok vt =>
              obtain ⟨tss', Env_t, C_t⟩ := vt
              rw [h_t] at h_blocks
              simp only at h_blocks
              obtain ⟨h_t_pres, h_Ct⟩ := goBlock_eq_GoPreserved P op C₀ Env_r tss₀ [] labels₀
                tss' Env_t C_t h_t h_wf_r hfwf₀ h_ne_r h_mono_r h_rigid_r h_closed
              subst C_t
              have h_ctx_t : Env_t.context = Env_r.context :=
                goBlock_preserves_context P op C₀ Env_r tss₀ [] labels₀ tss' Env_t C₀
                  h_t h_wf_r hfwf₀ h_mono_r h_rigid_r h_closed
              -- Head step 2 (`else` block) from `Env_t`.
              cases h_e : Statement.typeCheckAux.goBlock P op C₀ Env_t ess₀ [] labels₀ with
              | error e => rw [h_e] at h_blocks; simp only [reduceCtorEq] at h_blocks
              | ok ve =>
                obtain ⟨ess', Env_e, C_e⟩ := ve
                rw [h_e] at h_blocks
                simp only [Except.ok.injEq] at h_blocks
                obtain ⟨h_e_pres, h_Ce⟩ := goBlock_eq_GoPreserved P op C₀ Env_t ess₀ [] labels₀
                  ess' Env_e C_e h_e h_t_pres.wf h_t_pres.fwf h_t_pres.ne h_t_pres.mono
                  h_t_pres.rigid_inv h_closed
                subst C_e
                -- `h_blocks : (ite-stmt, Env_e, C₀) = v`, so the tail `go` runs from `Env_e`.
                subst h_blocks
                simp only at h_goeq
                have h_ctx_e : Env_e.context = Env_t.context :=
                  goBlock_preserves_context P op C₀ Env_t ess₀ [] labels₀ ess' Env_e C₀
                    h_e h_t_pres.wf h_t_pres.fwf h_t_pres.mono h_t_pres.rigid_inv h_closed
                -- Tail run preservation (`Env_e → Env'₀`).
                have h_tail_pres : GoPreserved C₀ C'₀ Env_e Env'₀ :=
                  typeCheckAux_go_preserves C₀ Env_e P op srest₀
                    (Stmt.ite (.det (unresolved conda)) tss' ess' md₀ :: acc₀) labels₀
                    ss'₀ Env'₀ C'₀ h_goeq h_e_pres.wf h_e_pres.fwf h_e_pres.ne h_e_pres.mono
                    h_e_pres.rigid_inv h_closed
                -- `S ⊒ Env'₀ ⊒ Env_e ⊒ Env_t ⊒ Env_r`, chaining absorbs.
                have hS_abs_e : Subst.absorbs S Env_e.stateSubstInfo.subst :=
                  Subst.absorbs_trans _ _ _ h_tail_pres.absorbs hS_abs
                have hS_abs_t : Subst.absorbs S Env_t.stateSubstInfo.subst :=
                  Subst.absorbs_trans _ _ _ h_e_pres.absorbs hS_abs_e
                have hS_abs_r : Subst.absorbs S Env_r.stateSubstInfo.subst :=
                  Subst.absorbs_trans _ _ _ h_t_pres.absorbs hS_abs_t
                -- Condition typing at `S` via `resolve_bool_HasType`.
                have h_cond : Lambda.LExpr.HasType (T := CoreLParams) C₀
                    (TContext.subst Env₀.context S) c (.forAll [] .bool) :=
                  resolve_bool_HasType C₀ Env₀ Env_r c conda S _ h_fvc h_res h_condty
                    hwf₀ hfwf₀ hmono₀ hS_abs_r hS_wf
                -- Branch typings (existential body outputs) via the branch IHs at `S`.
                have hres_r : TContext.AliasesResolved Env_r.context := by
                  unfold TContext.AliasesResolved at hres₀ ⊢; rw [h_ctx_r]; exact hres₀
                have hakn_r : ∀ a ∈ Env_r.context.aliases, a.name ≠ "arrow" := by
                  rw [h_ctx_r]; exact hakn₀
                have halnd_r : AliasesNonDropping Env_r.context.aliases := by
                  rw [h_ctx_r]; exact halnd₀
                have hamr_r : ∀ x ty, Env_r.context.types.find? x = some ty →
                    ∀ v ∈ LTy.freeVars ty, v ∈ C₀.rigidTypeVars := by rw [h_ctx_r]; exact hamr₀
                have hamm_r : ∀ ty ∈ Maps.values Env_r.context.types, LTy.boundVars ty = [] := by
                  rw [h_ctx_r]; exact hamm₀
                obtain ⟨C_then, Γ_then, h_then⟩ :=
                  ih_then Env_r tss' Env_t C₀ h_t h_wf_r hfwf₀ h_ne_r h_mono_r
                    hres_r hakn_r halnd_r harrow₀ hamr_r hamm_r h_rigid_r
                    S hS_abs_t hS_wf hS_rigid
                have hres_t : TContext.AliasesResolved Env_t.context := by
                  unfold TContext.AliasesResolved at hres₀ ⊢; rw [h_ctx_t, h_ctx_r]; exact hres₀
                have hakn_t : ∀ a ∈ Env_t.context.aliases, a.name ≠ "arrow" := by
                  rw [h_ctx_t, h_ctx_r]; exact hakn₀
                have halnd_t : AliasesNonDropping Env_t.context.aliases := by
                  rw [h_ctx_t, h_ctx_r]; exact halnd₀
                have hamr_t : ∀ x ty, Env_t.context.types.find? x = some ty →
                    ∀ v ∈ LTy.freeVars ty, v ∈ C₀.rigidTypeVars := by rw [h_ctx_t, h_ctx_r]; exact hamr₀
                have hamm_t : ∀ ty ∈ Maps.values Env_t.context.types, LTy.boundVars ty = [] := by
                  rw [h_ctx_t, h_ctx_r]; exact hamm₀
                obtain ⟨C_else, Γ_else, h_else⟩ :=
                  ih_else Env_t C₀ ess' Env_e C₀ h_e h_t_pres.wf h_t_pres.fwf h_t_pres.ne
                    h_t_pres.mono hres_t hakn_t halnd_t harrow₀ hamr_t hamm_t h_t_pres.rigid_inv
                    S hS_abs_e hS_wf hS_rigid
                -- All intermediate contexts collapse to `Env₀.context` under `S`.
                rw [h_ctx_r] at h_then
                rw [h_ctx_t, h_ctx_r] at h_else
                -- Tail at `S`.
                have hres_e : TContext.AliasesResolved Env_e.context := by
                  unfold TContext.AliasesResolved at hres₀ ⊢; rw [h_ctx_e, h_ctx_t, h_ctx_r]; exact hres₀
                have hakn_e : ∀ a ∈ Env_e.context.aliases, a.name ≠ "arrow" := by
                  rw [h_ctx_e, h_ctx_t, h_ctx_r]; exact hakn₀
                have halnd_e : AliasesNonDropping Env_e.context.aliases := by
                  rw [h_ctx_e, h_ctx_t, h_ctx_r]; exact halnd₀
                have hamr_e : ∀ x ty, Env_e.context.types.find? x = some ty →
                    ∀ v ∈ LTy.freeVars ty, v ∈ C₀.rigidTypeVars := by
                  rw [h_ctx_e, h_ctx_t, h_ctx_r]; exact hamr₀
                have hamm_e : ∀ ty ∈ Maps.values Env_e.context.types, LTy.boundVars ty = [] := by
                  rw [h_ctx_e, h_ctx_t, h_ctx_r]; exact hamm₀
                have h_tail := ih_tail (Stmt.ite (.det (unresolved conda)) tss' ess' md₀) Env_e C₀
                  ss'₀ Env'₀ C'₀ h_goeq h_e_pres.wf h_e_pres.fwf h_e_pres.ne h_e_pres.mono
                  hres_e hakn_e halnd_e harrow₀ hamr_e hamm_e h_e_pres.rigid_inv S hS_abs hS_wf hS_rigid
                rw [h_ctx_e, h_ctx_t, h_ctx_r] at h_tail
                refine StmtsHasType'.cons _ _ _ _ _ _ _ _
                  (StmtHasType'.ite_det C₀ (TContext.subst Env₀.context S) C_then Γ_then C_else Γ_else
                    c tss₀ ess₀ md₀ ?_ h_then h_else) h_tail
                -- `S.exprTyped C Γ c (S.embed .bool)` = `HasType C Γ c (.forAll [] .bool)`.
                exact h_cond
    | nondet =>
      simp only at h_goeq ih_branches
      obtain ⟨ih_then, ih_else⟩ := ih_branches
      -- Decompose the two block runs and the tail `go`.
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
          -- Head step 1 (`then` block): preserves invariants, returns input `C₀`.
          obtain ⟨h_t_pres, h_Ct⟩ := goBlock_eq_GoPreserved P op C₀ Env₀ tss₀ [] labels₀
            tss' Env_t C_t h_t hwf₀ hfwf₀ hne₀ hmono₀ hrigid₀ h_closed
          subst C_t
          have h_ctx_t : Env_t.context = Env₀.context :=
            goBlock_preserves_context P op C₀ Env₀ tss₀ [] labels₀ tss' Env_t C₀
              h_t hwf₀ hfwf₀ hmono₀ hrigid₀ h_closed
          -- Head step 2 (`else` block): from `Env_t`, again returns `C₀`.
          obtain ⟨h_e_pres, h_Ce⟩ := goBlock_eq_GoPreserved P op C₀ Env_t ess₀ [] labels₀
            ess' Env_e C_e h_e h_t_pres.wf h_t_pres.fwf h_t_pres.ne h_t_pres.mono
            h_t_pres.rigid_inv h_closed
          subst C_e
          have h_ctx_e : Env_e.context = Env_t.context :=
            goBlock_preserves_context P op C₀ Env_t ess₀ [] labels₀ ess' Env_e C₀
              h_e h_t_pres.wf h_t_pres.fwf h_t_pres.mono h_t_pres.rigid_inv h_closed
          -- Tail run preservation (`Env_e → Env'₀`) for the `S`-absorption chain.
          have h_tail_pres : GoPreserved C₀ C'₀ Env_e Env'₀ :=
            typeCheckAux_go_preserves C₀ Env_e P op srest₀
              (Stmt.ite .nondet tss' ess' md₀ :: acc₀) labels₀ ss'₀ Env'₀ C'₀ h_goeq
              h_e_pres.wf h_e_pres.fwf h_e_pres.ne h_e_pres.mono h_e_pres.rigid_inv h_closed
          -- `S ⊒ Env'₀ ⊒ Env_e ⊒ Env_t`, so `S` absorbs each intermediate subst.
          have hS_abs_e : Subst.absorbs S Env_e.stateSubstInfo.subst :=
            Subst.absorbs_trans _ _ _ h_tail_pres.absorbs hS_abs
          have hS_abs_t : Subst.absorbs S Env_t.stateSubstInfo.subst :=
            Subst.absorbs_trans _ _ _ h_e_pres.absorbs hS_abs_e
          -- Branch typings (existential body outputs) via the branch IHs at `S`.
          obtain ⟨C_then, Γ_then, h_then⟩ :=
            ih_then tss' Env_t C₀ h_t hwf₀ hfwf₀ hne₀ hmono₀ hres₀ hakn₀ halnd₀ harrow₀ hamr₀ hamm₀
              hrigid₀ S hS_abs_t hS_wf hS_rigid
          have hres_t : TContext.AliasesResolved Env_t.context := by
            unfold TContext.AliasesResolved at hres₀ ⊢; rw [h_ctx_t]; exact hres₀
          have hakn_t : ∀ a ∈ Env_t.context.aliases, a.name ≠ "arrow" := by
            rw [h_ctx_t]; exact hakn₀
          have halnd_t : AliasesNonDropping Env_t.context.aliases := by rw [h_ctx_t]; exact halnd₀
          have hamr_t : ∀ x ty, Env_t.context.types.find? x = some ty →
              ∀ v ∈ LTy.freeVars ty, v ∈ C₀.rigidTypeVars := by rw [h_ctx_t]; exact hamr₀
          have hamm_t : ∀ ty ∈ Maps.values Env_t.context.types, LTy.boundVars ty = [] := by
            rw [h_ctx_t]; exact hamm₀
          obtain ⟨C_else, Γ_else, h_else⟩ :=
            ih_else Env_t C₀ ess' Env_e C₀ h_e h_t_pres.wf h_t_pres.fwf h_t_pres.ne h_t_pres.mono
              hres_t hakn_t halnd_t harrow₀ hamr_t hamm_t h_t_pres.rigid_inv S hS_abs_e hS_wf hS_rigid
          -- `ih_else` types `ess₀` from `subst Env_t.context S = subst Env₀.context S`.
          rw [h_ctx_t] at h_else
          -- Tail at `S` (block leaves `C`/rigid unchanged from `Env_e`).
          have hres_e : TContext.AliasesResolved Env_e.context := by
            unfold TContext.AliasesResolved at hres₀ ⊢; rw [h_ctx_e, h_ctx_t]; exact hres₀
          have hakn_e : ∀ a ∈ Env_e.context.aliases, a.name ≠ "arrow" := by
            rw [h_ctx_e, h_ctx_t]; exact hakn₀
          have halnd_e : AliasesNonDropping Env_e.context.aliases := by rw [h_ctx_e, h_ctx_t]; exact halnd₀
          have hamr_e : ∀ x ty, Env_e.context.types.find? x = some ty →
              ∀ v ∈ LTy.freeVars ty, v ∈ C₀.rigidTypeVars := by rw [h_ctx_e, h_ctx_t]; exact hamr₀
          have hamm_e : ∀ ty ∈ Maps.values Env_e.context.types, LTy.boundVars ty = [] := by
            rw [h_ctx_e, h_ctx_t]; exact hamm₀
          have h_tail := ih_tail (Stmt.ite .nondet tss' ess' md₀) Env_e C₀ ss'₀ Env'₀ C'₀ h_goeq
            h_e_pres.wf h_e_pres.fwf h_e_pres.ne h_e_pres.mono
            hres_e hakn_e halnd_e harrow₀ hamr_e hamm_e h_e_pres.rigid_inv S hS_abs hS_wf hS_rigid
          -- The tail starts at `subst Env_e.context S = subst Env₀.context S`.
          rw [h_ctx_e, h_ctx_t] at h_tail
          exact StmtsHasType'.cons _ _ _ _ _ _ _ _
            (StmtHasType'.ite_nondet C₀ (TContext.subst Env₀.context S) C_then Γ_then C_else Γ_else
              tss₀ ess₀ md₀ h_then h_else) h_tail
  case case_loop =>
    intro C₀ Env₀ acc₀ labels₀ srest₀ guard₀ measure₀ invariant₀ bss₀ md₀ ih_tail ih_body
      ss'₀ Env'₀ C'₀ h_goeq hwf₀ hfwf₀ hne₀ hmono₀ hres₀ hakn₀ halnd₀ harrow₀ hamr₀ hamm₀ hrigid₀ S hS_abs hS_wf hS_rigid
    unfold Statement.typeCheckAux.go at h_goeq
    simp only [Bind.bind, Except.bind, tryCatchThe, tryCatch, MonadExcept.tryCatch,
      MonadExceptOf.tryCatch, Except.tryCatch, Except.mapError] at h_goeq
    -- Peel the outer tail-`go` bind, then strip the `try`/`catch` shell.
    elim_err h_goeq with v heq
    have h_body := trycatch_ok _ _ v heq
    clear heq
    cases guard₀ with
    | det g =>
      simp only at h_body
      -- guard: freeVarCheck, resolve, `if ty != bool then error else …`.
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
      have h_fvc_g : Env₀.freeVarCheck g
          (Std.format "[" ++ Std.format (Stmt.loop (ExprOrNondet.det g) measure₀ invariant₀ bss₀ md₀) ++
            Std.format "]") = .ok hfvc_v := by
        split at hfvc_eq
        · simp only [reduceCtorEq] at hfvc_eq
        · rename_i w h_fg
          rw [Except.ok.injEq] at hfvc_eq; subst hfvc_eq; exact h_fg
      -- Guard threading: `resolve` preserves context, absorbs, and WF; `checkAnnotCompat`
      -- later forces rigid identity.
      have h_ctx_g : Env_g.context = Env₀.context :=
        resolve_preserves_context g ga C₀ Env₀ Env_g h_res_g hwf₀ hne₀ hfwf₀
      have h_abs_g : Subst.absorbs Env_g.stateSubstInfo.subst Env₀.stateSubstInfo.subst :=
        resolve_absorbs g ga C₀ Env₀ Env_g h_res_g hwf₀ hne₀ hfwf₀
      have h_wf_g : TEnvWF (T := CoreLParams) Env_g :=
        resolve_TEnvWF g ga C₀ Env₀ Env_g h_res_g hwf₀ hfwf₀
      have h_ne_g : Env_g.context.types ≠ [] := by rw [h_ctx_g]; exact hne₀
      have h_mono_g : ContextMono Env_g.context := by rw [h_ctx_g]; exact hmono₀
      -- Peel the measure computation, the invariant fold, and `checkAnnotCompat`.
      elim_err h_body with mres mres_eq
      obtain ⟨mtOpt, Env_m⟩ := mres
      elim_err h_body with fres fres_eq
      obtain ⟨it, Env_inv⟩ := fres
      elim_err h_body with cac_v cac_eq
      simp only at fres_eq cac_eq h_body
      -- Measure threading: `Env_m` preserves `Env_g`'s context/subst/WF; when a measure
      -- is present, it resolves with witnesses (to lift to `int` after the dispatch).
      obtain ⟨h_ctx_m, h_abs_m, h_wf_m, h_meas_wit⟩ :
          Env_m.context = Env_g.context ∧
          Subst.absorbs Env_m.stateSubstInfo.subst Env_g.stateSubstInfo.subst ∧
          TEnvWF (T := CoreLParams) Env_m ∧
          (∀ m, measure₀ = some m → ∃ ma, mtOpt = some ma ∧
            LExpr.resolve C₀ Env_g m = .ok (ma, Env_m)) := by
        cases measure₀ with
        | none =>
          simp only [Except.ok.injEq, Prod.mk.injEq] at mres_eq
          obtain ⟨_, h_em⟩ := mres_eq
          subst h_em
          refine ⟨rfl, Subst.absorbs_refl _ Env_g.stateSubstInfo.isWF, h_wf_g, ?_⟩
          intro m h_eq; simp only [reduceCtorEq] at h_eq
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
          refine ⟨resolve_preserves_context m ma C₀ Env_g Env_ma h_res_m h_wf_g h_ne_g hfwf₀,
            resolve_absorbs m ma C₀ Env_g Env_ma h_res_m h_wf_g h_ne_g hfwf₀,
            resolve_TEnvWF m ma C₀ Env_g Env_ma h_res_m h_wf_g hfwf₀, ?_⟩
          intro m' h_eq; simp only [Option.some.injEq] at h_eq; subst h_eq
          exact ⟨ma, rfl, h_res_m⟩
      have h_ne_m : Env_m.context.types ≠ [] := by rw [h_ctx_m]; exact h_ne_g
      have h_mono_m : ContextMono Env_m.context := by rw [h_ctx_m]; exact h_mono_g
      -- The dispatch arms (`none` / `some int`) share the same goBlock + assembly; peel
      -- the goBlock first by casing on `Option.map toLMonoTy mtOpt`.
      have h_meas_int : ∀ ma, mtOpt = some ma → ma.toLMonoTy = LMonoTy.int := by
        intro ma h_ma
        rw [h_ma] at h_body
        simp only [Option.map_some] at h_body
        split at h_body
        · rename_i h_disc; simp only [reduceCtorEq] at h_disc
        · rename_i ty h_disc
          simp only [Option.some.injEq] at h_disc
          rw [h_disc]; rfl
        · simp only [reduceCtorEq] at h_body
      -- Whatever `mtOpt` is, the dispatch reduces to a goBlock yielding the loop output.
      -- Peel the measure-type dispatch (`none`/`some int`) and the loop-body goBlock,
      -- keeping the resolved measure `mtOpt` abstract. Both surviving arms run the same
      -- goBlock and yield the loop step's output `(Env_loop, C_loop)`.
      have h_gb : ∃ tb Env_loop C_loop,
          Statement.typeCheckAux.goBlock P op C₀ Env_inv bss₀ [] labels₀ = .ok (tb, Env_loop, C_loop) ∧
          v = (Stmt.loop (ExprOrNondet.det (unresolved ga)) (Option.map unresolved mtOpt)
                (List.map (fun x => (x.fst, unresolved x.snd)) it) tb md₀, Env_loop, C_loop) := by
        split at h_body
        · -- `none` arm.
          elim_err h_body with gbv h_gbeq
          obtain ⟨tb, Env_loop, C_loop⟩ := gbv
          rw [Except.ok.injEq] at h_body
          exact ⟨tb, Env_loop, C_loop, h_gbeq, h_body.symm⟩
        · -- `some int` arm.
          elim_err h_body with gbv h_gbeq
          obtain ⟨tb, Env_loop, C_loop⟩ := gbv
          rw [Except.ok.injEq] at h_body
          exact ⟨tb, Env_loop, C_loop, h_gbeq, h_body.symm⟩
        · -- not-`int` arm: the dispatch errors, contradicting `= ok v`.
          simp only [reduceCtorEq] at h_body
      obtain ⟨tb, Env_loop, C_loop, h_gb_eq, h_v⟩ := h_gb
      subst h_v
      -- Invariant-fold threading: apply the generic lemma; `f`/`R` are inferred from
      -- `fres_eq`, and the per-step obligation is discharged by peeling freeVarCheck +
      -- resolve + bool-check (no reproduced typechecker term).
      obtain ⟨h_ctx_inv, h_abs_inv, h_wf_inv, _, h_inv_facts⟩ :
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
        -- Per-step obligation (Lean substitutes the concrete fold body into the goal).
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
      -- `checkAnnotCompat` forces rigid identity at `Env_inv`.
      have h_rigid_inv : ∀ v, v ∈ C₀.rigidTypeVars →
          LMonoTy.subst Env_inv.stateSubstInfo.subst (.ftvar v) = .ftvar v :=
        CmdType.checkAnnotCompat_rigid C₀ Env_inv cac_eq
      -- Context recovery: `Env_inv ≡ Env_m ≡ Env_g ≡ Env₀` (all preserve the context).
      have h_ctx_inv0 : Env_inv.context = Env₀.context := by
        rw [h_ctx_inv, h_ctx_m, h_ctx_g]
      have h_ne_inv : Env_inv.context.types ≠ [] := by rw [h_ctx_inv0]; exact hne₀
      have h_mono_inv : ContextMono Env_inv.context := by rw [h_ctx_inv0]; exact hmono₀
      -- Body goBlock `GoPreserved` (returns input `C₀`) and its context recovery.
      obtain ⟨h_loop_pres, h_Cloop⟩ := goBlock_eq_GoPreserved P op C₀ Env_inv bss₀ [] labels₀
        tb Env_loop C_loop h_gb_eq h_wf_inv hfwf₀ h_ne_inv h_mono_inv h_rigid_inv h_closed
      -- `goBlock` returns the input `C₀`; rewrite the output `C_loop` to `C₀` everywhere
      -- it occurs (keeping `C₀`, the motive-bound head context — do not `subst`).
      rw [h_Cloop] at h_gb_eq h_goeq
      have h_ctx_loop : Env_loop.context = Env_inv.context :=
        goBlock_preserves_context P op C₀ Env_inv bss₀ [] labels₀ tb Env_loop C₀
          h_gb_eq h_wf_inv hfwf₀ h_mono_inv h_rigid_inv h_closed
      -- Tail run preservation (`Env_loop → Env'₀`).
      have h_tail_pres : GoPreserved C₀ C'₀ Env_loop Env'₀ :=
        typeCheckAux_go_preserves C₀ Env_loop P op srest₀
          (Stmt.loop (ExprOrNondet.det (unresolved ga)) (Option.map unresolved mtOpt)
            (List.map (fun x => (x.fst, unresolved x.snd)) it) tb md₀ :: acc₀) labels₀
          ss'₀ Env'₀ C'₀ h_goeq h_loop_pres.wf h_loop_pres.fwf h_loop_pres.ne h_loop_pres.mono
          h_loop_pres.rigid_inv h_closed
      -- Absorbs chain: `S ⊒ Env'₀ ⊒ Env_loop ⊒ Env_inv ⊒ Env_m ⊒ Env_g ⊒ Env₀`.
      have hS_abs_loop : Subst.absorbs S Env_loop.stateSubstInfo.subst :=
        Subst.absorbs_trans _ _ _ h_tail_pres.absorbs hS_abs
      have hS_abs_inv : Subst.absorbs S Env_inv.stateSubstInfo.subst :=
        Subst.absorbs_trans _ _ _ h_loop_pres.absorbs hS_abs_loop
      have hS_abs_m : Subst.absorbs S Env_m.stateSubstInfo.subst :=
        Subst.absorbs_trans _ _ _ h_abs_inv hS_abs_inv
      have hS_abs_g : Subst.absorbs S Env_g.stateSubstInfo.subst :=
        Subst.absorbs_trans _ _ _ h_abs_m hS_abs_m
      -- Guard typing at `S` via `resolve_bool_HasType`.
      have h_guard_ty : Lambda.LExpr.HasType (T := CoreLParams) C₀
          (TContext.subst Env₀.context S) g (.forAll [] .bool) :=
        resolve_bool_HasType C₀ Env₀ Env_g g ga S _ h_fvc_g h_res_g h_g_bool
          hwf₀ hfwf₀ hmono₀ hS_abs_g hS_wf
      -- Body typing via `ih_body` at `S` (existential body output). The body runs under
      -- `C₀`'s rigid set, so the ambient `hS_rigid` discharges the rigid side-condition.
      have hres_inv : TContext.AliasesResolved Env_inv.context := by
        unfold TContext.AliasesResolved at hres₀ ⊢; rw [h_ctx_inv0]; exact hres₀
      have hakn_inv : ∀ a ∈ Env_inv.context.aliases, a.name ≠ "arrow" := by
        rw [h_ctx_inv0]; exact hakn₀
      have halnd_inv : AliasesNonDropping Env_inv.context.aliases := by rw [h_ctx_inv0]; exact halnd₀
      have hamr_inv : ∀ x ty, Env_inv.context.types.find? x = some ty →
          ∀ v ∈ LTy.freeVars ty, v ∈ C₀.rigidTypeVars := by rw [h_ctx_inv0]; exact hamr₀
      have hamm_inv : ∀ ty ∈ Maps.values Env_inv.context.types, LTy.boundVars ty = [] := by
        rw [h_ctx_inv0]; exact hamm₀
      obtain ⟨C_body, Γ_body, h_body_ty⟩ :=
        ih_body Env_inv tb Env_loop C₀ h_gb_eq h_wf_inv hfwf₀ h_ne_inv h_mono_inv hres_inv hakn_inv halnd_inv harrow₀ hamr_inv hamm_inv h_rigid_inv
          S hS_abs_loop hS_wf hS_rigid
      -- Measure typing at `S` (when present) via the `int` analogue of `resolve_bool_HasType`.
      have h_meas_ty : ∀ m, measure₀ = some m →
          Lambda.LExpr.HasType (T := CoreLParams) C₀ (TContext.subst Env₀.context S) m
            (.forAll [] .int) := by
        intro m h_m
        obtain ⟨ma, h_mtOpt, h_res_m⟩ := h_meas_wit m h_m
        have h_int : ma.toLMonoTy = LMonoTy.int := h_meas_int ma h_mtOpt
        -- Recover the measure freeVarCheck from `mres_eq` (it preceded the resolve).
        rw [h_m] at mres_eq
        simp only at mres_eq
        elim_err mres_eq with mfv mfv_eq
        cases mfv
        have h_fvc_m : Env_g.freeVarCheck m (Std.format "[" ++
            Std.format (Stmt.loop (ExprOrNondet.det g) (some m) invariant₀ bss₀ md₀) ++
            Std.format "]") = .ok () := by
          split at mfv_eq
          · simp only [reduceCtorEq] at mfv_eq
          · rename_i w h_fm
            rw [Except.ok.injEq] at mfv_eq; subst mfv_eq; exact h_fm
        -- `S` absorbs `Env_m`'s subst (`= Env_ma` from the measure resolve at `Env_g`).
        rw [← h_ctx_g]
        exact resolve_int_HasType C₀ Env_g Env_m m ma S _ h_fvc_m h_res_m h_int
          h_wf_g hfwf₀ h_mono_g hS_abs_m hS_wf
      -- Invariant typings at `S`: each invariant resolves to `bool` (via `h_inv_facts`).
      have h_inv_ty : ∀ p, p ∈ invariant₀ →
          Lambda.LExpr.HasType (T := CoreLParams) C₀ (TContext.subst Env₀.context S) p.2
            (.forAll [] .bool) := by
        intro p h_mem
        obtain ⟨E_in, E_out, h_wf_in, h_ctx_in, h_abs_out, ia, h_fvc_p, h_res_p, h_bool_p⟩ :=
          h_inv_facts p h_mem
        have h_mono_in : ContextMono E_in.context := by rw [h_ctx_in, h_ctx_m, h_ctx_g]; exact hmono₀
        have h_ctx_in0 : E_in.context = Env₀.context := by rw [h_ctx_in, h_ctx_m, h_ctx_g]
        have hS_abs_out : Subst.absorbs S E_out.stateSubstInfo.subst :=
          Subst.absorbs_trans _ _ _ h_abs_out hS_abs_inv
        rw [← h_ctx_in0]
        exact resolve_bool_HasType C₀ E_in E_out p.2 ia S _ h_fvc_p h_res_p h_bool_p
          h_wf_in hfwf₀ h_mono_in hS_abs_out hS_wf
      -- Tail at `S` (loop leaves `C`/rigid unchanged from `Env_loop`).
      have hres_loop : TContext.AliasesResolved Env_loop.context := by
        unfold TContext.AliasesResolved at hres₀ ⊢; rw [h_ctx_loop, h_ctx_inv0]; exact hres₀
      have hakn_loop : ∀ a ∈ Env_loop.context.aliases, a.name ≠ "arrow" := by
        rw [h_ctx_loop, h_ctx_inv0]; exact hakn₀
      have halnd_loop : AliasesNonDropping Env_loop.context.aliases := by
        rw [h_ctx_loop, h_ctx_inv0]; exact halnd₀
      have hamr_loop : ∀ x ty, Env_loop.context.types.find? x = some ty →
          ∀ v ∈ LTy.freeVars ty, v ∈ C₀.rigidTypeVars := by rw [h_ctx_loop, h_ctx_inv0]; exact hamr₀
      have hamm_loop : ∀ ty ∈ Maps.values Env_loop.context.types, LTy.boundVars ty = [] := by
        rw [h_ctx_loop, h_ctx_inv0]; exact hamm₀
      have h_tail := ih_tail (Stmt.loop (ExprOrNondet.det (unresolved ga)) (Option.map unresolved mtOpt)
          (List.map (fun x => (x.fst, unresolved x.snd)) it) tb md₀) Env_loop C₀ ss'₀ Env'₀ C'₀ h_goeq
        h_loop_pres.wf h_loop_pres.fwf h_loop_pres.ne h_loop_pres.mono
        hres_loop hakn_loop halnd_loop harrow₀ hamr_loop hamm_loop h_loop_pres.rigid_inv
        S hS_abs hS_wf hS_rigid
      -- The tail starts at `subst Env_loop.context S = subst Env₀.context S`.
      rw [h_ctx_loop, h_ctx_inv0] at h_tail
      -- Body typing is at `Env_inv.context S = Env₀.context S` (context recovery).
      rw [h_ctx_inv0] at h_body_ty
      -- Assemble: head `StmtHasType'.loop` (body existential) + tail.
      refine StmtsHasType'.cons _ _ _ _ _ _ _ _
        (StmtHasType'.loop C₀ (TContext.subst Env₀.context S) C_body Γ_body
          (ExprOrNondet.det g) measure₀ invariant₀ bss₀ md₀ ?_ ?_ ?_ h_body_ty) h_tail
      · -- guard
        intro g' h_g'; cases h_g'; exact h_guard_ty
      · -- measure
        exact h_meas_ty
      · -- invariants
        exact h_inv_ty
    | nondet =>
      simp only [pure, Except.pure] at h_body
      -- Measure threading from `Env₀` (the guard leaves the env unchanged).
      elim_err h_body with mres mres_eq
      obtain ⟨mtOpt, Env_m⟩ := mres
      elim_err h_body with fres fres_eq
      obtain ⟨it, Env_inv⟩ := fres
      elim_err h_body with cac_v cac_eq
      simp only at fres_eq cac_eq h_body
      obtain ⟨h_ctx_m, h_abs_m, h_wf_m, h_meas_wit⟩ :
          Env_m.context = Env₀.context ∧
          Subst.absorbs Env_m.stateSubstInfo.subst Env₀.stateSubstInfo.subst ∧
          TEnvWF (T := CoreLParams) Env_m ∧
          (∀ m, measure₀ = some m → ∃ ma, mtOpt = some ma ∧
            LExpr.resolve C₀ Env₀ m = .ok (ma, Env_m)) := by
        cases measure₀ with
        | none =>
          simp only [Except.ok.injEq, Prod.mk.injEq] at mres_eq
          obtain ⟨_, h_em⟩ := mres_eq
          subst h_em
          refine ⟨rfl, Subst.absorbs_refl _ Env₀.stateSubstInfo.isWF, hwf₀, ?_⟩
          intro m h_eq; simp only [reduceCtorEq] at h_eq
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
          refine ⟨resolve_preserves_context m ma C₀ Env₀ Env_ma h_res_m hwf₀ hne₀ hfwf₀,
            resolve_absorbs m ma C₀ Env₀ Env_ma h_res_m hwf₀ hne₀ hfwf₀,
            resolve_TEnvWF m ma C₀ Env₀ Env_ma h_res_m hwf₀ hfwf₀, ?_⟩
          intro m' h_eq; simp only [Option.some.injEq] at h_eq; subst h_eq
          exact ⟨ma, rfl, h_res_m⟩
      have h_ne_m : Env_m.context.types ≠ [] := by rw [h_ctx_m]; exact hne₀
      have h_mono_m : ContextMono Env_m.context := by rw [h_ctx_m]; exact hmono₀
      have h_meas_int : ∀ ma, mtOpt = some ma → ma.toLMonoTy = LMonoTy.int := by
        intro ma h_ma
        rw [h_ma] at h_body
        simp only [Option.map_some] at h_body
        split at h_body
        · rename_i h_disc; simp only [reduceCtorEq] at h_disc
        · rename_i ty h_disc
          simp only [Option.some.injEq] at h_disc
          rw [h_disc]; rfl
        · simp only [reduceCtorEq] at h_body
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
      -- Invariant-fold threading (start env `Env_m`).
      obtain ⟨h_ctx_inv, h_abs_inv, h_wf_inv, _, h_inv_facts⟩ :
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
      have h_rigid_inv : ∀ v, v ∈ C₀.rigidTypeVars →
          LMonoTy.subst Env_inv.stateSubstInfo.subst (.ftvar v) = .ftvar v :=
        CmdType.checkAnnotCompat_rigid C₀ Env_inv cac_eq
      have h_ctx_inv0 : Env_inv.context = Env₀.context := by rw [h_ctx_inv, h_ctx_m]
      have h_ne_inv : Env_inv.context.types ≠ [] := by rw [h_ctx_inv0]; exact hne₀
      have h_mono_inv : ContextMono Env_inv.context := by rw [h_ctx_inv0]; exact hmono₀
      obtain ⟨h_loop_pres, h_Cloop⟩ := goBlock_eq_GoPreserved P op C₀ Env_inv bss₀ [] labels₀
        tb Env_loop C_loop h_gb_eq h_wf_inv hfwf₀ h_ne_inv h_mono_inv h_rigid_inv h_closed
      rw [h_Cloop] at h_gb_eq h_goeq
      have h_ctx_loop : Env_loop.context = Env_inv.context :=
        goBlock_preserves_context P op C₀ Env_inv bss₀ [] labels₀ tb Env_loop C₀
          h_gb_eq h_wf_inv hfwf₀ h_mono_inv h_rigid_inv h_closed
      have h_tail_pres : GoPreserved C₀ C'₀ Env_loop Env'₀ :=
        typeCheckAux_go_preserves C₀ Env_loop P op srest₀
          (Stmt.loop ExprOrNondet.nondet (Option.map unresolved mtOpt)
            (List.map (fun x => (x.fst, unresolved x.snd)) it) tb md₀ :: acc₀) labels₀
          ss'₀ Env'₀ C'₀ h_goeq h_loop_pres.wf h_loop_pres.fwf h_loop_pres.ne h_loop_pres.mono
          h_loop_pres.rigid_inv h_closed
      have hS_abs_loop : Subst.absorbs S Env_loop.stateSubstInfo.subst :=
        Subst.absorbs_trans _ _ _ h_tail_pres.absorbs hS_abs
      have hS_abs_inv : Subst.absorbs S Env_inv.stateSubstInfo.subst :=
        Subst.absorbs_trans _ _ _ h_loop_pres.absorbs hS_abs_loop
      have hS_abs_m : Subst.absorbs S Env_m.stateSubstInfo.subst :=
        Subst.absorbs_trans _ _ _ h_abs_inv hS_abs_inv
      have hres_inv : TContext.AliasesResolved Env_inv.context := by
        unfold TContext.AliasesResolved at hres₀ ⊢; rw [h_ctx_inv0]; exact hres₀
      have hakn_inv : ∀ a ∈ Env_inv.context.aliases, a.name ≠ "arrow" := by rw [h_ctx_inv0]; exact hakn₀
      have halnd_inv : AliasesNonDropping Env_inv.context.aliases := by rw [h_ctx_inv0]; exact halnd₀
      have hamr_inv : ∀ x ty, Env_inv.context.types.find? x = some ty →
          ∀ v ∈ LTy.freeVars ty, v ∈ C₀.rigidTypeVars := by rw [h_ctx_inv0]; exact hamr₀
      have hamm_inv : ∀ ty ∈ Maps.values Env_inv.context.types, LTy.boundVars ty = [] := by rw [h_ctx_inv0]; exact hamm₀
      obtain ⟨C_body, Γ_body, h_body_ty⟩ :=
        ih_body Env_inv tb Env_loop C₀ h_gb_eq h_wf_inv hfwf₀ h_ne_inv h_mono_inv hres_inv hakn_inv halnd_inv harrow₀ hamr_inv hamm_inv h_rigid_inv
          S hS_abs_loop hS_wf hS_rigid
      have h_meas_ty : ∀ m, measure₀ = some m →
          Lambda.LExpr.HasType (T := CoreLParams) C₀ (TContext.subst Env₀.context S) m
            (.forAll [] .int) := by
        intro m h_m
        obtain ⟨ma, h_mtOpt, h_res_m⟩ := h_meas_wit m h_m
        have h_int : ma.toLMonoTy = LMonoTy.int := h_meas_int ma h_mtOpt
        rw [h_m] at mres_eq
        simp only at mres_eq
        elim_err mres_eq with mfv mfv_eq
        cases mfv
        have h_fvc_m : Env₀.freeVarCheck m (Std.format "[" ++
            Std.format (Stmt.loop ExprOrNondet.nondet (some m) invariant₀ bss₀ md₀) ++
            Std.format "]") = .ok () := by
          split at mfv_eq
          · simp only [reduceCtorEq] at mfv_eq
          · rename_i w h_fm
            rw [Except.ok.injEq] at mfv_eq; subst mfv_eq; exact h_fm
        exact resolve_int_HasType C₀ Env₀ Env_m m ma S _ h_fvc_m h_res_m h_int
          hwf₀ hfwf₀ hmono₀ hS_abs_m hS_wf
      have h_inv_ty : ∀ p, p ∈ invariant₀ →
          Lambda.LExpr.HasType (T := CoreLParams) C₀ (TContext.subst Env₀.context S) p.2
            (.forAll [] .bool) := by
        intro p h_mem
        obtain ⟨E_in, E_out, h_wf_in, h_ctx_in, h_abs_out, ia, h_fvc_p, h_res_p, h_bool_p⟩ :=
          h_inv_facts p h_mem
        have h_mono_in : ContextMono E_in.context := by rw [h_ctx_in, h_ctx_m]; exact hmono₀
        have h_ctx_in0 : E_in.context = Env₀.context := by rw [h_ctx_in, h_ctx_m]
        have hS_abs_out : Subst.absorbs S E_out.stateSubstInfo.subst :=
          Subst.absorbs_trans _ _ _ h_abs_out hS_abs_inv
        rw [← h_ctx_in0]
        exact resolve_bool_HasType C₀ E_in E_out p.2 ia S _ h_fvc_p h_res_p h_bool_p
          h_wf_in hfwf₀ h_mono_in hS_abs_out hS_wf
      have hres_loop : TContext.AliasesResolved Env_loop.context := by
        unfold TContext.AliasesResolved at hres₀ ⊢; rw [h_ctx_loop, h_ctx_inv0]; exact hres₀
      have hakn_loop : ∀ a ∈ Env_loop.context.aliases, a.name ≠ "arrow" := by rw [h_ctx_loop, h_ctx_inv0]; exact hakn₀
      have halnd_loop : AliasesNonDropping Env_loop.context.aliases := by rw [h_ctx_loop, h_ctx_inv0]; exact halnd₀
      have hamr_loop : ∀ x ty, Env_loop.context.types.find? x = some ty →
          ∀ v ∈ LTy.freeVars ty, v ∈ C₀.rigidTypeVars := by rw [h_ctx_loop, h_ctx_inv0]; exact hamr₀
      have hamm_loop : ∀ ty ∈ Maps.values Env_loop.context.types, LTy.boundVars ty = [] := by rw [h_ctx_loop, h_ctx_inv0]; exact hamm₀
      have h_tail := ih_tail (Stmt.loop ExprOrNondet.nondet (Option.map unresolved mtOpt)
          (List.map (fun x => (x.fst, unresolved x.snd)) it) tb md₀) Env_loop C₀ ss'₀ Env'₀ C'₀ h_goeq
        h_loop_pres.wf h_loop_pres.fwf h_loop_pres.ne h_loop_pres.mono hres_loop hakn_loop halnd_loop harrow₀ hamr_loop hamm_loop h_loop_pres.rigid_inv
        S hS_abs hS_wf hS_rigid
      rw [h_ctx_loop, h_ctx_inv0] at h_tail
      rw [h_ctx_inv0] at h_body_ty
      refine StmtsHasType'.cons _ _ _ _ _ _ _ _
        (StmtHasType'.loop C₀ (TContext.subst Env₀.context S) C_body Γ_body
          ExprOrNondet.nondet measure₀ invariant₀ bss₀ md₀ ?_ ?_ ?_ h_body_ty) h_tail
      · -- guard (vacuous: nondet)
        intro g' h_g'; simp only [reduceCtorEq] at h_g'
      · exact h_meas_ty
      · exact h_inv_ty
  case case_exit =>
    intro C₀ Env₀ acc₀ labels₀ srest₀ l₀ md₀ ih_tail ss'₀ Env'₀ C'₀ h_goeq hwf₀ hfwf₀ hne₀ hmono₀ hres₀ hakn₀ halnd₀ harrow₀ hamr₀ hamm₀ hrigid₀
      S hS_abs hS_wf hS_rigid
    -- The `exit` head leaves `Env`/`C` unchanged; the head emits `StmtHasType'.exit`,
    -- the tail is the IH (both at the passed subst `S`).
    unfold Statement.typeCheckAux.go at h_goeq
    simp only [Bind.bind, Except.bind, tryCatchThe, tryCatch, MonadExcept.tryCatch,
      MonadExceptOf.tryCatch, Except.tryCatch] at h_goeq
    cases op with
    | none => simp only [reduceCtorEq] at h_goeq
    | some proc =>
      by_cases h_lbl : labels₀.contains l₀
      · simp only [h_lbl, if_true] at h_goeq
        have h_tail := ih_tail (Stmt.exit l₀ md₀) Env₀ C₀ ss'₀ Env'₀ C'₀ h_goeq hwf₀ hfwf₀ hne₀ hmono₀
          hres₀ hakn₀ halnd₀ harrow₀ hamr₀ hamm₀ hrigid₀ S hS_abs hS_wf hS_rigid
        exact StmtsHasType'.cons _ _ _ _ _ _ _ _
          (StmtHasType'.exit _ _ l₀ md₀) h_tail
      · simp only [h_lbl, if_false, Bool.false_eq_true, reduceCtorEq] at h_goeq
  case case_funcDecl =>
    intro C₀ Env₀ acc₀ labels₀ srest₀ decl₀ md₀ ih_tail ss'₀ Env'₀ C'₀ h_goeq hwf₀ hfwf₀ hne₀ hmono₀
      hres₀ hakn₀ halnd₀ harrow₀ hamr₀ hamm₀ hrigid₀ S hS_abs hS_wf hS_rigid
    -- Inline the funcDecl inversion (mirrors the annotated twin).
    unfold Statement.typeCheckAux.go at h_goeq
    simp only [Bind.bind, Except.bind, tryCatchThe, tryCatch, MonadExcept.tryCatch,
      MonadExceptOf.tryCatch, Except.tryCatch] at h_goeq
    cases h_rec : decl₀.isRecursive with
    | true => rw [h_rec] at h_goeq; simp only [if_true, reduceCtorEq] at h_goeq
    | false =>
      rw [h_rec] at h_goeq
      simp only [if_false, Bool.false_eq_true] at h_goeq
      cases h_pf : PureFunc.typeCheck C₀ Env₀ decl₀ with
      | error e =>
        rw [h_pf] at h_goeq
        simp only [Except.mapError, pure, Except.pure, reduceCtorEq] at h_goeq
      | ok v =>
        obtain ⟨decl', func, Env_mid⟩ := v
        rw [h_pf] at h_goeq
        simp only [Except.mapError] at h_goeq
        unfold PureFunc.typeCheck at h_pf
        simp only [Bind.bind, Except.bind] at h_pf
        cases h_of : Function.ofPureFunc decl₀ with
        | error e => rw [h_of] at h_pf; simp only [reduceCtorEq] at h_pf
        | ok func0 =>
          rw [h_of] at h_pf
          simp only at h_pf
          cases h_ft : Function.typeCheck C₀ Env₀ func0 with
          | error e => rw [h_ft] at h_pf; simp only [reduceCtorEq] at h_pf
          | ok w =>
            obtain ⟨func', Env2⟩ := w
            rw [h_ft] at h_pf
            simp only [Except.ok.injEq, Prod.mk.injEq] at h_pf
            obtain ⟨h_decl'_eq, h_func_eq, h_env_eq⟩ := h_pf
            subst h_func_eq
            subst h_env_eq
            -- Polymorphic soundness of the output `func'` at `Γ = Env₀.context`.
            have h_ftype_base : FuncHasType C₀ Env₀.context func' :=
              Function.typeCheck_HasType_output C₀ Env₀ func0 func' Env2 h_ft hwf₀ hfwf₀ hres₀ hakn₀
                hamr₀ hamm₀ halnd₀ harrow₀
            have h_ctx : Env2.context = Env₀.context :=
              Function.typeCheck_context_eq C₀ Env₀ func0 func' Env2 h_ft hwf₀ hfwf₀
            have h_lfwf : Lambda.LFuncWF func' :=
              Function.typeCheck_LFuncWF C₀ Env₀ func0 func' Env2 h_ft hwf₀
            -- Γ-bridge: transport FuncHasType from Env₀.context to subst Env₀.context S.
            have h_expr_congr : ∀ (Γa Γb : TContext Unit) (Cx : LContext CoreLParams)
                (e : Expression.Expr) (t : LTy),
                (∀ x, Γb.types.find? x = Γa.types.find? x) → Γb.aliases = Γa.aliases →
                instHasType.exprTyped Cx Γa e t → instHasType.exprTyped Cx Γb e t :=
              fun Γa Γb Cx e t h_eq h_al h_e => Lambda.LExpr.HasType.find_congr h_e Γb h_eq h_al
            have h_find_bridge : ∀ x,
                (TContext.subst Env₀.context S).types.find? x = Env₀.context.types.find? x :=
              subst_context_find_congr_of_ambient Env₀.context S C₀ hamm₀ hamr₀ hS_rigid
            have h_al_bridge : (TContext.subst Env₀.context S).aliases = Env₀.context.aliases :=
              TContext.subst_aliases Env₀.context S
            have h_ftype_S : FuncHasType C₀ (TContext.subst Env₀.context S) func' :=
              FuncHasType'_find_congr h_expr_congr h_find_bridge h_al_bridge h_ftype_base
            -- Threading premises for the tail IH at C_mid = addFactoryFunction func', Env2.
            have h_wf_mid : TEnvWF (T := CoreLParams) Env2 :=
              Function.typeCheck_TEnvWF C₀ Env₀ func0 func' Env2 h_ft hwf₀ hfwf₀
            have h_fwf_mid : FactoryWF (C₀.addFactoryFunction func').functions :=
              addFactoryFunction_FactoryWF C₀ func' hfwf₀ h_lfwf
            have h_ne_mid : Env2.context.types ≠ [] := by rw [h_ctx]; exact hne₀
            have h_mono_mid : ContextMono Env2.context := by rw [h_ctx]; exact hmono₀
            have h_res_mid : TContext.AliasesResolved Env2.context := by rw [h_ctx]; exact hres₀
            have h_akn_mid : ∀ a ∈ Env2.context.aliases, a.name ≠ "arrow" := by rw [h_ctx]; exact hakn₀
            have h_alnd_mid : AliasesNonDropping Env2.context.aliases := by rw [h_ctx]; exact halnd₀
            have h_arrow_mid : ArrowKnownBinary (C₀.addFactoryFunction func') :=
              addFactoryFunction_ArrowKnownBinary C₀ func' harrow₀
            have h_amr_mid : ∀ x ty, Env2.context.types.find? x = some ty →
                ∀ v ∈ LTy.freeVars ty, v ∈ (C₀.addFactoryFunction func').rigidTypeVars := by
              rw [h_ctx, addFactoryFunction_rigidTypeVars]; exact hamr₀
            have h_amm_mid : ∀ ty ∈ Maps.values Env2.context.types, LTy.boundVars ty = [] := by
              rw [h_ctx]; exact hamm₀
            have h_rigid_mid : ∀ v, v ∈ (C₀.addFactoryFunction func').rigidTypeVars →
                LMonoTy.subst Env2.stateSubstInfo.subst (.ftvar v) = .ftvar v := by
              rw [addFactoryFunction_rigidTypeVars]
              exact Function.typeCheck_preserves_rigid_inv C₀ Env₀ func0 func' Env2 h_ft hwf₀ hfwf₀
                hrigid₀
            have hS_rigid_mid : ∀ v, v ∈ (C₀.addFactoryFunction func').rigidTypeVars →
                LMonoTy.subst S (.ftvar v) = .ftvar v := by
              rw [addFactoryFunction_rigidTypeVars]; exact hS_rigid
            have h_tail := ih_tail (Stmt.funcDecl decl' md₀) Env2 (C₀.addFactoryFunction func')
              ss'₀ Env'₀ C'₀ h_goeq h_wf_mid h_fwf_mid h_ne_mid h_mono_mid
              h_res_mid h_akn_mid h_alnd_mid h_arrow_mid h_amr_mid h_amm_mid h_rigid_mid S hS_abs hS_wf hS_rigid_mid
            rw [h_ctx] at h_tail
            refine StmtsHasType'.cons _ _ _ _ _ _ _ _
              (StmtHasType'.funcDecl C₀ (TContext.subst Env₀.context S) _ func' md₀ ?_ h_ftype_S) h_tail
            -- ¬ decl₀.isRecursive: directly from the inversion's `h_rec`.
            simp [h_rec]
  case case_typeDecl =>
    intro C₀ Env₀ acc₀ labels₀ srest₀ tc₀ md₀ ih_tail ss'₀ Env'₀ C'₀ h_goeq hwf₀ hfwf₀ hne₀ hmono₀ hres₀ hakn₀ halnd₀ harrow₀ hamr₀ hamm₀ hrigid₀
      S hS_abs hS_wf hS_rigid
    unfold Statement.typeCheckAux.go at h_goeq
    simp only [Bind.bind, Except.bind, tryCatchThe, tryCatch, MonadExcept.tryCatch,
      MonadExceptOf.tryCatch, Except.tryCatch] at h_goeq
    cases h_add : C₀.addKnownTypeWithError { name := tc₀.name, metadata := tc₀.numargs }
        (md₀.toDiagnosticF (Std.format "Type '" ++ Std.format tc₀.name ++ Std.format "' is already declared")) with
    | error e => rw [h_add] at h_goeq; simp only [reduceCtorEq] at h_goeq
    | ok C_mid =>
      rw [h_add] at h_goeq
      simp only at h_goeq
      -- `addKnownTypeWithError` preserves `functions` and `rigidTypeVars`.
      obtain ⟨h_fns, h_rig⟩ := addKnownTypeWithError_preserves C₀ C_mid _ _ h_add
      -- The tail's rigid premise needs `S` fixing `C_mid.rigidTypeVars` = `C₀.rigidTypeVars`.
      have hS_rigid_mid : ∀ v, v ∈ C_mid.rigidTypeVars → LMonoTy.subst S (.ftvar v) = .ftvar v := by
        rw [h_rig]; exact hS_rigid
      -- typeDecl leaves aliases + ambient types unchanged; `C.knownTypes` gains a
      -- differently-named type (arrow entry preserved) and rigidTypeVars is unchanged.
      have harrow_mid : ArrowKnownBinary C_mid :=
        addKnownTypeWithError_ArrowKnownBinary C₀ C_mid _ _ h_add harrow₀
      have hamr_mid : ∀ x ty, Env₀.context.types.find? x = some ty →
          ∀ v ∈ LTy.freeVars ty, v ∈ C_mid.rigidTypeVars := by
        intro x ty hfind v hv; rw [h_rig]; exact hamr₀ x ty hfind v hv
      have h_tail := ih_tail (Stmt.typeDecl tc₀ md₀) Env₀ C_mid ss'₀ Env'₀ C'₀ h_goeq hwf₀ (h_fns ▸ hfwf₀)
        hne₀ hmono₀ hres₀ hakn₀ halnd₀ harrow_mid hamr_mid hamm₀ (by rw [h_rig]; exact hrigid₀) S hS_abs hS_wf hS_rigid_mid
      -- The head emits `StmtHasType'.typeDecl`; its `addKnownTypeWithError … default
      -- = ok C_mid` premise comes from `h_add` (real diagnostic) via diag-irrelevance.
      refine StmtsHasType'.cons _ _ _ _ _ _ _ _
        (StmtHasType'.typeDecl C₀ C_mid _ tc₀ md₀ ?_) h_tail
      exact addKnownTypeWithError_diag_irrel C₀ C_mid _ _ default h_add
  case case_goBlock =>
    intro C₀ Env₀ bss₀ acc₀ labels₀ Env₁ ih_body ss'₀ Env'₀ C'₀ h_goeq hwf₀ hfwf₀ hne₀ hmono₀ hres₀ hakn₀ halnd₀ harrow₀ hamr₀ hamm₀ hrigid₀
      S hS_abs hS_wf hS_rigid
    -- `goBlock` = `push; (bss', Env_body, C_body) ← go C₀ (push Env₀) bss₀ acc₀ labels₀;
    --             ok (bss', Env_body.popContext, C₀)`.
    unfold Statement.typeCheckAux.goBlock at h_goeq
    simp only [Bind.bind, Except.bind] at h_goeq
    cases h_body_run : Statement.typeCheckAux.go P op C₀ Env₀.pushEmptyContext bss₀ acc₀ labels₀ with
    | error e => rw [h_body_run] at h_goeq; simp only [reduceCtorEq] at h_goeq
    | ok v =>
      obtain ⟨bss', Env_body, C_body⟩ := v
      rw [h_body_run] at h_goeq
      simp only [Except.ok.injEq, Prod.mk.injEq] at h_goeq
      obtain ⟨_, hEnv, hC⟩ := h_goeq
      subst hEnv; subst hC
      -- `pushEmptyContext` preserves the threading premises needed by the body IH.
      have h_push_wf : TEnvWF (T := CoreLParams) Env₀.pushEmptyContext :=
        pushEmptyContext_TEnvWF Env₀ hwf₀
      have h_push_ne : Env₀.pushEmptyContext.context.types ≠ [] := by
        simp only [TEnv.pushEmptyContext, TEnv.updateContext, TEnv.context, Maps.push]
        exact List.cons_ne_nil _ _
      have h_push_mono : ContextMono Env₀.pushEmptyContext.context :=
        pushEmptyContext_ContextMono Env₀ hmono₀
      have h_push_rigid : ∀ v, v ∈ C₀.rigidTypeVars →
          LMonoTy.subst Env₀.pushEmptyContext.stateSubstInfo.subst (.ftvar v) = .ftvar v := hrigid₀
      -- `Env'₀ = Env_body.popContext`, whose subst is `Env_body.subst` (pop unchanged),
      -- so the passed `S` absorbs `Env_body.subst` directly.
      have hS_abs_body : Subst.absorbs S Env_body.stateSubstInfo.subst := hS_abs
      -- `pushEmptyContext` only prepends an empty types scope: aliases unchanged, `find?`
      -- unchanged (`pushEmptyContext_find?`), values unchanged (empty scope adds nothing), C unchanged.
      have h_push_al : Env₀.pushEmptyContext.context.aliases = Env₀.context.aliases := by
        simp only [TEnv.pushEmptyContext, TEnv.updateContext, TEnv.context]
      have h_push_res : TContext.AliasesResolved Env₀.pushEmptyContext.context := by
        unfold TContext.AliasesResolved at hres₀ ⊢; rw [h_push_al]; exact hres₀
      have h_push_akn : ∀ a ∈ Env₀.pushEmptyContext.context.aliases, a.name ≠ "arrow" := by
        rw [h_push_al]; exact hakn₀
      have h_push_alnd : AliasesNonDropping Env₀.pushEmptyContext.context.aliases := by
        rw [h_push_al]; exact halnd₀
      have h_push_amr : ∀ x ty, Env₀.pushEmptyContext.context.types.find? x = some ty →
          ∀ v ∈ LTy.freeVars ty, v ∈ C₀.rigidTypeVars := by
        intro x ty hfind; rw [pushEmptyContext_find?] at hfind; exact hamr₀ x ty hfind
      have h_push_amm : ∀ ty ∈ Maps.values Env₀.pushEmptyContext.context.types,
          LTy.boundVars ty = [] := by
        intro ty hty
        simp only [TEnv.pushEmptyContext, TEnv.updateContext, TEnv.context, Maps.push,
          Maps.values, Map.values, List.nil_append] at hty
        exact hamm₀ ty hty
      have h_body_typed : StmtsHasType P C₀
          (TContext.subst Env₀.pushEmptyContext.context S) bss₀
          C_body (TContext.subst Env_body.context S) :=
        ih_body bss' Env_body C_body h_body_run h_push_wf hfwf₀ h_push_ne h_push_mono
          h_push_res h_push_akn h_push_alnd harrow₀ h_push_amr h_push_amm h_push_rigid
          S hS_abs_body hS_wf hS_rigid
      -- Expression-layer congruence at the `instHasType` instance (= `HasType`).
      have h_expr_congr : ∀ (Γa Γb : TContext Unit) (Cx : LContext CoreLParams)
          (e : Expression.Expr) (t : LTy),
          (∀ x, Γb.types.find? x = Γa.types.find? x) → Γb.aliases = Γa.aliases →
          instHasType.exprTyped Cx Γa e t → instHasType.exprTyped Cx Γb e t :=
        fun Γa Γb Cx e t h_eq h_al h_e => Lambda.LExpr.HasType.find_congr h_e Γb h_eq h_al
      -- The pushed input context agrees with the plain one on `aliases`.
      have h_al_bridge : (TContext.subst Env₀.pushEmptyContext.context S).aliases
          = (TContext.subst Env₀.context S).aliases := by
        rw [TContext.subst_aliases, TContext.subst_aliases]
        simp only [TEnv.pushEmptyContext, TEnv.updateContext, TEnv.context]
      -- Bridge the INPUT Γ from `subst (push Env₀).context S` to `subst Env₀.context S`
      -- (they agree on `find?` and `aliases`) via the statement-level Γ-congruence.
      obtain ⟨Γ_body', _, _, h_body_plain⟩ :=
        StmtsHasType'_find_congr h_expr_congr h_body_typed (TContext.subst Env₀.context S)
          (fun y => subst_pushEmptyContext_find? Env₀ S y) h_al_bridge
      -- The body output is existential — supply `C_body` and the bridged Γ.
      exact ⟨C_body, Γ_body', h_body_plain⟩

/-! ### Part I — Top-level theorem -/

/--
Soundness of the statement typechecker (Part I, unannotated): if
`Statement.typeCheck` succeeds, the original statements satisfy `StmtsHasType`
between the substituted input/output contexts. The output `LContext` is discarded
by `typeCheck`, so it is existentially quantified.
-/
theorem Statement.typeCheck_sound (C : LContext CoreLParams) (Env : TEnv Unit)
    (P : Program) (op : Option Procedure) (ss ss' : List Statement) (Env' : TEnv Unit)
    (h : Statement.typeCheck C Env P op ss = .ok (ss', Env'))
    (h_wf : TEnvWF (T := CoreLParams) Env)
    (h_fwf : FactoryWF C.functions)
    (h_ne : Env.context.types ≠ [])
    (h_mono : ContextMono Env.context)
    -- Well-formedness antecedents threaded to the `funcDecl` case. All monotone invariants.
    (h_resolved : TContext.AliasesResolved Env.context)
    (h_aliases_not_known : ∀ a ∈ Env.context.aliases, a.name ≠ "arrow")
    (h_ali_nd : AliasesNonDropping Env.context.aliases)
    (h_arrow_wf : ArrowKnownBinary C)
    (h_ambient_rigid : ∀ x ty, Env.context.types.find? x = some ty →
      ∀ v ∈ LTy.freeVars ty, v ∈ C.rigidTypeVars)
    (h_ambient_mono : ∀ ty ∈ Maps.values Env.context.types, LTy.boundVars ty = [])
    (h_rigid_inv : ∀ v, v ∈ C.rigidTypeVars →
      LMonoTy.subst Env.stateSubstInfo.subst (.ftvar v) = .ftvar v)
    (h_closed : CalledProcsClosed P) :
    ∃ C', StmtsHasType P C (TContext.subst Env.context Env'.stateSubstInfo.subst) ss
      C' Env'.context := by
  -- `typeCheck` runs `typeCheckAux = go … [] []`, then overwrites the output
  -- context with `subst Env_aux.context Env_aux.subst` while leaving
  -- `stateSubstInfo` untouched. So `Env'.stateSubstInfo.subst = Env_aux.subst`
  -- and `Env'.context = subst Env_aux.context Env_aux.subst`.
  unfold Statement.typeCheck Statement.typeCheckAux at h
  -- The body is `go … >>= fun (ss', Env, _C) => …`; destructure the `go` result.
  cases h_go : Statement.typeCheckAux.go P op C Env ss [] [] with
  | error e => rw [h_go] at h; simp only [bind, Except.bind] at h; cases h
  | ok v_aux =>
    obtain ⟨ss_aux, Env_aux, C_aux⟩ := v_aux
    rw [h_go] at h
    simp only [bind, Except.bind, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨h_ss, h_env⟩ := h
    refine ⟨C_aux, ?_⟩
    have h_core := typeCheckAux_go_sound C Env P op ss [] [] ss_aux Env_aux C_aux
      h_go h_wf h_fwf h_ne h_mono h_resolved h_aliases_not_known h_ali_nd h_arrow_wf
      h_ambient_rigid h_ambient_mono h_rigid_inv h_closed
    -- `Env'` is `Env_aux.updateContext (subst Env_aux.context Env_aux.subst)`, so
    -- `Env'.stateSubstInfo.subst = Env_aux.stateSubstInfo.subst` and
    -- `Env'.context = subst Env_aux.context Env_aux.subst`.
    subst h_env
    simpa [TEnv.updateContext, TEnv.context] using h_core

/-! ### Part II — Annotated soundness -/

/-- `Statement.subst.go` with an accumulator equals reverse-accumulator appended to
    the plain map. (Mirrors the standard `go`/accumulator-reverse pattern.) -/
theorem Statement.subst_go_eq (S : Subst) (ss acc : List Statement) :
    Core.Statement.Statement.subst.go S ss acc =
      acc.reverse ++ List.map (Core.Statement.Statement.subst S) ss := by
  induction ss generalizing acc with
  | nil => simp [Core.Statement.Statement.subst.go]
  | cons s srest ih =>
    rw [Core.Statement.Statement.subst.go]
    rw [ih ((Core.Statement.Statement.subst S s) :: acc)]
    simp

/-- `Statement.subst.go` started from the empty accumulator is the plain map. -/
theorem Statement.subst_go_nil (S : Subst) (ss : List Statement) :
    Core.Statement.Statement.subst.go S ss [] =
      List.map (Core.Statement.Statement.subst S) ss := by
  rw [Statement.subst_go_eq]; simp

/-- Annotated soundness for the `go` loop of `typeCheckAux`: the output statements
    (with the final substitution applied) satisfy `StmtsHasTypeA`. Requires
    `AliasesResolved` instead of the rigid invariant (cf. the `Cmd` annotated layer). -/
theorem typeCheckAux_go_annotated_sound (C : LContext CoreLParams) (Env : TEnv Unit)
    (P : Program) (op : Option Procedure) (ss : List Statement) (labels : List String)
    (ss' : List Statement) (Env' : TEnv Unit) (C' : LContext CoreLParams)
    (h : Statement.typeCheckAux.go P op C Env ss [] labels = .ok (ss', Env', C'))
    (h_wf : TEnvWF (T := CoreLParams) Env)
    (h_fwf : FactoryWF C.functions)
    (h_ne : Env.context.types ≠ [])
    (h_mono : ContextMono Env.context)
    (h_resolved : TContext.AliasesResolved Env.context)
    (h_rigid_inv : ∀ v, v ∈ C.rigidTypeVars →
      LMonoTy.subst Env.stateSubstInfo.subst (.ftvar v) = .ftvar v)
    (h_closed : CalledProcsClosed P) :
    StmtsHasTypeA P C (TContext.subst Env.context Env'.stateSubstInfo.subst)
      (List.map (Core.Statement.Statement.subst Env'.stateSubstInfo.subst) ss')
      C' (TContext.subst Env'.context Env'.stateSubstInfo.subst) := by
  -- `h_rigid_inv` is threaded only to discharge the intermediate `absorbs` facts via
  -- `_preserves`/`typeCheckCmd_preserves`; the annotated head needs no rigid premise
  -- (`HasTypeA` is substitution-independent), and `AliasesResolved` replaces it there.
  -- Existential-accumulator motive: `ss' = acc.reverse ++ ss_proc` with `StmtsHasTypeA`
  -- on only the processed suffix `ss_proc` (carrying `acc` into the conclusion would force
  -- typing already-processed statements from the input context — false). At `acc = []` this
  -- recovers the theorem's conclusion.
  have h_ind := Statement.typeCheckAux.go.induct P op
    (motive1 := fun C Env ss acc labels =>
      ∀ ss' Env' C',
      Statement.typeCheckAux.go P op C Env ss acc labels = .ok (ss', Env', C') →
      TEnvWF (T := CoreLParams) Env → FactoryWF C.functions →
      Env.context.types ≠ [] → ContextMono Env.context →
      TContext.AliasesResolved Env.context →
      (∀ v, v ∈ C.rigidTypeVars →
        LMonoTy.subst Env.stateSubstInfo.subst (.ftvar v) = .ftvar v) →
      ∀ S, Subst.absorbs S Env'.stateSubstInfo.subst → SubstWF S →
        ∃ ss_proc, ss' = acc.reverse ++ ss_proc ∧
          StmtsHasTypeA P C (TContext.subst Env.context S)
            (List.map (Core.Statement.Statement.subst S) ss_proc)
            C' (TContext.subst Env'.context S))
    (motive2 := fun C Env bss acc labels =>
      ∀ ss' Env' C',
      Statement.typeCheckAux.goBlock P op C Env bss acc labels = .ok (ss', Env', C') →
      TEnvWF (T := CoreLParams) Env → FactoryWF C.functions →
      Env.context.types ≠ [] → ContextMono Env.context →
      TContext.AliasesResolved Env.context →
      (∀ v, v ∈ C.rigidTypeVars →
        LMonoTy.subst Env.stateSubstInfo.subst (.ftvar v) = .ftvar v) →
      ∀ S, Subst.absorbs S Env'.stateSubstInfo.subst → SubstWF S →
        ∃ C_body Γ_body ss_proc, ss' = acc.reverse ++ ss_proc ∧
          StmtsHasTypeA P C (TContext.subst Env.context S)
            (List.map (Core.Statement.Statement.subst S) ss_proc) C_body Γ_body)
    ?case_nil ?case_cmd ?case_block_clash ?case_block ?case_ite ?case_loop
    ?case_exit ?case_funcDecl ?case_typeDecl ?case_goBlock
    C Env ss [] labels
  -- Instantiate at `S = Env'.subst` (absorbs by refl, WF by `isWF`) and `acc = []`.
  obtain ⟨ss_proc, h_eq, h_typed⟩ := h_ind ss' Env' C' h h_wf h_fwf h_ne h_mono h_resolved
    h_rigid_inv Env'.stateSubstInfo.subst (Subst.absorbs_refl _ Env'.stateSubstInfo.isWF)
    Env'.stateSubstInfo.isWF
  simp only [List.reverse_nil, List.nil_append] at h_eq
  rw [h_eq]; exact h_typed
  case case_nil =>
    intro C₀ Env₀ acc₀ labels₀ ss'₀ Env'₀ C'₀ h₀ hwf₀ hfwf₀ hne₀ hmono₀ hres₀ hrigid₀ S hS_abs hS_wf
    -- `go … [] …` returns `(acc.reverse, Env₀, C₀)`, so `ss'₀ = acc₀.reverse`, `Env'₀ = Env₀`, `C'₀ = C₀`.
    simp only [Statement.typeCheckAux.go, Except.ok.injEq, Prod.mk.injEq] at h₀
    obtain ⟨hss, hEnv, hC⟩ := h₀
    subst hEnv; subst hC
    refine ⟨[], ?_, ?_⟩
    · rw [hss]; simp
    · simp only [List.map_nil]; exact StmtsHasType'.nil _ _
  case case_cmd =>
    intro C₀ Env₀ acc₀ labels₀ srest₀ cmd₀ ih ss'₀ Env'₀ C'₀ h₀ hwf₀ hfwf₀ hne₀ hmono₀ hres₀ hrigid₀
      S hS_abs hS_wf
    simp only [Statement.typeCheckAux.go, Bind.bind, Except.bind] at h₀
    cases h_tc : Statement.typeCheckCmd C₀ Env₀ P cmd₀ with
    | error e => rw [h_tc] at h₀; simp at h₀
    | ok v =>
      obtain ⟨c', Env_mid⟩ := v
      rw [h_tc] at h₀
      simp only at h₀
      -- Threading: command-step preservation (head) gives WF/ne/mono/absorbs/rigid/aliases.
      obtain ⟨h_wf_mid, h_ne_mid, h_mono_mid, _, h_rigid_mid, _, h_al_mid, _⟩ :=
        typeCheckCmd_preserves C₀ Env₀ P cmd₀ c' Env_mid h_tc hwf₀ hfwf₀ hne₀ hmono₀ hrigid₀ h_closed
      -- `AliasesResolved` is preserved: it depends only on `.aliases`, which the
      -- command step leaves fixed (`h_al_mid`).
      have h_res_mid : TContext.AliasesResolved Env_mid.context := by
        unfold TContext.AliasesResolved at hres₀ ⊢; rw [h_al_mid]; exact hres₀
      have h_tail_pres : GoPreserved C₀ C'₀ Env_mid Env'₀ :=
        typeCheckAux_go_preserves C₀ Env_mid P op srest₀ (Stmt.cmd c' :: acc₀) labels₀
          ss'₀ Env'₀ C'₀ h₀ h_wf_mid hfwf₀ h_ne_mid h_mono_mid h_rigid_mid h_closed
      -- `S` absorbs the command's intermediate subst (S ⊒ Env'₀ ⊒ Env_mid).
      have h_abs_S_mid : Subst.absorbs S Env_mid.stateSubstInfo.subst :=
        Subst.absorbs_trans _ _ _ h_tail_pres.absorbs hS_abs
      -- Head obligation at `S` via the universal-`S` annotated command theorem.
      have h_head_cmd : CmdExtHasTypeA C₀ P (TContext.subst Env₀.context S)
          (Statement.Command.subst S c') (TContext.subst Env_mid.context S) :=
        Command.typeCheckCmd_annotated_sound_gen C₀ Env₀ P cmd₀ c' Env_mid h_tc hwf₀ hfwf₀ hne₀
          hmono₀ hres₀
          (fun proc pname callArgs md h_eq h_find => h_closed pname proc h_find)
          S h_abs_S_mid hS_wf
      -- Tail via the IH (commands leave `C`/rigid/`AliasesResolved` unchanged).
      obtain ⟨ss_proc_tail, h_eq_tail, h_typed_tail⟩ :=
        ih (Stmt.cmd c') Env_mid C₀ ss'₀ Env'₀ C'₀ h₀ h_wf_mid hfwf₀ h_ne_mid h_mono_mid h_res_mid
          h_rigid_mid S hS_abs hS_wf
      -- Reassociate the accumulator: `(cmd c' :: acc₀).reverse ++ tail = acc₀.reverse ++ (cmd c' :: tail)`.
      refine ⟨Stmt.cmd c' :: ss_proc_tail, ?_, ?_⟩
      · rw [h_eq_tail]; simp
      · simp only [List.map_cons, Core.Statement.Statement.subst]
        exact StmtsHasType'.cons _ _ _ _ _ _ _ _
          (StmtHasType'.cmd _ _ _ _ h_head_cmd) h_typed_tail
  case case_block_clash =>
    intro C₀ Env₀ acc₀ labels₀ srest₀ label₀ bss₀ md₀ h_clash ih_tail ih_block
      ss'₀ Env'₀ C'₀ h_goeq hwf₀ hfwf₀ hne₀ hmono₀ hres₀ hrigid₀ S hS_abs hS_wf
    -- The label clashes, so the `block` head `throw`s; `go = ok` is contradictory.
    rw [Statement.typeCheckAux.go] at h_goeq
    simp only [h_clash, if_true, Bind.bind, Except.bind] at h_goeq
    exact absurd h_goeq (by simp)
  case case_block =>
    intro C₀ Env₀ acc₀ labels₀ srest₀ label₀ bss₀ md₀ h_noclash ih_tail ih_block
      ss'₀ Env'₀ C'₀ h_goeq hwf₀ hfwf₀ hne₀ hmono₀ hres₀ hrigid₀ S hS_abs hS_wf
    -- `block` (no label clash): `(bss', Env_blk, C₀) ← goBlock …; go C₀ Env_blk srest (s'::acc)`.
    rw [Statement.typeCheckAux.go] at h_goeq
    simp only [h_noclash, if_false, Bool.false_eq_true, Bind.bind, Except.bind] at h_goeq
    cases h_blk : Statement.typeCheckAux.goBlock P op C₀ Env₀ bss₀ [] (label₀ :: labels₀) with
    | error e => rw [h_blk] at h_goeq; simp [pure, Except.pure] at h_goeq
    | ok v =>
      obtain ⟨bss', Env_blk, C_blk⟩ := v
      rw [h_blk] at h_goeq
      simp only [pure, Except.pure] at h_goeq
      -- `goBlock` returns the input `C₀` (`goBlock_returns_input_C`).
      have h_Cblk : C_blk = C₀ :=
        goBlock_returns_input_C P op C₀ C_blk Env₀ Env_blk bss₀ [] (label₀ :: labels₀) bss' h_blk
      rw [h_Cblk] at h_blk h_goeq
      -- The block step's output context equals the input (`goBlock_preserves_context`).
      have h_ctx_blk : Env_blk.context = Env₀.context :=
        goBlock_preserves_context P op C₀ Env₀ bss₀ [] (label₀ :: labels₀) bss' Env_blk C₀
          h_blk hwf₀ hfwf₀ hmono₀ hrigid₀ h_closed
      -- The block step preserves the threading invariants (head: `goBlock`'s `GoPreserved`).
      have h_blk_pres : GoPreserved C₀ C₀ Env₀ Env_blk := by
        have h_blk' := h_blk
        unfold Statement.typeCheckAux.goBlock at h_blk'
        simp only [Bind.bind, Except.bind] at h_blk'
        cases h_run : Statement.typeCheckAux.go P op C₀ Env₀.pushEmptyContext bss₀ [] (label₀ :: labels₀) with
        | error e => rw [h_run] at h_blk'; simp only [reduceCtorEq] at h_blk'
        | ok w =>
          obtain ⟨w1, Env_body, w3⟩ := w
          rw [h_run] at h_blk'
          simp only [Except.ok.injEq, Prod.mk.injEq] at h_blk'
          obtain ⟨_, h_envblk, _⟩ := h_blk'
          have h_push_wf : TEnvWF (T := CoreLParams) Env₀.pushEmptyContext :=
            pushEmptyContext_TEnvWF Env₀ hwf₀
          have h_push_ne : Env₀.pushEmptyContext.context.types ≠ [] := by
            simp only [TEnv.pushEmptyContext, TEnv.updateContext, TEnv.context, Maps.push]
            exact List.cons_ne_nil _ _
          have h_push_mono : ContextMono Env₀.pushEmptyContext.context :=
            pushEmptyContext_ContextMono Env₀ hmono₀
          have h_body_pres : GoPreserved C₀ w3 Env₀.pushEmptyContext Env_body :=
            typeCheckAux_go_preserves C₀ Env₀.pushEmptyContext P op bss₀ [] (label₀ :: labels₀)
              w1 Env_body w3 h_run h_push_wf hfwf₀ h_push_ne h_push_mono hrigid₀ h_closed
          rw [← h_envblk]
          exact goBlock_GoPreserved h_body_pres hwf₀ hfwf₀ hne₀ hmono₀
      -- `AliasesResolved` at `Env_blk` (context unchanged across the block step).
      have h_res_blk : TContext.AliasesResolved Env_blk.context := by
        unfold TContext.AliasesResolved at hres₀ ⊢; rw [h_ctx_blk]; exact hres₀
      -- Tail preservation (`Env_blk → Env'₀`) gives `S ⊒ Env'₀ ⊒ Env_blk`.
      have h_tail_pres : GoPreserved C₀ C'₀ Env_blk Env'₀ :=
        typeCheckAux_go_preserves C₀ Env_blk P op srest₀ (Stmt.block label₀ bss' md₀ :: acc₀)
          labels₀ ss'₀ Env'₀ C'₀ h_goeq h_blk_pres.wf h_blk_pres.fwf h_blk_pres.ne h_blk_pres.mono
          h_blk_pres.rigid_inv h_closed
      have hS_abs_blk : Subst.absorbs S Env_blk.stateSubstInfo.subst :=
        Subst.absorbs_trans _ _ _ h_tail_pres.absorbs hS_abs
      -- The block head's body typing (existential body output + accumulator) via `ih_block`.
      obtain ⟨C_body, Γ_body, bss_proc, h_bss_eq, h_body⟩ :=
        ih_block bss' Env_blk C₀ h_blk hwf₀ hfwf₀ hne₀ hmono₀ hres₀ hrigid₀ S hS_abs_blk hS_wf
      -- `goBlock` is called with `acc = []`, so `bss' = bss_proc`.
      simp only [List.reverse_nil, List.nil_append] at h_bss_eq
      subst h_bss_eq
      -- Tail via the IH (`Env_blk → Env'₀`); block leaves `C`/rigid/`AliasesResolved` unchanged.
      obtain ⟨ss_proc_tail, h_eq_tail, h_typed_tail⟩ :=
        ih_tail (Stmt.block label₀ bss' md₀) Env_blk C₀ ss'₀ Env'₀ C'₀ h_goeq
          h_blk_pres.wf h_blk_pres.fwf h_blk_pres.ne h_blk_pres.mono h_res_blk h_blk_pres.rigid_inv
          S hS_abs hS_wf
      -- The tail starts at `subst Env_blk.context S = subst Env₀.context S` (context recovery).
      rw [h_ctx_blk] at h_typed_tail
      refine ⟨Stmt.block label₀ bss' md₀ :: ss_proc_tail, ?_, ?_⟩
      · rw [h_eq_tail]; simp
      · simp only [List.map_cons, Core.Statement.Statement.subst, Statement.subst_go_nil]
        exact StmtsHasType'.cons _ _ _ _ _ _ _ _
          (StmtHasType'.block C₀ (TContext.subst Env₀.context S) C_body Γ_body label₀
            (List.map (Core.Statement.Statement.subst S) bss') md₀ h_body)
          h_typed_tail
  case case_ite =>
    intro C₀ Env₀ acc₀ labels₀ srest₀ cond₀ tss₀ ess₀ md₀ ih_tail ih_branches
      ss'₀ Env'₀ C'₀ h_goeq hwf₀ hfwf₀ hne₀ hmono₀ hres₀ hrigid₀ S hS_abs hS_wf
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
            have h_ctx_r : Env_r.context = Env₀.context :=
              resolve_preserves_context c conda C₀ Env₀ Env_r h_res hwf₀ hne₀ hfwf₀
            have h_wf_r : TEnvWF (T := CoreLParams) Env_r :=
              resolve_TEnvWF c conda C₀ Env₀ Env_r h_res hwf₀ hfwf₀
            have h_ne_r : Env_r.context.types ≠ [] := by rw [h_ctx_r]; exact hne₀
            have h_mono_r : ContextMono Env_r.context := by rw [h_ctx_r]; exact hmono₀
            have h_res_r : TContext.AliasesResolved Env_r.context := by
              unfold TContext.AliasesResolved at hres₀ ⊢; rw [h_ctx_r]; exact hres₀
            have h_rigid_r : ∀ v, v ∈ C₀.rigidTypeVars →
                LMonoTy.subst Env_r.stateSubstInfo.subst (.ftvar v) = .ftvar v :=
              CmdType.checkAnnotCompat_rigid C₀ Env_r h_cac
            cases h_t : Statement.typeCheckAux.goBlock P op C₀ Env_r tss₀ [] labels₀ with
            | error e => rw [h_t] at h_blocks; simp only [reduceCtorEq] at h_blocks
            | ok vt =>
              obtain ⟨tss', Env_t, C_t⟩ := vt
              rw [h_t] at h_blocks
              simp only at h_blocks
              obtain ⟨h_t_pres, h_Ct⟩ := goBlock_eq_GoPreserved P op C₀ Env_r tss₀ [] labels₀
                tss' Env_t C_t h_t h_wf_r hfwf₀ h_ne_r h_mono_r h_rigid_r h_closed
              subst C_t
              have h_ctx_t : Env_t.context = Env_r.context :=
                goBlock_preserves_context P op C₀ Env_r tss₀ [] labels₀ tss' Env_t C₀
                  h_t h_wf_r hfwf₀ h_mono_r h_rigid_r h_closed
              have h_res_t : TContext.AliasesResolved Env_t.context := by
                unfold TContext.AliasesResolved at h_res_r ⊢; rw [h_ctx_t]; exact h_res_r
              cases h_e : Statement.typeCheckAux.goBlock P op C₀ Env_t ess₀ [] labels₀ with
              | error e => rw [h_e] at h_blocks; simp only [reduceCtorEq] at h_blocks
              | ok ve =>
                obtain ⟨ess', Env_e, C_e⟩ := ve
                rw [h_e] at h_blocks
                simp only [Except.ok.injEq] at h_blocks
                obtain ⟨h_e_pres, h_Ce⟩ := goBlock_eq_GoPreserved P op C₀ Env_t ess₀ [] labels₀
                  ess' Env_e C_e h_e h_t_pres.wf h_t_pres.fwf h_t_pres.ne h_t_pres.mono
                  h_t_pres.rigid_inv h_closed
                subst C_e
                subst h_blocks
                simp only at h_goeq
                have h_ctx_e : Env_e.context = Env_t.context :=
                  goBlock_preserves_context P op C₀ Env_t ess₀ [] labels₀ ess' Env_e C₀
                    h_e h_t_pres.wf h_t_pres.fwf h_t_pres.mono h_t_pres.rigid_inv h_closed
                have h_res_e : TContext.AliasesResolved Env_e.context := by
                  unfold TContext.AliasesResolved at h_res_t ⊢; rw [h_ctx_e]; exact h_res_t
                have h_tail_pres : GoPreserved C₀ C'₀ Env_e Env'₀ :=
                  typeCheckAux_go_preserves C₀ Env_e P op srest₀
                    (Stmt.ite (.det (unresolved conda)) tss' ess' md₀ :: acc₀) labels₀
                    ss'₀ Env'₀ C'₀ h_goeq h_e_pres.wf h_e_pres.fwf h_e_pres.ne h_e_pres.mono
                    h_e_pres.rigid_inv h_closed
                have hS_abs_e : Subst.absorbs S Env_e.stateSubstInfo.subst :=
                  Subst.absorbs_trans _ _ _ h_tail_pres.absorbs hS_abs
                have hS_abs_t : Subst.absorbs S Env_t.stateSubstInfo.subst :=
                  Subst.absorbs_trans _ _ _ h_e_pres.absorbs hS_abs_e
                have hS_abs_r : Subst.absorbs S Env_r.stateSubstInfo.subst :=
                  Subst.absorbs_trans _ _ _ h_t_pres.absorbs hS_abs_t
                -- Output condition typing at `S` via `resolve_bool_HasTypeA`.
                have h_cond : Lambda.LExpr.HasTypeA [] (conda.unresolved.applySubst S) .bool :=
                  resolve_bool_HasTypeA C₀ Env₀ Env_r c conda S h_res h_condty hwf₀ hfwf₀ hres₀
                -- Branch typings (existential body output + accumulator) via the branch IHs.
                obtain ⟨C_then, Γ_then, tss_proc, h_tss_eq, h_then⟩ :=
                  ih_then Env_r tss' Env_t C₀ h_t h_wf_r hfwf₀ h_ne_r h_mono_r h_res_r h_rigid_r
                    S hS_abs_t hS_wf
                obtain ⟨C_else, Γ_else, ess_proc, h_ess_eq, h_else⟩ :=
                  ih_else Env_t C₀ ess' Env_e C₀ h_e h_t_pres.wf h_t_pres.fwf h_t_pres.ne
                    h_t_pres.mono h_res_t h_t_pres.rigid_inv S hS_abs_e hS_wf
                simp only [List.reverse_nil, List.nil_append] at h_tss_eq h_ess_eq
                subst h_tss_eq; subst h_ess_eq
                rw [h_ctx_r] at h_then
                rw [h_ctx_t, h_ctx_r] at h_else
                obtain ⟨ss_proc_tail, h_eq_tail, h_typed_tail⟩ :=
                  ih_tail (Stmt.ite (.det (unresolved conda)) tss' ess' md₀) Env_e C₀
                    ss'₀ Env'₀ C'₀ h_goeq h_e_pres.wf h_e_pres.fwf h_e_pres.ne h_e_pres.mono
                    h_res_e h_e_pres.rigid_inv S hS_abs hS_wf
                rw [h_ctx_e, h_ctx_t, h_ctx_r] at h_typed_tail
                refine ⟨Stmt.ite (.det (unresolved conda)) tss' ess' md₀ :: ss_proc_tail, ?_, ?_⟩
                · rw [h_eq_tail]; simp
                · simp only [List.map_cons, Core.Statement.Statement.subst,
                    Imperative.ExprOrNondet.map, Statement.subst_go_nil]
                  exact StmtsHasType'.cons _ _ _ _ _ _ _ _
                    (StmtHasType'.ite_det C₀ (TContext.subst Env₀.context S) C_then Γ_then
                      C_else Γ_else (conda.unresolved.applySubst S)
                      (List.map (Core.Statement.Statement.subst S) tss')
                      (List.map (Core.Statement.Statement.subst S) ess') md₀ h_cond h_then h_else)
                    h_typed_tail
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
          obtain ⟨h_t_pres, h_Ct⟩ := goBlock_eq_GoPreserved P op C₀ Env₀ tss₀ [] labels₀
            tss' Env_t C_t h_t hwf₀ hfwf₀ hne₀ hmono₀ hrigid₀ h_closed
          subst C_t
          have h_ctx_t : Env_t.context = Env₀.context :=
            goBlock_preserves_context P op C₀ Env₀ tss₀ [] labels₀ tss' Env_t C₀
              h_t hwf₀ hfwf₀ hmono₀ hrigid₀ h_closed
          have h_res_t : TContext.AliasesResolved Env_t.context := by
            unfold TContext.AliasesResolved at hres₀ ⊢; rw [h_ctx_t]; exact hres₀
          obtain ⟨h_e_pres, h_Ce⟩ := goBlock_eq_GoPreserved P op C₀ Env_t ess₀ [] labels₀
            ess' Env_e C_e h_e h_t_pres.wf h_t_pres.fwf h_t_pres.ne h_t_pres.mono
            h_t_pres.rigid_inv h_closed
          subst C_e
          have h_ctx_e : Env_e.context = Env_t.context :=
            goBlock_preserves_context P op C₀ Env_t ess₀ [] labels₀ ess' Env_e C₀
              h_e h_t_pres.wf h_t_pres.fwf h_t_pres.mono h_t_pres.rigid_inv h_closed
          have h_res_e : TContext.AliasesResolved Env_e.context := by
            unfold TContext.AliasesResolved at h_res_t ⊢; rw [h_ctx_e]; exact h_res_t
          have h_tail_pres : GoPreserved C₀ C'₀ Env_e Env'₀ :=
            typeCheckAux_go_preserves C₀ Env_e P op srest₀
              (Stmt.ite .nondet tss' ess' md₀ :: acc₀) labels₀ ss'₀ Env'₀ C'₀ h_goeq
              h_e_pres.wf h_e_pres.fwf h_e_pres.ne h_e_pres.mono h_e_pres.rigid_inv h_closed
          have hS_abs_e : Subst.absorbs S Env_e.stateSubstInfo.subst :=
            Subst.absorbs_trans _ _ _ h_tail_pres.absorbs hS_abs
          have hS_abs_t : Subst.absorbs S Env_t.stateSubstInfo.subst :=
            Subst.absorbs_trans _ _ _ h_e_pres.absorbs hS_abs_e
          obtain ⟨C_then, Γ_then, tss_proc, h_tss_eq, h_then⟩ :=
            ih_then tss' Env_t C₀ h_t hwf₀ hfwf₀ hne₀ hmono₀ hres₀ hrigid₀ S hS_abs_t hS_wf
          obtain ⟨C_else, Γ_else, ess_proc, h_ess_eq, h_else⟩ :=
            ih_else Env_t C₀ ess' Env_e C₀ h_e h_t_pres.wf h_t_pres.fwf h_t_pres.ne h_t_pres.mono
              h_res_t h_t_pres.rigid_inv S hS_abs_e hS_wf
          simp only [List.reverse_nil, List.nil_append] at h_tss_eq h_ess_eq
          subst h_tss_eq; subst h_ess_eq
          rw [h_ctx_t] at h_else
          obtain ⟨ss_proc_tail, h_eq_tail, h_typed_tail⟩ :=
            ih_tail (Stmt.ite .nondet tss' ess' md₀) Env_e C₀ ss'₀ Env'₀ C'₀ h_goeq
              h_e_pres.wf h_e_pres.fwf h_e_pres.ne h_e_pres.mono h_res_e h_e_pres.rigid_inv
              S hS_abs hS_wf
          rw [h_ctx_e, h_ctx_t] at h_typed_tail
          refine ⟨Stmt.ite .nondet tss' ess' md₀ :: ss_proc_tail, ?_, ?_⟩
          · rw [h_eq_tail]; simp
          · simp only [List.map_cons, Core.Statement.Statement.subst,
              Imperative.ExprOrNondet.map, Statement.subst_go_nil]
            exact StmtsHasType'.cons _ _ _ _ _ _ _ _
              (StmtHasType'.ite_nondet C₀ (TContext.subst Env₀.context S) C_then Γ_then
                C_else Γ_else (List.map (Core.Statement.Statement.subst S) tss')
                (List.map (Core.Statement.Statement.subst S) ess') md₀ h_then h_else)
              h_typed_tail
  case case_loop =>
    intro C₀ Env₀ acc₀ labels₀ srest₀ guard₀ measure₀ invariant₀ bss₀ md₀ ih_tail ih_body
      ss'₀ Env'₀ C'₀ h_goeq hwf₀ hfwf₀ hne₀ hmono₀ hres₀ hrigid₀ S hS_abs hS_wf
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
      have h_wf_g : TEnvWF (T := CoreLParams) Env_g :=
        resolve_TEnvWF g ga C₀ Env₀ Env_g h_res_g hwf₀ hfwf₀
      have h_ne_g : Env_g.context.types ≠ [] := by rw [h_ctx_g]; exact hne₀
      have h_mono_g : ContextMono Env_g.context := by rw [h_ctx_g]; exact hmono₀
      have h_res_resolved_g : TContext.AliasesResolved Env_g.context := by
        unfold TContext.AliasesResolved at hres₀ ⊢; rw [h_ctx_g]; exact hres₀
      elim_err h_body with mres mres_eq
      obtain ⟨mtOpt, Env_m⟩ := mres
      elim_err h_body with fres fres_eq
      obtain ⟨it, Env_inv⟩ := fres
      elim_err h_body with cac_v cac_eq
      simp only at fres_eq cac_eq h_body
      obtain ⟨h_ctx_m, h_abs_m, h_wf_m, h_meas_wit⟩ :
          Env_m.context = Env_g.context ∧
          Subst.absorbs Env_m.stateSubstInfo.subst Env_g.stateSubstInfo.subst ∧
          TEnvWF (T := CoreLParams) Env_m ∧
          (∀ m, measure₀ = some m → ∃ ma, mtOpt = some ma ∧
            LExpr.resolve C₀ Env_g m = .ok (ma, Env_m)) := by
        cases measure₀ with
        | none =>
          simp only [Except.ok.injEq, Prod.mk.injEq] at mres_eq
          obtain ⟨_, h_em⟩ := mres_eq
          subst h_em
          refine ⟨rfl, Subst.absorbs_refl _ Env_g.stateSubstInfo.isWF, h_wf_g, ?_⟩
          intro m h_eq; simp only [reduceCtorEq] at h_eq
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
          refine ⟨resolve_preserves_context m ma C₀ Env_g Env_ma h_res_m h_wf_g h_ne_g hfwf₀,
            resolve_absorbs m ma C₀ Env_g Env_ma h_res_m h_wf_g h_ne_g hfwf₀,
            resolve_TEnvWF m ma C₀ Env_g Env_ma h_res_m h_wf_g hfwf₀, ?_⟩
          intro m' h_eq; simp only [Option.some.injEq] at h_eq; subst h_eq
          exact ⟨ma, rfl, h_res_m⟩
      have h_ne_m : Env_m.context.types ≠ [] := by rw [h_ctx_m]; exact h_ne_g
      have h_mono_m : ContextMono Env_m.context := by rw [h_ctx_m]; exact h_mono_g
      have h_res_resolved_m : TContext.AliasesResolved Env_m.context := by
        unfold TContext.AliasesResolved at h_res_resolved_g ⊢; rw [h_ctx_m]; exact h_res_resolved_g
      have h_meas_int : ∀ ma, mtOpt = some ma → ma.toLMonoTy = LMonoTy.int := by
        intro ma h_ma
        rw [h_ma] at h_body
        simp only [Option.map_some] at h_body
        split at h_body
        · rename_i h_disc; simp only [reduceCtorEq] at h_disc
        · rename_i ty h_disc
          simp only [Option.some.injEq] at h_disc
          rw [h_disc]; rfl
        · simp only [reduceCtorEq] at h_body
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
      -- Env threading across the invariant fold (`foldlM_env_threading`).
      obtain ⟨h_ctx_inv, h_abs_inv, h_wf_inv, _, _⟩ :=
        foldlM_env_threading _ (fun E E' p => True) (by
          intro accp E p accp' E' h_wf_E h_ne_E h_stepeq
          elim_err h_stepeq with sfvc_v sfvc_eq
          elim_err h_stepeq with sres_v sres_eq
          obtain ⟨ia, E_ia⟩ := sres_v
          have h_res_p : LExpr.resolve C₀ E p.2 = .ok (ia, E_ia) := by
            split at sres_eq
            · simp only [reduceCtorEq] at sres_eq
            · rename_i w h_rp
              rw [Except.ok.injEq] at sres_eq; subst sres_eq; exact h_rp
          split at h_stepeq
          · rw [Except.ok.injEq, Prod.mk.injEq] at h_stepeq
            obtain ⟨_, h_E'⟩ := h_stepeq
            subst h_E'
            exact ⟨resolve_preserves_context p.2 ia C₀ E E_ia h_res_p h_wf_E h_ne_E hfwf₀,
              resolve_absorbs p.2 ia C₀ E E_ia h_res_p h_wf_E h_ne_E hfwf₀,
              resolve_TEnvWF p.2 ia C₀ E E_ia h_res_p h_wf_E hfwf₀,
              resolve_genState_mono C₀ E E_ia p.2 ia h_res_p h_wf_E hfwf₀, trivial⟩
          · simp only [reduceCtorEq] at h_stepeq)
          invariant₀ [] Env_m Env_inv it h_wf_m h_ne_m fres_eq
      -- Output invariant typings via `foldlM_output_facts`.
      have h_inv_out : ∀ o, o ∈ it →
          Lambda.LExpr.HasTypeA [] (o.2.unresolved.applySubst S) .bool := by
        have h_facts := foldlM_output_facts _
          (fun o => Lambda.LExpr.HasTypeA [] (o.2.unresolved.applySubst S) .bool) (by
            intro accp E p accp' E' h_wf_E h_ne_E h_res_E h_stepeq
            elim_err h_stepeq with sfvc_v sfvc_eq
            elim_err h_stepeq with sres_v sres_eq
            obtain ⟨ia, E_ia⟩ := sres_v
            have h_res_p : LExpr.resolve C₀ E p.2 = .ok (ia, E_ia) := by
              split at sres_eq
              · simp only [reduceCtorEq] at sres_eq
              · rename_i w h_rp
                rw [Except.ok.injEq] at sres_eq; subst sres_eq; exact h_rp
            split at h_stepeq
            · rename_i h_isbool
              rw [Except.ok.injEq, Prod.mk.injEq] at h_stepeq
              obtain ⟨h_accp', h_E'⟩ := h_stepeq
              subst h_E'
              have h_bool : ia.toLMonoTy = LMonoTy.bool := by
                simp only [beq_iff_eq] at h_isbool; exact h_isbool
              refine ⟨resolve_preserves_context p.2 ia C₀ E E_ia h_res_p h_wf_E h_ne_E hfwf₀,
                resolve_TEnvWF p.2 ia C₀ E E_ia h_res_p h_wf_E hfwf₀, (p.1, ia), h_accp'.symm, ?_⟩
              exact resolve_bool_HasTypeA C₀ E E_ia p.2 ia S h_res_p h_bool h_wf_E hfwf₀ h_res_E
            · simp only [reduceCtorEq] at h_stepeq)
          invariant₀ [] it Env_m Env_inv h_wf_m h_ne_m h_res_resolved_m fres_eq
        intro o ho
        rcases h_facts o ho with h_nil | h_q
        · exact absurd h_nil (List.not_mem_nil)
        · exact h_q
      have h_rigid_inv : ∀ v, v ∈ C₀.rigidTypeVars →
          LMonoTy.subst Env_inv.stateSubstInfo.subst (.ftvar v) = .ftvar v :=
        CmdType.checkAnnotCompat_rigid C₀ Env_inv cac_eq
      have h_ctx_inv0 : Env_inv.context = Env₀.context := by
        rw [h_ctx_inv, h_ctx_m, h_ctx_g]
      have h_ne_inv : Env_inv.context.types ≠ [] := by rw [h_ctx_inv0]; exact hne₀
      have h_mono_inv : ContextMono Env_inv.context := by rw [h_ctx_inv0]; exact hmono₀
      have h_res_inv : TContext.AliasesResolved Env_inv.context := by
        unfold TContext.AliasesResolved at hres₀ ⊢; rw [h_ctx_inv0]; exact hres₀
      obtain ⟨h_loop_pres, h_Cloop⟩ := goBlock_eq_GoPreserved P op C₀ Env_inv bss₀ [] labels₀
        tb Env_loop C_loop h_gb_eq h_wf_inv hfwf₀ h_ne_inv h_mono_inv h_rigid_inv h_closed
      rw [h_Cloop] at h_gb_eq h_goeq
      have h_ctx_loop : Env_loop.context = Env_inv.context :=
        goBlock_preserves_context P op C₀ Env_inv bss₀ [] labels₀ tb Env_loop C₀
          h_gb_eq h_wf_inv hfwf₀ h_mono_inv h_rigid_inv h_closed
      have h_res_loop : TContext.AliasesResolved Env_loop.context := by
        unfold TContext.AliasesResolved at h_res_inv ⊢; rw [h_ctx_loop]; exact h_res_inv
      have h_tail_pres : GoPreserved C₀ C'₀ Env_loop Env'₀ :=
        typeCheckAux_go_preserves C₀ Env_loop P op srest₀
          (Stmt.loop (ExprOrNondet.det (unresolved ga)) (Option.map unresolved mtOpt)
            (List.map (fun x => (x.fst, unresolved x.snd)) it) tb md₀ :: acc₀) labels₀
          ss'₀ Env'₀ C'₀ h_goeq h_loop_pres.wf h_loop_pres.fwf h_loop_pres.ne h_loop_pres.mono
          h_loop_pres.rigid_inv h_closed
      have hS_abs_loop : Subst.absorbs S Env_loop.stateSubstInfo.subst :=
        Subst.absorbs_trans _ _ _ h_tail_pres.absorbs hS_abs
      have hS_abs_inv : Subst.absorbs S Env_inv.stateSubstInfo.subst :=
        Subst.absorbs_trans _ _ _ h_loop_pres.absorbs hS_abs_loop
      have hS_abs_m : Subst.absorbs S Env_m.stateSubstInfo.subst :=
        Subst.absorbs_trans _ _ _ h_abs_inv hS_abs_inv
      have hS_abs_g : Subst.absorbs S Env_g.stateSubstInfo.subst :=
        Subst.absorbs_trans _ _ _ h_abs_m hS_abs_m
      -- Output guard typing via `resolve_bool_HasTypeA`.
      have h_guard_ty : Lambda.LExpr.HasTypeA [] (ga.unresolved.applySubst S) .bool :=
        resolve_bool_HasTypeA C₀ Env₀ Env_g g ga S h_res_g h_g_bool hwf₀ hfwf₀ hres₀
      -- Body typing via `ih_body` (existential body output + accumulator) at `S`.
      obtain ⟨C_body, Γ_body, bss_proc, h_bss_eq, h_body_ty⟩ :=
        ih_body Env_inv tb Env_loop C₀ h_gb_eq h_wf_inv hfwf₀ h_ne_inv h_mono_inv h_res_inv
          h_rigid_inv S hS_abs_loop hS_wf
      simp only [List.reverse_nil, List.nil_append] at h_bss_eq
      subst h_bss_eq
      rw [h_ctx_inv0] at h_body_ty
      -- Output measure typing via the `int` analogue. The output measure expression is
      -- `Option.map unresolved mtOpt`; when present it equals `mtm.unresolved` for the
      -- resolved `mtm`, which is `int`-typed.
      have h_meas_ty : ∀ m, Option.map unresolved mtOpt = some m →
          Lambda.LExpr.HasTypeA [] (m.applySubst S) .int := by
        intro m h_m
        cases h_mtOpt : mtOpt with
        | none => rw [h_mtOpt] at h_m; simp only [Option.map_none, reduceCtorEq] at h_m
        | some mtm =>
          rw [h_mtOpt] at h_m; simp only [Option.map_some, Option.some.injEq] at h_m
          subst h_m
          -- The measure must have been present (`measure₀ = some _`): else `mtOpt = none`.
          have h_meas_some : ∃ mm, measure₀ = some mm := by
            cases measure₀ with
            | none =>
              simp only [Except.ok.injEq, Prod.mk.injEq] at mres_eq
              obtain ⟨h_mt, _⟩ := mres_eq
              rw [← h_mt] at h_mtOpt; simp only [reduceCtorEq] at h_mtOpt
            | some mm => exact ⟨mm, rfl⟩
          obtain ⟨mm, h_mm⟩ := h_meas_some
          obtain ⟨mtm', h_mtOpt', h_res_m⟩ := h_meas_wit mm h_mm
          rw [h_mtOpt] at h_mtOpt'; simp only [Option.some.injEq] at h_mtOpt'
          subst h_mtOpt'
          have h_int : mtm.toLMonoTy = LMonoTy.int := h_meas_int mtm h_mtOpt
          exact resolve_int_HasTypeA C₀ Env_g Env_m mm mtm S h_res_m h_int h_wf_g hfwf₀
            h_res_resolved_g
      -- Tail via the IH at `S`.
      obtain ⟨ss_proc_tail, h_eq_tail, h_typed_tail⟩ :=
        ih_tail (Stmt.loop (ExprOrNondet.det (unresolved ga)) (Option.map unresolved mtOpt)
            (List.map (fun x => (x.fst, unresolved x.snd)) it) tb md₀) Env_loop C₀ ss'₀ Env'₀ C'₀
          h_goeq h_loop_pres.wf h_loop_pres.fwf h_loop_pres.ne h_loop_pres.mono h_res_loop
          h_loop_pres.rigid_inv S hS_abs hS_wf
      rw [h_ctx_loop, h_ctx_inv0] at h_typed_tail
      refine ⟨Stmt.loop (ExprOrNondet.det (unresolved ga)) (Option.map unresolved mtOpt)
          (List.map (fun x => (x.fst, unresolved x.snd)) it) tb md₀ :: ss_proc_tail, ?_, ?_⟩
      · rw [h_eq_tail]; simp
      · simp only [List.map_cons, Core.Statement.Statement.subst, Statement.subst_go_nil]
        refine StmtsHasType'.cons _ _ _ _ _ _ _ _
          (StmtHasType'.loop C₀ (TContext.subst Env₀.context S) C_body Γ_body
            _ _ _ (List.map (Core.Statement.Statement.subst S) tb) md₀ ?_ ?_ ?_ h_body_ty)
          h_typed_tail
        · intro g' h_g'
          simp only [Imperative.ExprOrNondet.map, ExprOrNondet.det.injEq] at h_g'
          rw [← h_g']; exact h_guard_ty
        · intro m h_m
          simp only [Statement.substOptionExpr] at h_m
          cases h_mo : Option.map unresolved mtOpt with
          | none => rw [h_mo] at h_m; simp only [reduceCtorEq] at h_m
          | some mo =>
            rw [h_mo] at h_m; simp only [Option.some.injEq] at h_m
            rw [← h_m]; exact h_meas_ty mo h_mo
        · intro p h_mem
          simp only [List.map_map, List.mem_map] at h_mem
          obtain ⟨y, h_y_mem, h_y_eq⟩ := h_mem
          rw [← h_y_eq]
          simp only [Function.comp]
          exact h_inv_out y h_y_mem
    | nondet =>
      simp only [pure, Except.pure] at h_body
      elim_err h_body with mres mres_eq
      obtain ⟨mtOpt, Env_m⟩ := mres
      elim_err h_body with fres fres_eq
      obtain ⟨it, Env_inv⟩ := fres
      elim_err h_body with cac_v cac_eq
      simp only at fres_eq cac_eq h_body
      obtain ⟨h_ctx_m, h_abs_m, h_wf_m, h_meas_wit⟩ :
          Env_m.context = Env₀.context ∧
          Subst.absorbs Env_m.stateSubstInfo.subst Env₀.stateSubstInfo.subst ∧
          TEnvWF (T := CoreLParams) Env_m ∧
          (∀ m, measure₀ = some m → ∃ ma, mtOpt = some ma ∧
            LExpr.resolve C₀ Env₀ m = .ok (ma, Env_m)) := by
        cases measure₀ with
        | none =>
          simp only [Except.ok.injEq, Prod.mk.injEq] at mres_eq
          obtain ⟨_, h_em⟩ := mres_eq
          subst h_em
          refine ⟨rfl, Subst.absorbs_refl _ Env₀.stateSubstInfo.isWF, hwf₀, ?_⟩
          intro m h_eq; simp only [reduceCtorEq] at h_eq
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
          refine ⟨resolve_preserves_context m ma C₀ Env₀ Env_ma h_res_m hwf₀ hne₀ hfwf₀,
            resolve_absorbs m ma C₀ Env₀ Env_ma h_res_m hwf₀ hne₀ hfwf₀,
            resolve_TEnvWF m ma C₀ Env₀ Env_ma h_res_m hwf₀ hfwf₀, ?_⟩
          intro m' h_eq; simp only [Option.some.injEq] at h_eq; subst h_eq
          exact ⟨ma, rfl, h_res_m⟩
      have h_ne_m : Env_m.context.types ≠ [] := by rw [h_ctx_m]; exact hne₀
      have h_mono_m : ContextMono Env_m.context := by rw [h_ctx_m]; exact hmono₀
      have h_res_resolved_m : TContext.AliasesResolved Env_m.context := by
        unfold TContext.AliasesResolved at hres₀ ⊢; rw [h_ctx_m]; exact hres₀
      have h_meas_int : ∀ ma, mtOpt = some ma → ma.toLMonoTy = LMonoTy.int := by
        intro ma h_ma
        rw [h_ma] at h_body
        simp only [Option.map_some] at h_body
        split at h_body
        · rename_i h_disc; simp only [reduceCtorEq] at h_disc
        · rename_i ty h_disc
          simp only [Option.some.injEq] at h_disc
          rw [h_disc]; rfl
        · simp only [reduceCtorEq] at h_body
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
      obtain ⟨h_ctx_inv, h_abs_inv, h_wf_inv, _, _⟩ :=
        foldlM_env_threading _ (fun E E' p => True) (by
          intro accp E p accp' E' h_wf_E h_ne_E h_stepeq
          elim_err h_stepeq with sfvc_v sfvc_eq
          elim_err h_stepeq with sres_v sres_eq
          obtain ⟨ia, E_ia⟩ := sres_v
          have h_res_p : LExpr.resolve C₀ E p.2 = .ok (ia, E_ia) := by
            split at sres_eq
            · simp only [reduceCtorEq] at sres_eq
            · rename_i w h_rp
              rw [Except.ok.injEq] at sres_eq; subst sres_eq; exact h_rp
          split at h_stepeq
          · rw [Except.ok.injEq, Prod.mk.injEq] at h_stepeq
            obtain ⟨_, h_E'⟩ := h_stepeq
            subst h_E'
            exact ⟨resolve_preserves_context p.2 ia C₀ E E_ia h_res_p h_wf_E h_ne_E hfwf₀,
              resolve_absorbs p.2 ia C₀ E E_ia h_res_p h_wf_E h_ne_E hfwf₀,
              resolve_TEnvWF p.2 ia C₀ E E_ia h_res_p h_wf_E hfwf₀,
              resolve_genState_mono C₀ E E_ia p.2 ia h_res_p h_wf_E hfwf₀, trivial⟩
          · simp only [reduceCtorEq] at h_stepeq)
          invariant₀ [] Env_m Env_inv it h_wf_m h_ne_m fres_eq
      have h_inv_out : ∀ o, o ∈ it →
          Lambda.LExpr.HasTypeA [] (o.2.unresolved.applySubst S) .bool := by
        have h_facts := foldlM_output_facts _
          (fun o => Lambda.LExpr.HasTypeA [] (o.2.unresolved.applySubst S) .bool) (by
            intro accp E p accp' E' h_wf_E h_ne_E h_res_E h_stepeq
            elim_err h_stepeq with sfvc_v sfvc_eq
            elim_err h_stepeq with sres_v sres_eq
            obtain ⟨ia, E_ia⟩ := sres_v
            have h_res_p : LExpr.resolve C₀ E p.2 = .ok (ia, E_ia) := by
              split at sres_eq
              · simp only [reduceCtorEq] at sres_eq
              · rename_i w h_rp
                rw [Except.ok.injEq] at sres_eq; subst sres_eq; exact h_rp
            split at h_stepeq
            · rename_i h_isbool
              rw [Except.ok.injEq, Prod.mk.injEq] at h_stepeq
              obtain ⟨h_accp', h_E'⟩ := h_stepeq
              subst h_E'
              have h_bool : ia.toLMonoTy = LMonoTy.bool := by
                simp only [beq_iff_eq] at h_isbool; exact h_isbool
              refine ⟨resolve_preserves_context p.2 ia C₀ E E_ia h_res_p h_wf_E h_ne_E hfwf₀,
                resolve_TEnvWF p.2 ia C₀ E E_ia h_res_p h_wf_E hfwf₀, (p.1, ia), h_accp'.symm, ?_⟩
              exact resolve_bool_HasTypeA C₀ E E_ia p.2 ia S h_res_p h_bool h_wf_E hfwf₀ h_res_E
            · simp only [reduceCtorEq] at h_stepeq)
          invariant₀ [] it Env_m Env_inv h_wf_m h_ne_m h_res_resolved_m fres_eq
        intro o ho
        rcases h_facts o ho with h_nil | h_q
        · exact absurd h_nil (List.not_mem_nil)
        · exact h_q
      have h_rigid_inv : ∀ v, v ∈ C₀.rigidTypeVars →
          LMonoTy.subst Env_inv.stateSubstInfo.subst (.ftvar v) = .ftvar v :=
        CmdType.checkAnnotCompat_rigid C₀ Env_inv cac_eq
      have h_ctx_inv0 : Env_inv.context = Env₀.context := by rw [h_ctx_inv, h_ctx_m]
      have h_ne_inv : Env_inv.context.types ≠ [] := by rw [h_ctx_inv0]; exact hne₀
      have h_mono_inv : ContextMono Env_inv.context := by rw [h_ctx_inv0]; exact hmono₀
      have h_res_inv : TContext.AliasesResolved Env_inv.context := by
        unfold TContext.AliasesResolved at hres₀ ⊢; rw [h_ctx_inv0]; exact hres₀
      obtain ⟨h_loop_pres, h_Cloop⟩ := goBlock_eq_GoPreserved P op C₀ Env_inv bss₀ [] labels₀
        tb Env_loop C_loop h_gb_eq h_wf_inv hfwf₀ h_ne_inv h_mono_inv h_rigid_inv h_closed
      rw [h_Cloop] at h_gb_eq h_goeq
      have h_ctx_loop : Env_loop.context = Env_inv.context :=
        goBlock_preserves_context P op C₀ Env_inv bss₀ [] labels₀ tb Env_loop C₀
          h_gb_eq h_wf_inv hfwf₀ h_mono_inv h_rigid_inv h_closed
      have h_res_loop : TContext.AliasesResolved Env_loop.context := by
        unfold TContext.AliasesResolved at h_res_inv ⊢; rw [h_ctx_loop]; exact h_res_inv
      have h_tail_pres : GoPreserved C₀ C'₀ Env_loop Env'₀ :=
        typeCheckAux_go_preserves C₀ Env_loop P op srest₀
          (Stmt.loop ExprOrNondet.nondet (Option.map unresolved mtOpt)
            (List.map (fun x => (x.fst, unresolved x.snd)) it) tb md₀ :: acc₀) labels₀
          ss'₀ Env'₀ C'₀ h_goeq h_loop_pres.wf h_loop_pres.fwf h_loop_pres.ne h_loop_pres.mono
          h_loop_pres.rigid_inv h_closed
      have hS_abs_loop : Subst.absorbs S Env_loop.stateSubstInfo.subst :=
        Subst.absorbs_trans _ _ _ h_tail_pres.absorbs hS_abs
      have hS_abs_inv : Subst.absorbs S Env_inv.stateSubstInfo.subst :=
        Subst.absorbs_trans _ _ _ h_loop_pres.absorbs hS_abs_loop
      have hS_abs_m : Subst.absorbs S Env_m.stateSubstInfo.subst :=
        Subst.absorbs_trans _ _ _ h_abs_inv hS_abs_inv
      obtain ⟨C_body, Γ_body, bss_proc, h_bss_eq, h_body_ty⟩ :=
        ih_body Env_inv tb Env_loop C₀ h_gb_eq h_wf_inv hfwf₀ h_ne_inv h_mono_inv h_res_inv
          h_rigid_inv S hS_abs_loop hS_wf
      simp only [List.reverse_nil, List.nil_append] at h_bss_eq
      subst h_bss_eq
      rw [h_ctx_inv0] at h_body_ty
      have h_meas_ty : ∀ m, Option.map unresolved mtOpt = some m →
          Lambda.LExpr.HasTypeA [] (m.applySubst S) .int := by
        intro m h_m
        cases h_mtOpt : mtOpt with
        | none => rw [h_mtOpt] at h_m; simp only [Option.map_none, reduceCtorEq] at h_m
        | some mtm =>
          rw [h_mtOpt] at h_m; simp only [Option.map_some, Option.some.injEq] at h_m
          subst h_m
          have h_meas_some : ∃ mm, measure₀ = some mm := by
            cases measure₀ with
            | none =>
              simp only [Except.ok.injEq, Prod.mk.injEq] at mres_eq
              obtain ⟨h_mt, _⟩ := mres_eq
              rw [← h_mt] at h_mtOpt; simp only [reduceCtorEq] at h_mtOpt
            | some mm => exact ⟨mm, rfl⟩
          obtain ⟨mm, h_mm⟩ := h_meas_some
          obtain ⟨mtm', h_mtOpt', h_res_m⟩ := h_meas_wit mm h_mm
          rw [h_mtOpt] at h_mtOpt'; simp only [Option.some.injEq] at h_mtOpt'
          subst h_mtOpt'
          have h_int : mtm.toLMonoTy = LMonoTy.int := h_meas_int mtm h_mtOpt
          exact resolve_int_HasTypeA C₀ Env₀ Env_m mm mtm S h_res_m h_int hwf₀ hfwf₀ hres₀
      obtain ⟨ss_proc_tail, h_eq_tail, h_typed_tail⟩ :=
        ih_tail (Stmt.loop ExprOrNondet.nondet (Option.map unresolved mtOpt)
            (List.map (fun x => (x.fst, unresolved x.snd)) it) tb md₀) Env_loop C₀ ss'₀ Env'₀ C'₀
          h_goeq h_loop_pres.wf h_loop_pres.fwf h_loop_pres.ne h_loop_pres.mono h_res_loop
          h_loop_pres.rigid_inv S hS_abs hS_wf
      rw [h_ctx_loop, h_ctx_inv0] at h_typed_tail
      refine ⟨Stmt.loop ExprOrNondet.nondet (Option.map unresolved mtOpt)
          (List.map (fun x => (x.fst, unresolved x.snd)) it) tb md₀ :: ss_proc_tail, ?_, ?_⟩
      · rw [h_eq_tail]; simp
      · simp only [List.map_cons, Core.Statement.Statement.subst, Statement.subst_go_nil]
        refine StmtsHasType'.cons _ _ _ _ _ _ _ _
          (StmtHasType'.loop C₀ (TContext.subst Env₀.context S) C_body Γ_body
            _ _ _ (List.map (Core.Statement.Statement.subst S) tb) md₀ ?_ ?_ ?_ h_body_ty)
          h_typed_tail
        · intro g' h_g'
          simp only [Imperative.ExprOrNondet.map, reduceCtorEq] at h_g'
        · intro m h_m
          simp only [Statement.substOptionExpr] at h_m
          cases h_mo : Option.map unresolved mtOpt with
          | none => rw [h_mo] at h_m; simp only [reduceCtorEq] at h_m
          | some mo =>
            rw [h_mo] at h_m; simp only [Option.some.injEq] at h_m
            rw [← h_m]; exact h_meas_ty mo h_mo
        · intro p h_mem
          simp only [List.map_map, List.mem_map] at h_mem
          obtain ⟨y, h_y_mem, h_y_eq⟩ := h_mem
          rw [← h_y_eq]
          simp only [Function.comp]
          exact h_inv_out y h_y_mem
  case case_exit =>
    intro C₀ Env₀ acc₀ labels₀ srest₀ l₀ md₀ ih_tail ss'₀ Env'₀ C'₀ h_goeq hwf₀ hfwf₀ hne₀ hmono₀
      hres₀ hrigid₀ S hS_abs hS_wf
    unfold Statement.typeCheckAux.go at h_goeq
    simp only [Bind.bind, Except.bind, tryCatchThe, tryCatch, MonadExcept.tryCatch,
      MonadExceptOf.tryCatch, Except.tryCatch] at h_goeq
    cases op with
    | none => simp only [reduceCtorEq] at h_goeq
    | some proc =>
      by_cases h_lbl : labels₀.contains l₀
      · simp only [h_lbl, if_true] at h_goeq
        obtain ⟨ss_proc_tail, h_eq_tail, h_typed_tail⟩ :=
          ih_tail (Stmt.exit l₀ md₀) Env₀ C₀ ss'₀ Env'₀ C'₀ h_goeq hwf₀ hfwf₀ hne₀ hmono₀ hres₀
            hrigid₀ S hS_abs hS_wf
        refine ⟨Stmt.exit l₀ md₀ :: ss_proc_tail, ?_, ?_⟩
        · rw [h_eq_tail]; simp
        · simp only [List.map_cons, Core.Statement.Statement.subst]
          exact StmtsHasType'.cons _ _ _ _ _ _ _ _ (StmtHasType'.exit _ _ l₀ md₀) h_typed_tail
      · simp only [h_lbl, if_false, Bool.false_eq_true, reduceCtorEq] at h_goeq
  case case_funcDecl =>
    intro C₀ Env₀ acc₀ labels₀ srest₀ decl₀ md₀ ih_tail ss'₀ Env'₀ C'₀ h_goeq hwf₀ hfwf₀ hne₀ hmono₀
      hres₀ hrigid₀ S hS_abs hS_wf
    -- Inline the `funcDecl` inversion (S0), retaining `decl'`'s definition so we can
    -- discharge `¬ decl'.isRecursive` (it is `false` by structure default).
    unfold Statement.typeCheckAux.go at h_goeq
    simp only [Bind.bind, Except.bind, tryCatchThe, tryCatch, MonadExcept.tryCatch,
      MonadExceptOf.tryCatch, Except.tryCatch] at h_goeq
    cases h_rec : decl₀.isRecursive with
    | true => rw [h_rec] at h_goeq; simp only [if_true, reduceCtorEq] at h_goeq
    | false =>
      rw [h_rec] at h_goeq
      simp only [if_false, Bool.false_eq_true] at h_goeq
      cases h_pf : PureFunc.typeCheck C₀ Env₀ decl₀ with
      | error e =>
        rw [h_pf] at h_goeq
        simp only [Except.mapError, pure, Except.pure, reduceCtorEq] at h_goeq
      | ok v =>
        obtain ⟨decl', func, Env_mid⟩ := v
        rw [h_pf] at h_goeq
        simp only [Except.mapError] at h_goeq
        unfold PureFunc.typeCheck at h_pf
        simp only [Bind.bind, Except.bind] at h_pf
        cases h_of : Function.ofPureFunc decl₀ with
        | error e => rw [h_of] at h_pf; simp only [reduceCtorEq] at h_pf
        | ok func0 =>
          rw [h_of] at h_pf
          simp only at h_pf
          cases h_ft : Function.typeCheck C₀ Env₀ func0 with
          | error e => rw [h_ft] at h_pf; simp only [reduceCtorEq] at h_pf
          | ok w =>
            obtain ⟨func', Env2⟩ := w
            rw [h_ft] at h_pf
            simp only [Except.ok.injEq, Prod.mk.injEq] at h_pf
            obtain ⟨h_decl'_eq, h_func_eq, h_env_eq⟩ := h_pf
            subst h_func_eq
            subst h_env_eq
            -- `h_goeq` now runs the tail on `C₀.addFactoryFunction func'` / `Env2`.
            -- Annotated soundness of the checked function, at any `Γ`.
            have h_ftype : ∀ Γ, FuncHasTypeA C₀ Γ func' :=
              Function.typeCheck_annotated_sound C₀ Env₀ func0 func' Env2 h_ft hwf₀ hfwf₀ hres₀
            have h_ctx : Env2.context = Env₀.context :=
              Function.typeCheck_context_eq C₀ Env₀ func0 func' Env2 h_ft hwf₀ hfwf₀
            have h_lfwf : Lambda.LFuncWF func' :=
              Function.typeCheck_LFuncWF C₀ Env₀ func0 func' Env2 h_ft hwf₀
            -- Threading premises for the tail IH at `C_mid = addFactoryFunction func'`, `Env2`.
            have h_wf_mid : TEnvWF (T := CoreLParams) Env2 :=
              Function.typeCheck_TEnvWF C₀ Env₀ func0 func' Env2 h_ft hwf₀ hfwf₀
            have h_fwf_mid : FactoryWF (C₀.addFactoryFunction func').functions :=
              addFactoryFunction_FactoryWF C₀ func' hfwf₀ h_lfwf
            have h_ne_mid : Env2.context.types ≠ [] := by rw [h_ctx]; exact hne₀
            have h_mono_mid : ContextMono Env2.context := by rw [h_ctx]; exact hmono₀
            have h_res_mid : TContext.AliasesResolved Env2.context := by rw [h_ctx]; exact hres₀
            have h_rigid_mid : ∀ v, v ∈ (C₀.addFactoryFunction func').rigidTypeVars →
                LMonoTy.subst Env2.stateSubstInfo.subst (.ftvar v) = .ftvar v := by
              rw [addFactoryFunction_rigidTypeVars]
              exact Function.typeCheck_preserves_rigid_inv C₀ Env₀ func0 func' Env2 h_ft hwf₀ hfwf₀
                hrigid₀
            obtain ⟨ss_proc_tail, h_eq_tail, h_typed_tail⟩ :=
              ih_tail (Stmt.funcDecl decl' md₀) Env2 (C₀.addFactoryFunction func') ss'₀ Env'₀ C'₀
                h_goeq h_wf_mid h_fwf_mid h_ne_mid h_mono_mid h_res_mid h_rigid_mid S hS_abs hS_wf
            rw [h_ctx] at h_typed_tail
            refine ⟨Stmt.funcDecl decl' md₀ :: ss_proc_tail, ?_, ?_⟩
            · rw [h_eq_tail]; simp
            · simp only [List.map_cons, Core.Statement.Statement.subst]
              refine StmtsHasType'.cons _ _ _ _ _ _ _ _
                (StmtHasType'.funcDecl C₀ (TContext.subst Env₀.context S) _ func' md₀ ?_
                  (h_ftype _)) h_typed_tail
              -- `¬ (subst S decl').isRecursive`: `Statement.subst` preserves `isRecursive`,
              -- and `decl'` (from `PureFunc.typeCheck`) omits `isRecursive` ⇒ default `false`.
              rw [← h_decl'_eq]; simp
  case case_typeDecl =>
    intro C₀ Env₀ acc₀ labels₀ srest₀ tc₀ md₀ ih_tail ss'₀ Env'₀ C'₀ h_goeq hwf₀ hfwf₀ hne₀ hmono₀
      hres₀ hrigid₀ S hS_abs hS_wf
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
      have hS_rigid_mid : ∀ v, v ∈ C_mid.rigidTypeVars →
          LMonoTy.subst Env₀.stateSubstInfo.subst (.ftvar v) = .ftvar v := by rw [h_rig]; exact hrigid₀
      -- `typeDecl` leaves `Env` (hence context/aliases) unchanged.
      obtain ⟨ss_proc_tail, h_eq_tail, h_typed_tail⟩ :=
        ih_tail (Stmt.typeDecl tc₀ md₀) Env₀ C_mid ss'₀ Env'₀ C'₀ h_goeq hwf₀ (h_fns ▸ hfwf₀)
          hne₀ hmono₀ hres₀ hS_rigid_mid S hS_abs hS_wf
      refine ⟨Stmt.typeDecl tc₀ md₀ :: ss_proc_tail, ?_, ?_⟩
      · rw [h_eq_tail]; simp
      · simp only [List.map_cons, Core.Statement.Statement.subst]
        refine StmtsHasType'.cons _ _ _ _ _ _ _ _
          (StmtHasType'.typeDecl C₀ C_mid _ tc₀ md₀ ?_) h_typed_tail
        exact addKnownTypeWithError_diag_irrel C₀ C_mid _ _ default h_add
  case case_goBlock =>
    intro C₀ Env₀ bss₀ acc₀ labels₀ Env₁ ih_body ss'₀ Env'₀ C'₀ h_goeq hwf₀ hfwf₀ hne₀ hmono₀
      hres₀ hrigid₀ S hS_abs hS_wf
    unfold Statement.typeCheckAux.goBlock at h_goeq
    simp only [Bind.bind, Except.bind] at h_goeq
    cases h_body_run : Statement.typeCheckAux.go P op C₀ Env₀.pushEmptyContext bss₀ acc₀ labels₀ with
    | error e => rw [h_body_run] at h_goeq; simp only [reduceCtorEq] at h_goeq
    | ok v =>
      obtain ⟨bss', Env_body, C_body⟩ := v
      rw [h_body_run] at h_goeq
      simp only [Except.ok.injEq, Prod.mk.injEq] at h_goeq
      obtain ⟨hss, hEnv, hC⟩ := h_goeq
      subst hEnv; subst hC
      have h_push_wf : TEnvWF (T := CoreLParams) Env₀.pushEmptyContext :=
        pushEmptyContext_TEnvWF Env₀ hwf₀
      have h_push_ne : Env₀.pushEmptyContext.context.types ≠ [] := by
        simp only [TEnv.pushEmptyContext, TEnv.updateContext, TEnv.context, Maps.push]
        exact List.cons_ne_nil _ _
      have h_push_mono : ContextMono Env₀.pushEmptyContext.context :=
        pushEmptyContext_ContextMono Env₀ hmono₀
      have h_push_rigid : ∀ v, v ∈ C₀.rigidTypeVars →
          LMonoTy.subst Env₀.pushEmptyContext.stateSubstInfo.subst (.ftvar v) = .ftvar v := hrigid₀
      -- `pushEmptyContext` preserves `AliasesResolved` (it only changes `types`).
      have h_push_res : TContext.AliasesResolved Env₀.pushEmptyContext.context := by
        unfold TContext.AliasesResolved at hres₀ ⊢
        have h_al : Env₀.pushEmptyContext.context.aliases = Env₀.context.aliases := by
          simp only [TEnv.pushEmptyContext, TEnv.updateContext, TEnv.context]
        rw [h_al]; exact hres₀
      have hS_abs_body : Subst.absorbs S Env_body.stateSubstInfo.subst := hS_abs
      -- Body typing via the inner-`go` IH (motive1) at `S`, pushed Γ.
      obtain ⟨bss_proc, h_bss_eq, h_body_typed⟩ :=
        ih_body bss' Env_body C_body h_body_run h_push_wf hfwf₀ h_push_ne h_push_mono h_push_res
          h_push_rigid S hS_abs_body hS_wf
      -- `goBlock` returns `bss'` as its output list, so `ss'₀ = bss'`.
      subst hss
      -- Bridge the INPUT Γ from `subst (push Env₀).context S` to `subst Env₀.context S`
      -- (they agree on `find?`/`aliases`); `HasTypeA` ignores Γ so the expr-congruence is trivial.
      have h_expr_congr : ∀ (Γa Γb : TContext Unit) (Cx : LContext CoreLParams)
          (e : Expression.Expr) (t : LMonoTy),
          (∀ x, Γb.types.find? x = Γa.types.find? x) → Γb.aliases = Γa.aliases →
          instHasTypeA.exprTyped Cx Γa e t → instHasTypeA.exprTyped Cx Γb e t :=
        fun _ _ _ _ _ _ _ h_e => h_e
      have h_al_bridge : (TContext.subst Env₀.pushEmptyContext.context S).aliases
          = (TContext.subst Env₀.context S).aliases := by
        rw [TContext.subst_aliases, TContext.subst_aliases]
        simp only [TEnv.pushEmptyContext, TEnv.updateContext, TEnv.context]
      obtain ⟨Γ_body', _, _, h_body_plain⟩ :=
        StmtsHasType'_find_congr h_expr_congr h_body_typed (TContext.subst Env₀.context S)
          (fun y => subst_pushEmptyContext_find? Env₀ S y) h_al_bridge
      -- The output `goBlock` env discards the body's `Γ`, so the body output context is
      -- existential; supply `C_body` and the bridged Γ.
      exact ⟨C_body, Γ_body', bss_proc, h_bss_eq, h_body_plain⟩

/--
Annotated soundness of the statement typechecker (Part II): if
`Statement.typeCheck` succeeds, the output statements (with the final substitution
applied) satisfy `StmtsHasTypeA`.
-/
theorem Statement.typeCheck_annotated_sound (C : LContext CoreLParams) (Env : TEnv Unit)
    (P : Program) (op : Option Procedure) (ss ss' : List Statement) (Env' : TEnv Unit)
    (h : Statement.typeCheck C Env P op ss = .ok (ss', Env'))
    (h_wf : TEnvWF (T := CoreLParams) Env)
    (h_fwf : FactoryWF C.functions)
    (h_ne : Env.context.types ≠ [])
    (h_mono : ContextMono Env.context)
    (h_resolved : TContext.AliasesResolved Env.context)
    (h_rigid_inv : ∀ v, v ∈ C.rigidTypeVars →
      LMonoTy.subst Env.stateSubstInfo.subst (.ftvar v) = .ftvar v)
    (h_closed : CalledProcsClosed P) :
    ∃ C', StmtsHasTypeA P C (TContext.subst Env.context Env'.stateSubstInfo.subst)
      ss' C' Env'.context := by
  unfold Statement.typeCheck Statement.typeCheckAux at h
  cases h_go : Statement.typeCheckAux.go P op C Env ss [] [] with
  | error e => rw [h_go] at h; simp only [bind, Except.bind] at h; cases h
  | ok v_aux =>
    obtain ⟨ss_aux, Env_aux, C_aux⟩ := v_aux
    rw [h_go] at h
    simp only [bind, Except.bind, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨h_ss, h_env⟩ := h
    refine ⟨C_aux, ?_⟩
    have h_core := typeCheckAux_go_annotated_sound C Env P op ss [] ss_aux Env_aux C_aux
      h_go h_wf h_fwf h_ne h_mono h_resolved h_rigid_inv h_closed
    -- `ss' = subst.go Env_aux.subst ss_aux []` = `map (subst Env_aux.subst) ss_aux`,
    -- which is exactly the core lemma's output list. And `Env'.subst = Env_aux.subst`,
    -- `Env'.context = subst Env_aux.context Env_aux.subst`.
    subst h_ss h_env
    rw [Statement.subst_go_nil]
    simpa [TEnv.updateContext, TEnv.context] using h_core

end TypeSpec
end Core
