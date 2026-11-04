/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

import all Strata.DL.Imperative.CmdSemantics
public import Strata.DL.Imperative.CmdSemanticsProps
import all Strata.DL.Imperative.CmdSemanticsProps
import all Strata.DL.Imperative.StmtSemantics
public import Strata.DL.Imperative.StmtSemanticsProps
import all Strata.DL.Imperative.StmtSemanticsProps
import all Strata.DL.Imperative.HasVars
import all Strata.DL.Util.Nodup
public import Strata.Util.ListUtilsProps
import all Strata.Util.ListUtils
import all Strata.Util.ListUtilsProps
import all Strata.Languages.Core.Statement
public import Strata.Languages.Core.StatementSemantics
import all Strata.Languages.Core.StatementSemantics
import all Strata.DL.Imperative.Cmd
import all Strata.DL.Imperative.Stmt
import Std.Tactic.BVDecide.Normalize.BitVec

public section

/-! ## Theorems related to StatementSemantics

Metatheory of Core's event statement semantics (`EvalCommandE`,
`CoreStepStarE`).  Key results include `withOldSnapshots_preserves_wf` for
constructing well-formed call frames, beyond the remaining
`updatedStates`/`InitVars`/`HavocVars` plumbing:

- Core's call semantics is the generic one at `Expression`: `callEntry_iff`,
  `callExit_iff`, `havocVars_iff` and `evalCommandContractE_iff` (each `Iff.rfl`)
  identify Core's `CallEntry`, `CallExit`, `HavocVars` and `EvalCommandContractE`
  with `Calls.CallEntry`, `Calls.CallExit`, `Calls.HavocVars` and
  `EvalCmdExtContractE`; `HavocVars.update_none` / `update_some`,
  `EvalCommandE.cmd_sem` / `call_sem`, `CoreBodyExecE.structured` and
  `EvalCommandContractE.cmd_sem` / `call_sem` are the generic constructors under
  Core's names.
- `EvalExpressionsInjective`, `InitCallFrameUniqueResult`,
  `CallEntryUniqueResult`, and `CallExitUniqueResult`: deterministic expression
  lists and store-update relations uniquely determine call frames and caller
  result stores.
- `CoreBodyExecE.empty_unique`, the singleton command inversion/uniqueness
  theorems, and `EvalCommandE.call_unique_of_body_unique` compose body
  determinism into a unique caller store together with its chronological trace.
  `EvalCommandContractE.call_unique_of_outputs_nil` gives the corresponding
  full-result guarantee when contract abstraction has no outputs to havoc.
- `assertBodyE_preserves_store` and `setBodyE_frame`: one-command procedure
  bodies establish exact store preservation or an output write frame.
- Event-trace store-domain results:
  `evalCommandE_preserves_none_of_not_def`, `evalCommandE_preserves_isSome`,
  `evalCommandE_storeWellDefined`, `core_stmts_preserves_isSomeE`,
  `core_stmt_run_terminal_preserves_none_of_not_definedVars_trueE`, and
  `core_stmt_run_terminal_store_isSome_eqE` provide the corresponding
  guarantees for `EvalCommandE` / `StepStmtStarE` runs.
- Event-trace typed-slot results: `evalCommandE_preserves_typedAt` (a `call`
  writes back values of the types the caller variables held),
  `core_stmt_preserves_typedAtE` / `core_stmts_preserves_typedAtE` (a run keeps a
  slot at its type), and `core_stmt_run_storeHasTyping_extendE` (after a statement
  runs, the store conforms to the entry typing extended with the statement's typed
  definitions).
- `stmt_run_to_singleton_runE` / `singleton_run_to_stmt_runE`: a run of a
  statement and a run of the one-element list holding it emit the same traces.
-/

namespace Core
open Imperative

/-! ## Core's call semantics is the generic one at `Expression`

Core's call components and event relations are abbreviations of the generic ones at
`Expression`: the equivalences hold by `Iff.rfl`, and the generic constructors are
restated under Core's names. -/

/-- Core's call-entry relation is the generic `Calls.CallEntry` at `Expression`. -/
theorem callEntry_iff (fac : Expression.Factory) (σ : CoreStore) (p : Procedure)
    (callArgs : List (CallArg Expression)) (σAO : CoreStore) :
    CallEntry fac σ p callArgs σAO ↔ Calls.CallEntry fac σ p callArgs σAO := .rfl

/-- Core's call-exit relation is the generic `Calls.CallExit` at `Expression`. -/
theorem callExit_iff (fac : Expression.Factory) (σ : CoreStore) (p : Procedure)
    (callArgs : List (CallArg Expression)) (σEnd σ' : CoreStore) :
    CallExit fac σ p callArgs σEnd σ' ↔ Calls.CallExit fac σ p callArgs σEnd σ' := .rfl

/-- Core's havoc relation is the generic `Calls.HavocVars` at `Expression`. -/
theorem havocVars_iff (fac : Expression.Factory) (σ : CoreStore) (xs : List Expression.Ident)
    (σ' : CoreStore) : HavocVars fac σ xs σ' ↔ Calls.HavocVars fac σ xs σ' := .rfl

/-- Core's event contract relation is the generic `EvalCmdExtContractE` at `Expression`. -/
theorem evalCommandContractE_iff (π : String → Option Procedure) (fac : Expression.Factory)
    (σ : CoreStore) (c : Command) (σ' : CoreStore) (emitted : Trace Expression) :
    EvalCommandContractE π fac σ c σ' emitted ↔ EvalCmdExtContractE π fac σ c σ' emitted :=
  .rfl

/-- No slot to havoc: the store is unchanged. -/
theorem HavocVars.update_none {P : PureExpr} [HasVal P] {f : P.Factory}
    {σ : SemanticStore P} : HavocVars f σ [] σ := Calls.HavocVars.update_none

/-- Havoc the first slot `x` to a value `v` of its stored type, then the rest. -/
theorem HavocVars.update_some {P : PureExpr} [HasVal P] {f : P.Factory}
    {σ σ' σ'' : SemanticStore P} {x : P.Ident} {v : P.Val} {xs : List P.Ident}
    (hup : UpdateState P σ x v σ') (hty : HasVal.valueOfStoredTy (P := P) f σ x v)
    (hrest : HavocVars f σ' xs σ'') : HavocVars f σ (x :: xs) σ'' :=
  Calls.HavocVars.update_some hup hty hrest

/-- Base-command step of Core's event command relation. -/
theorem EvalCommandE.cmd_sem
    {π : String → Option Procedure}
    {fac : Expression.Factory} {σ σ' : CoreStore} {c : Imperative.Cmd Expression}
    {emitted : Trace Expression}
    (h : Imperative.EvalCmdE (P := Expression) fac σ c σ' emitted) :
    EvalCommandE π fac σ (.cmd c) σ' emitted := EvalCmdExtE.cmd_sem h

/-- Call step of Core's event command relation, stated with Core's `CallEntry` /
    `CallExit` / `defaultAssertEvents`. -/
theorem EvalCommandE.call_sem
    {π : String → Option Procedure}
    {σ : CoreStore} {n : String} {p : Procedure} {callArgs : List (CallArg Expression)}
    {σ' σ_final : CoreStore} {bodyEvents : Trace Expression}
    {md : MetaData Expression} {fac : Expression.Factory} {σAO : CoreStore}
    (hπ : π n = some p)
    (hentry : CallEntry fac σ p callArgs σAO)
    (hbody : CoreBodyExecE π p.body ⟨σAO, fac⟩ σ_final bodyEvents)
    (hexit : CallExit fac σ p callArgs σ_final σ') :
    EvalCommandE π fac σ (.call n callArgs md) σ'
      (defaultAssertEvents fac σAO (Imperative.Calls.checksAtCall md p.spec.preconditions) ++
        bodyEvents ++
        defaultAssertEvents fac σ_final p.spec.postconditions) :=
  EvalCmdExtE.call_sem hπ hentry hbody hexit

/-- Structured-body run of Core's event body relation. -/
theorem CoreBodyExecE.structured
    {π : String → Option Procedure}
    {ss : List Statement} {ρ ρ' : Env Expression}
    {emitted : Trace Expression}
    (h : CoreStepStarE π
      (.stmt (Stmt.block "" ss #[]) ρ) emitted (.terminal ρ')) :
    CoreBodyExecE π (.structured ss) ρ ρ'.store emitted := BigStepE.structured h

/-- Base-command step of Core's event contract relation. -/
theorem EvalCommandContractE.cmd_sem {π : String → Option Procedure}
    {fac : Expression.Factory} {σ σ' : CoreStore} {c : Imperative.Cmd Expression}
    {emitted : Trace Expression}
    (h : EvalCmdE (P := Expression) fac σ c σ' emitted) :
    EvalCommandContractE π fac σ (.cmd c) σ' emitted := EvalCmdExtContractE.cmd_sem h

/-- Call step of Core's event contract relation, stated with Core's `CallEntry` /
`HavocVars` / `CallExit` / `defaultAssertEvents` / `assumeEvents`. -/
theorem EvalCommandContractE.call_sem {π : String → Option Procedure}
    {σ σO : CoreStore} {n : String} {p : Procedure} {callArgs : List (CallArg Expression)}
    {σ' : CoreStore} {md : MetaData Expression} {fac : Expression.Factory} {σAO : CoreStore}
    (hπ : π n = .some p)
    (hentry : CallEntry fac σ p callArgs σAO)
    (hhavoc : HavocVars fac σAO (ListMap.keys p.header.outputs) σO)
    (hexit : CallExit fac σ p callArgs σO σ') :
    EvalCommandContractE π fac σ (.call n callArgs md) σ'
      (defaultAssertEvents fac σAO (Imperative.Calls.checksAtCall md p.spec.preconditions) ++
        assumeEvents fac σO p.spec.postconditions) :=
  EvalCmdExtContractE.call_sem hπ hentry hhavoc hexit

/-- Adding `old` snapshots only copies existing bindings, so it preserves store
well-formedness. -/
theorem withOldSnapshots_preserves_wf {fac : Expression.Factory}
    (snap : List Expression.Ident) (σ : CoreStore)
    (hσ : WellFormedStore σ fac) :
    WellFormedStore (withOldSnapshots snap σ) fac := by
  intro w vw hw
  simp only [withOldSnapshots, Calls.withOldSnapshots] at hw
  split at hw
  · exact hσ _ _ hw
  · exact hσ _ _ hw

theorem HavocVarsEmpty {P : PureExpr} [HasVal P] {f : P.Factory} {σ σ' : SemanticStore P} :
  HavocVars f σ [] σ' → σ = σ' := by
  intros H; cases H <;> simp

theorem InitVarsEmpty :
  @InitVars P σ [] σ' → σ = σ' := by
  intros H; cases H <;> simp

theorem TouchVarsEmpty :
  @TouchVars P σ [] σ' → σ = σ' := by
  intros H; cases H <;> simp

theorem InitStateDefined
  {P : PureExpr} {σ σ' : SemanticStore P} {e : P.Val} {v : P.Ident} :
  @InitState P σ v e σ' →
  SemanticStore.varsDefined (· ∈ [v]) σ' := by
  intros Hup
  cases Hup with
  | init Hold Hsome Hall =>
  simp [SemanticStore.varsDefined, Option.isSome, Hsome]

theorem updatedStateUpdate {P : PureExpr}
  {σ : SemanticStore P} {h : P.Ident} {v v' : P.Val} :
  σ h = some v' →
  UpdateState P σ h v (@updatedState P σ h v) := by
  intros Hsome
  constructor
  · assumption
  · simp [updatedState]
  · intro y Hneq; simp [updatedState, Ne.symm Hneq]

theorem updatedStateId {P : PureExpr}
  {σ : SemanticStore P} {h : P.Ident} {v : P.Val} :
  σ h = some v →
  @updatedState P σ h v = σ := by
  intros Hsome
  funext x
  simp_all [updatedState]

theorem updatedStateDefMonotone {vs : List _} :
  SemanticStore.varsDefined (· ∈ vs) σ →
  SemanticStore.varsDefined (· ∈ vs) (updatedState σ v' e') := by
  intros Hdef
  induction vs
  case nil => simp [SemanticStore.varsDefined]
  case cons h t ih =>
    simp only [SemanticStore.varsDefined, List.mem_cons, forall_eq_or_imp] at *
    apply And.intro
    . simp [Option.isSome]
      split <;> simp_all
      next x heq =>
      simp [updatedState] at heq
      split at heq <;> simp_all
    . intros id Hin
      apply ih <;> simp_all

theorem updatedStatesDefMonotone
  {P : PureExpr} {σ : SemanticStore P}
  {vs : List P.Ident} {ves : List (P.Ident × P.Val)} :
  SemanticStore.varsDefined (· ∈ vs) σ →
  SemanticStore.varsDefined (· ∈ vs) (updatedStates' σ ves) := by
  intros Hdef
  induction ves generalizing σ <;>
  unfold updatedStates' <;> try simp_all
  case cons h t ih =>
    simp only [SemanticStore.varsDefined]
    intros v Hin
    apply ih
    exact updatedStateDefMonotone Hdef
    assumption

  theorem updatedStatesDefined :
  ks.length = vs.length →
  SemanticStore.varsDefined (· ∈ ks) (updatedStates σ ks vs) := by
    intros Hlen k Hin
    induction ks generalizing σ vs <;> simp_all
    case cons h t ih =>
    simp only [updatedStates] at *
    cases vs <;> simp at Hlen
    case cons h' t' =>
    cases Hin with
    | inl Hin =>
      simp [updatedStates']
      have Hdef : SemanticStore.varsDefined (· ∈ [h]) (updatedStates' (updatedState σ h h') (t.zip t')) := by
        apply updatedStatesDefMonotone
        simp [SemanticStore.varsDefined, updatedState]
      simp_all [SemanticStore.varsDefined]
    | inr Hin =>
      apply ih <;> assumption

theorem updatedStatesUpdate {P : PureExpr}
  {σ : SemanticStore P} {hs : List P.Ident} {vs : List P.Val} :
  hs.length = vs.length →
  SemanticStore.varsDefined (· ∈ hs) σ →
  UpdateStates σ hs vs (updatedStates σ hs vs) := by
  intros Hlen Hdef
  induction hs generalizing vs σ
  case nil =>
    simp_all only [List.length_nil]
    have Hemp : vs = [] := by
      exact List.length_eq_zero_iff.mp (id (Eq.symm Hlen))
    simp only [Hemp, updatedStates, List.zip_nil_right]
    exact UpdateStates.update_none
  case cons h t ih =>
    induction vs <;> simp_all
    case cons h' t' =>
    simp only [SemanticStore.varsDefined, forall_eq_or_imp] at Hdef
    have Hlkup := Hdef.1
    simp [Option.isSome] at Hlkup
    split at Hlkup <;> simp_all
    next x val heq =>
    apply UpdateStates.update_some (updatedStateUpdate heq)
    exact ih rfl (updatedStateDefMonotone Hdef)

theorem updatedStateInit {P : PureExpr}
  {σ : SemanticStore P} {h : P.Ident} {v : P.Val} :
  σ h = none →
  InitState P σ h v (@updatedState P σ h v) := by
  intros Hsome
  constructor
  · assumption
  · simp [updatedState]
  · intro y Hneq; simp [updatedState, Ne.symm Hneq]

theorem updatedStatesInit {P : PureExpr}
  {σ : SemanticStore P} {hs : List P.Ident} {vs : List P.Val} :
  hs.length = vs.length →
  SemanticStore.varsUndefined (· ∈ hs) σ →
  hs.Nodup →
  InitStates σ hs vs (updatedStates σ hs vs) := by
  intros Hlen Hdef Hnd
  induction hs generalizing vs σ
  case nil =>
    simp_all only [List.length_nil, List.nodup_nil]
    have Hemp : vs = [] := by
      exact List.length_eq_zero_iff.mp (id (Eq.symm Hlen))
    simp only [Hemp, updatedStates, List.zip_nil_right]
    exact InitStates.init_none
  case cons h t ih =>
    induction vs <;> simp_all
    case cons h' t' =>
    simp only [SemanticStore.varsUndefined, forall_eq_or_imp] at Hdef
    have Hlkup := Hdef.1
    apply InitStates.init_some (updatedStateInit Hlkup)
    apply ih rfl
    simp only [SemanticStore.varsUndefined, updatedState, decide_eq_true_eq]
    intros v Hin
    simp_all only [true_and, ite_eq_right_iff, reduceCtorEq, imp_false]
    exact ne_of_mem_of_not_mem Hin Hnd.1

/-- use the zipped version to avoid needing to prove length equivalent -/
theorem updatedStates'App :
  updatedStates' σ (a ++ b) =
  updatedStates' (updatedStates' σ a) b := by
  induction a generalizing σ
  case nil =>
    simp [updatedStates']
  case cons h t ih =>
    simp only [List.cons_append, updatedStates']
    rw [ih]

theorem InitStatesInitVars :
  InitStates σ hs vs σ' →
  InitVars σ hs σ' := by
  intros Hinit
  induction Hinit
  case init_none => exact InitVars.init_none
  case init_some h t ih => exact InitVars.init_some h ih

theorem InitStatesInits :
  InitStates σ hs vs σ' →
  Inits σ σ' := by
  intros Hinit
  constructor
  exact InitStatesInitVars Hinit

/-- Evaluating the same expression list in the same factory and store yields the
same value list. -/
theorem EvalExpressionsInjective {f : Expression.Factory} {σ : CoreStore}
    {es : List Expression.Expr} {vs vs' : List Expression.Val} :
    EvalExpressions f σ es vs → EvalExpressions f σ es vs' → vs = vs' := by
  intro h₁ h₂
  induction h₁ generalizing vs' with
  | eval_none => cases h₂; rfl
  | eval_some _ heval₁ _ ih =>
    cases h₂ with
    | eval_some _ heval₂ hrest₂ =>
      have hv := Option.some.inj (heval₁.symm.trans heval₂)
      subst hv
      exact congrArg (fun tail => _ :: tail) (ih hrest₂)

theorem InitStateUpdated :
    InitState P σ' k v σ'' →
    σ'' = updatedState σ' k v := by
  intros Hinit
  cases Hinit with
  | init Hnone Hsome Heq =>
  funext x
  simp only [updatedState, decide_eq_true_eq]
  by_cases Hxk : x = k <;> simp_all only [ne_eq, ↓reduceIte]
  rw [Heq]
  exact fun a => Hxk (Eq.symm a)

theorem InitStatesUpdated :
    InitStates σ' ks vs σ'' →
    σ'' = updatedStates σ' ks vs := by
  intros Hinit
  induction Hinit
  case init_none =>
    simp [updatedStates, updatedStates']
  case init_some Hinit Hinits ih =>
    simp [ih]
    simp [updatedStates, updatedStates']
    have Heq := InitStateUpdated Hinit
    simp [Heq]

theorem UpdateStateUpdated :
    UpdateState P σ' k v σ'' →
    σ'' = updatedState σ' k v := by
  intros Hinit
  cases Hinit with
  | update Hnone Hsome Heq =>
  funext x
  simp only [updatedState, decide_eq_true_eq]
  by_cases Hxk : x = k <;> simp_all only [ne_eq, ↓reduceIte]
  rw [Heq]
  exact fun a => Hxk (Eq.symm a)

theorem UpdateStatesUpdated :
    UpdateStates σ' ks vs σ'' →
    σ'' = updatedStates σ' ks vs := by
  intros Hinit
  induction Hinit
  case update_none =>
    simp [updatedStates, updatedStates']
  case update_some Hinit Hinits ih =>
    simp [ih]
    simp [updatedStates, updatedStates']
    have Heq := UpdateStateUpdated Hinit
    simp [Heq]

/-- Building a call frame from the same procedure and argument values yields the
same callee store. -/
theorem InitCallFrameUniqueResult {p : Procedure} {inputVals outOnlyVals : List Expression.Val}
    {σ₁ σ₂ : CoreStore} :
    InitCallFrame p inputVals outOnlyVals σ₁ →
    InitCallFrame p inputVals outOnlyVals σ₂ →
    σ₁ = σ₂ := by
  rintro ⟨σA₁, σIO₁, hIn₁, hOut₁, hSnap₁⟩
    ⟨σA₂, σIO₂, hIn₂, hOut₂, hSnap₂⟩
  have hA : σA₁ = σA₂ := (InitStatesUpdated hIn₁).trans (InitStatesUpdated hIn₂).symm
  subst σA₂
  have hIO : σIO₁ = σIO₂ := (InitStatesUpdated hOut₁).trans (InitStatesUpdated hOut₂).symm
  subst σIO₂
  exact hSnap₁.trans hSnap₂.symm

/-- The call-entry frame is uniquely determined by the procedure, caller store,
and call arguments. -/
theorem CallEntryUniqueResult {fac : Expression.Factory} {σ : CoreStore}
    {p : Procedure} {callArgs : List (CallArg Expression)} {σ₁ σ₂ : CoreStore} :
    CallEntry fac σ p callArgs σ₁ → CallEntry fac σ p callArgs σ₂ → σ₁ = σ₂ := by
  rintro ⟨inputs₁, outs₁, hEval₁, hRead₁, hInit₁⟩
    ⟨inputs₂, outs₂, hEval₂, hRead₂, hInit₂⟩
  have hInputs : inputs₁ = inputs₂ := EvalExpressionsInjective hEval₁ hEval₂
  have hOuts : outs₁ = outs₂ := ReadValuesInjective hRead₁ hRead₂
  subst inputs₂
  subst outs₂
  exact InitCallFrameUniqueResult hInit₁ hInit₂

/-- Given the same callee-exit store, call write-back uniquely determines the
caller result store. -/
theorem CallExitUniqueResult {fac : Expression.Factory} {σ : CoreStore}
    {p : Procedure} {callArgs : List (CallArg Expression)} {σEnd σ₁ σ₂ : CoreStore} :
    CallExit fac σ p callArgs σEnd σ₁ → CallExit fac σ p callArgs σEnd σ₂ → σ₁ = σ₂ := by
  rintro ⟨_, outputs₁, hRead₁, hUpdate₁, -⟩ ⟨_, outputs₂, hRead₂, hUpdate₂, -⟩
  have hOutputs : outputs₁ = outputs₂ := ReadValuesInjective hRead₁ hRead₂
  subst outputs₂
  exact (UpdateStatesUpdated hUpdate₁).trans (UpdateStatesUpdated hUpdate₂).symm

/-- A call with no left-hand-side arguments cannot change the caller store. -/
theorem CallExit.store_eq_of_getLhs_nil {fac : Expression.Factory} {σ : CoreStore}
    {p : Procedure} {callArgs : List (CallArg Expression)} {σEnd σ' : CoreStore}
    (hLhs : CallArg.getLhs callArgs = [])
    (h : CallExit fac σ p callArgs σEnd σ') : σ' = σ := by
  obtain ⟨_, outputs, _, hUpdate, -⟩ := h
  rw [hLhs] at hUpdate
  cases hUpdate
  rfl

/-- Executing an event-producing concrete call with no left-hand-side arguments
leaves the caller store unchanged. -/
theorem EvalCommandE.store_eq_of_call_getLhs_nil
    {π : String → Option Procedure}

    {fac : Expression.Factory} {σ σ' : CoreStore} {n : String}
    {callArgs : List (CallArg Expression)} {md : MetaData Expression}
    {emitted : Trace Expression}
    (hLhs : CallArg.getLhs callArgs = [])
    (h : EvalCommandE π fac σ (.call n callArgs md) σ' emitted) : σ' = σ := by
  cases h with
  | call_sem _ _ _ hExit => exact CallExit.store_eq_of_getLhs_nil hLhs hExit

/-- Executing an event-producing abstract contract call with no left-hand-side
arguments leaves the caller store unchanged. -/
theorem EvalCommandContractE.store_eq_of_call_getLhs_nil
    {π : String → Option Procedure} {fac : Expression.Factory} {σ σ' : CoreStore}
    {n : String} {callArgs : List (CallArg Expression)} {md : MetaData Expression}
    {emitted : Trace Expression}
    (hLhs : CallArg.getLhs callArgs = [])
    (h : EvalCommandContractE π fac σ (.call n callArgs md) σ' emitted) : σ' = σ := by
  cases h with
  | call_sem _ _ _ hExit => exact CallExit.store_eq_of_getLhs_nil hLhs hExit

/-- Event-producing abstract contract calls for a procedure with no outputs have
a unique caller store and event trace. -/
theorem EvalCommandContractE.call_unique_of_outputs_nil
    {π : String → Option Procedure} {fac : Expression.Factory}
    {σ σ₁ σ₂ : CoreStore} {n : String} {p : Procedure}
    {callArgs : List (CallArg Expression)} {md : MetaData Expression}
    {emitted₁ emitted₂ : Trace Expression}
    (hLookup : π n = some p) (hOutputs : ListMap.keys p.header.outputs = [])
    (h₁ : EvalCommandContractE π fac σ (.call n callArgs md) σ₁ emitted₁)
    (h₂ : EvalCommandContractE π fac σ (.call n callArgs md) σ₂ emitted₂) :
    σ₁ = σ₂ ∧ emitted₁ = emitted₂ := by
  cases h₁ with
  | @call_sem _ out₁ _ p₁ _ _ _ _ frame₁ lookup₁ entry₁ havoc₁ exit₁ =>
    cases h₂ with
    | @call_sem _ out₂ _ p₂ _ _ _ _ frame₂ lookup₂ entry₂ havoc₂ exit₂ =>
      have hp₁ : p₁ = p := Option.some.inj (lookup₁.symm.trans hLookup)
      have hp₂ : p₂ = p := Option.some.inj (lookup₂.symm.trans hLookup)
      subst p₁
      subst p₂
      have hframe : frame₁ = frame₂ := CallEntryUniqueResult entry₁ entry₂
      subst frame₂
      rw [show ProcedureHeader.outputParams p.header = [] from hOutputs] at havoc₁ havoc₂
      cases havoc₁
      cases havoc₂
      exact ⟨CallExitUniqueResult exit₁ exit₂, rfl⟩

/-- A terminal configuration cannot take an event-producing statement step. -/
private theorem no_stepE_from_terminal
    (π : String → Option Procedure)

    (ρ : Env Expression) (emitted : Trace Expression) (c : Config Expression Command)
    (h : StepStmtE Expression (EvalCommandE π)
      (.terminal ρ) emitted c) : False := by
  cases h

/-- Invert an event step from a command statement into its command result. -/
private theorem stepE_stmt_cmd_inv
    {π : String → Option Procedure}

    {cmd : Command} {ρ : Env Expression} {e : Trace Expression}
    {c' : Config Expression Command}
    (h : CoreStepE π (.stmt (.cmd cmd) ρ) e c') :
    ∃ σ', EvalCommandE π ρ.factory ρ.store cmd σ' e ∧
      c' = .terminal { ρ with store := σ' } := by
  cases h with
  | step_cmd hcmd => exact ⟨_, hcmd, rfl⟩

/-- Invert an event step from a statement-list configuration. -/
private theorem stepE_stmts_inv
    {π : String → Option Procedure}

    {ss : List (Stmt Expression Command)} {ρ : Env Expression}
    {e : Trace Expression} {c' : Config Expression Command}
    (h : CoreStepE π (.stmts ss ρ) e c') :
    (ss = [] ∧ e = [] ∧ c' = .terminal ρ) ∨
      (∃ s ss', ss = s :: ss' ∧ e = [] ∧ c' = .seq (.stmt s ρ) ss') := by
  cases h with
  | step_stmts_nil => exact .inl ⟨rfl, rfl, rfl⟩
  | step_stmts_cons => exact .inr ⟨_, _, rfl, rfl, rfl⟩

/-- Invert an event step from a sequence, identifying an inner step or one of
its two administrative exits. -/
private theorem stepE_seq_inv
    {π : String → Option Procedure}

    {inner : Config Expression Command} {ss : List (Stmt Expression Command)}
    {e : Trace Expression} {c' : Config Expression Command}
    (h : CoreStepE π (.seq inner ss) e c') :
    (∃ inner', CoreStepE π inner e inner' ∧ c' = .seq inner' ss) ∨
      (∃ ρ₁ : Env Expression,
        inner = .terminal ρ₁ ∧ e = [] ∧ c' = .stmts ss ρ₁) ∨
      (∃ (l : String) (ρ₁ : Env Expression),
        inner = .exiting l ρ₁ ∧ e = [] ∧ c' = .exiting l ρ₁) := by
  cases h with
  | step_seq_done => exact .inr (.inl ⟨_, rfl, rfl, rfl⟩)
  | step_seq_exit => exact .inr (.inr ⟨_, _, rfl, rfl, rfl⟩)
  | step_seq_inner hE => exact .inl ⟨_, hE, rfl⟩

/-- Invert an event step from a block, identifying an inner step or one of its
three administrative exits. -/
private theorem stepE_block_inv
    {π : String → Option Procedure}

    {label : Option String} {σp : SemanticStore Expression}
    {inner : Config Expression Command}
    {e : Trace Expression} {c' : Config Expression Command}
    (h : CoreStepE π (.block label σp inner) e c') :
    (∃ inner', CoreStepE π inner e inner' ∧
      c' = .block label σp inner') ∨
    (∃ ρ₁ : Env Expression, inner = .terminal ρ₁ ∧ e = [] ∧
      c' = .terminal { ρ₁ with store := projectStore σp ρ₁.store }) ∨
    (∃ (l : String) (ρ₁ : Env Expression),
      inner = .exiting l ρ₁ ∧ label = some l ∧ e = [] ∧
      c' = .terminal { ρ₁ with store := projectStore σp ρ₁.store }) ∨
    (∃ (l : String) (ρ₁ : Env Expression),
      inner = .exiting l ρ₁ ∧ label ≠ some l ∧ e = [] ∧
      c' = .exiting l
        { ρ₁ with store := projectStore σp ρ₁.store }) := by
  cases h with
  | step_block_done => exact .inr (.inl ⟨_, rfl, rfl, rfl⟩)
  | step_block_exit_match hlabel =>
    exact .inr (.inr (.inl ⟨_, _, rfl, hlabel, rfl, rfl⟩))
  | step_block_exit_mismatch hne =>
    exact .inr (.inr (.inr ⟨_, _, rfl, hne, rfl, rfl⟩))
  | step_block_body hE => exact .inl ⟨_, hE, rfl⟩

/-- A singleton-command structured event body exposes exactly the command result
before the procedure block projects its store and restores its factory. -/
theorem CoreBodyExecE.singleton_cmd_invert
    {π : String → Option Procedure}

    {fac : Expression.Factory} {σ σ' : CoreStore}
    {cmd : Command} {emitted : Trace Expression}
    (h : CoreBodyExecE π (.structured [.cmd cmd]) ⟨σ, fac⟩ σ' emitted) :
    ∃ σCmd, EvalCommandE π fac σ cmd σCmd emitted ∧
      σ' = projectStore σ σCmd := by
  cases h with
  | structured hstar =>
    cases hstar with
    | step _ _ _ _ _ hs1 hr1 =>
      cases hs1 with
      | step_block =>
        cases hr1 with
        | step _ _ _ _ _ hs2 hr2 =>
          rcases stepE_block_inv hs2 with
            ⟨_, hin2, rfl⟩ | ⟨_, hc, _⟩ | ⟨_, _, hc, _⟩ | ⟨_, _, hc, _⟩
          · rcases stepE_stmts_inv hin2 with
              ⟨hc, _⟩ | ⟨_, _, hcons, rfl, rfl⟩
            · simp at hc
            · cases hcons
              cases hr2 with
              | step _ _ _ _ _ hs3 hr3 =>
                rcases stepE_block_inv hs3 with
                  ⟨_, hin3, rfl⟩ | ⟨_, hc, _⟩ | ⟨_, _, hc, _⟩ | ⟨_, _, hc, _⟩
                · rcases stepE_seq_inv hin3 with
                    ⟨_, hseq3, rfl⟩ | ⟨_, hc, _⟩ | ⟨_, _, hc, _⟩
                  · obtain ⟨σCmd, hcmd, rfl⟩ := stepE_stmt_cmd_inv hseq3
                    cases hr3 with
                    | step _ _ _ _ _ hs4 hr4 =>
                      rcases stepE_block_inv hs4 with
                        ⟨_, hin4, rfl⟩ | ⟨_, hc, _⟩ | ⟨_, _, hc, _⟩ | ⟨_, _, hc, _⟩
                      · rcases stepE_seq_inv hin4 with
                          ⟨_, hseq4, rfl⟩ | ⟨_, he4, rfl, rfl⟩ | ⟨_, _, hc, _⟩
                        · exact (no_stepE_from_terminal π _ _ _ hseq4).elim
                        · injection he4 with he4
                          subst he4
                          cases hr4 with
                          | step _ _ _ _ _ hs5 hr5 =>
                            rcases stepE_block_inv hs5 with
                              ⟨_, hin5, rfl⟩ | ⟨_, hc, _⟩ | ⟨_, _, hc, _⟩ | ⟨_, _, hc, _⟩
                            · rcases stepE_stmts_inv hin5 with
                                ⟨_, rfl, rfl⟩ | ⟨_, _, hc, _⟩
                              · cases hr5 with
                                | step _ _ _ _ _ hs6 hr6 =>
                                  rcases stepE_block_inv hs6 with
                                    ⟨_, hin6, _⟩ | ⟨_, he6, rfl, rfl⟩ |
                                    ⟨_, _, hc, _⟩ | ⟨_, _, hc, _⟩
                                  · exact (no_stepE_from_terminal π _ _ _ hin6).elim
                                  · injection he6 with he6
                                    subst he6
                                    cases hr6 with
                                    | refl => exact ⟨σCmd, by simpa using hcmd, rfl⟩
                                    | step _ _ _ _ _ hs7 _ =>
                                      exact (no_stepE_from_terminal π _ _ _ hs7).elim
                                  · simp at hc
                                  · simp at hc
                              · simp at hc
                            · simp at hc
                            · simp at hc
                            · simp at hc
                        · simp at hc
                      · simp at hc
                      · simp at hc
                      · simp at hc
                  · simp at hc
                  · simp at hc
                · simp at hc
                · simp at hc
                · simp at hc
          · simp at hc
          · simp at hc
          · simp at hc

/-- An event-producing call has a unique store and trace when every execution of
its selected body has a unique store, factory, and trace. -/
theorem EvalCommandE.call_unique_of_body_unique
    {π : String → Option Procedure}

    {fac : Expression.Factory} {σ σ₁ σ₂ : CoreStore}
    {n : String} {p : Procedure} {callArgs : List (CallArg Expression)}
    {md : MetaData Expression} {emitted₁ emitted₂ : Trace Expression}
    (hLookup : π n = some p)
    (hBodyUnique : ∀ {frame end₁ end₂ : CoreStore}
      {bodyEvents₁ bodyEvents₂ : Trace Expression},
      CoreBodyExecE π p.body ⟨frame, fac⟩ end₁ bodyEvents₁ →
      CoreBodyExecE π p.body ⟨frame, fac⟩ end₂ bodyEvents₂ →
      end₁ = end₂ ∧ bodyEvents₁ = bodyEvents₂)
    (h₁ : EvalCommandE π fac σ (.call n callArgs md) σ₁ emitted₁)
    (h₂ : EvalCommandE π fac σ (.call n callArgs md) σ₂ emitted₂) :
    σ₁ = σ₂ ∧ emitted₁ = emitted₂ := by
  cases h₁ with
  | @call_sem _ _ p₁ _ _ end₁ bodyEvents₁ _ _ frame₁
      lookup₁ entry₁ bodyExec₁ exit₁ =>
    cases h₂ with
    | @call_sem _ _ p₂ _ _ end₂ bodyEvents₂ _ _ frame₂
        lookup₂ entry₂ bodyExec₂ exit₂ =>
      have hp₁ : p₁ = p := Option.some.inj (lookup₁.symm.trans hLookup)
      have hp₂ : p₂ = p := Option.some.inj (lookup₂.symm.trans hLookup)
      subst p₁
      subst p₂
      have hframe : frame₁ = frame₂ := CallEntryUniqueResult entry₁ entry₂
      subst frame₂
      obtain ⟨hend, hbody⟩ := hBodyUnique bodyExec₁ bodyExec₂
      subst end₂
      subst bodyEvents₂
      exact ⟨CallExitUniqueResult exit₁ exit₂, rfl⟩

/-- A singleton-command event body has a unique store, factory, and trace when
that command has a unique store and trace. -/
theorem CoreBodyExecE.singleton_cmd_unique
    {π : String → Option Procedure}

    {fac : Expression.Factory} {σ end₁ end₂ : CoreStore}
    {cmd : Command}
    {emitted₁ emitted₂ : Trace Expression}
    (hCmdUnique : ∀ {σ₁ σ₂ : CoreStore} {result₁ result₂ : Trace Expression},
      EvalCommandE π fac σ cmd σ₁ result₁ →
      EvalCommandE π fac σ cmd σ₂ result₂ →
      σ₁ = σ₂ ∧ result₁ = result₂)
    (h₁ : CoreBodyExecE π (.structured [.cmd cmd]) ⟨σ, fac⟩ end₁ emitted₁)
    (h₂ : CoreBodyExecE π (.structured [.cmd cmd]) ⟨σ, fac⟩ end₂ emitted₂) :
    end₁ = end₂ ∧ emitted₁ = emitted₂ := by
  obtain ⟨σCmd₁, hcmd₁, hend₁⟩ := h₁.singleton_cmd_invert
  obtain ⟨σCmd₂, hcmd₂, hend₂⟩ := h₂.singleton_cmd_invert
  obtain ⟨hcmdStore, hresult⟩ := hCmdUnique hcmd₁ hcmd₂
  subst σCmd₂
  exact ⟨hend₁.trans hend₂.symm, hresult⟩

/-- A fixed event-producing assertion command has a unique output store and
single-event trace. -/
theorem EvalCommandE.assert_unique
    {π : String → Option Procedure}

    {fac : Expression.Factory} {σ σ₁ σ₂ : CoreStore}
    {label : String} {e : Expression.Expr} {md : MetaData Expression}
    {emitted₁ emitted₂ : Trace Expression}
    (h₁ : EvalCommandE π fac σ (.cmd (.assert label e md)) σ₁ emitted₁)
    (h₂ : EvalCommandE π fac σ (.cmd (.assert label e md)) σ₂ emitted₂) :
    σ₁ = σ₂ ∧ emitted₁ = emitted₂ := by
  cases h₁ with
  | cmd_sem cmd₁ =>
    cases cmd₁
    cases h₂ with
    | cmd_sem cmd₂ =>
      cases cmd₂
      exact ⟨rfl, rfl⟩

/-- An empty structured event body uniquely preserves its input store and factory
and emits no events. -/
theorem CoreBodyExecE.empty_unique
    (π : String → Option Procedure)

    (σ σ' : CoreStore) (fac : Expression.Factory) (emitted : Trace Expression)
    (h : CoreBodyExecE π (.structured []) ⟨σ, fac⟩ σ' emitted) :
    σ' = σ ∧ emitted = [] := by
  cases h with
  | structured hstar =>
    obtain ⟨ρ_inner, hinner, hρ⟩ :=
      stmt_block_reaches_doneE (P := Expression) (EvalCmd := EvalCommandE π) (.inl hstar)
    have hbody : StepStmtStarE Expression (EvalCommandE π)
        (.stmts [] ⟨σ, fac⟩) emitted (.terminal ρ_inner) := by
      rcases hinner with hterm | ⟨_, hexit⟩
      · exact hterm
      · obtain ⟨_, hcfg⟩ := stmts_nil_runE (EvalCmd := EvalCommandE π) hexit
        rcases hcfg with h | h <;> exact absurd h (by simp)
    obtain ⟨htr, hcfg⟩ := stmts_nil_runE (EvalCmd := EvalCommandE π) hbody
    rcases hcfg with h | h
    · exact absurd h (by simp)
    · injection h with h
      subst h
      refine ⟨?_, htr⟩
      rw [congrArg Env.store hρ]
      exact projectStore_self σ

/-- An event-producing concrete call to an empty body has the unique caller
result obtained from its uniquely determined entry frame and expected call exit. -/
theorem EvalCommandE.empty_body_call_store_unique
    {π : String → Option Procedure}

    {fac : Expression.Factory} {σ σAO expected σ' : CoreStore}
    {n : String} {p : Procedure} {callArgs : List (CallArg Expression)}
    {md : MetaData Expression} {emitted : Trace Expression}
    (hLookup : π n = some p) (hBody : p.body = .structured [])
    (hEntry : CallEntry fac σ p callArgs σAO)
    (hExit : CallExit fac σ p callArgs σAO expected)
    (h : EvalCommandE π fac σ (.call n callArgs md) σ' emitted) : σ' = expected := by
  cases h with
  | @call_sem _ _ q _ _ σFinal bodyEvents _ _ frame
      hLookup' hEntry' hBodyExec hExit' =>
    have hp : q = p := Option.some.inj (hLookup'.symm.trans hLookup)
    subst q
    have hFrame : frame = σAO := CallEntryUniqueResult hEntry' hEntry
    subst frame
    rw [hBody] at hBodyExec
    obtain ⟨rfl, _⟩ := CoreBodyExecE.empty_unique π σAO σFinal fac bodyEvents hBodyExec
    exact CallExitUniqueResult hExit' hExit

theorem InitStatesApp' :
  InitStates σ (k1 ++ k2) (v1 ++ v2) σ' →
  k1.length = v1.length →
  k2.length = v2.length →
  ∃ σ₁,
  σ₁ = updatedStates σ k1 v1 ∧
  InitStates σ k1 v1 σ₁ ∧
  InitStates σ₁ k2 v2 σ' := by
  intros Hinit Hlen1 Hlen2
  exists (updatedStates σ k1 v1)
  refine ⟨rfl, ?_⟩
  have H1 : InitStates σ k1 v1 (updatedStates σ k1 v1) := by
    apply updatedStatesInit Hlen1
    . have Hndef := InitStatesNotDefined Hinit
      simp [SemanticStore.varsUndefined] at *
      simp_all
    . have Hndup := InitStatesNodup Hinit
      refine List.Sublist.nodup ?_ Hndup
      exact List.sublist_append_left k1 k2
  refine ⟨H1, ?_⟩
  generalize Hup : updatedStates σ k1 v1 = σ₁ at *
  induction H1 <;> simp_all
  case init_some σ₂ Hinit' Hinits ih =>
  apply ih
  . cases Hinit with
    | init_some Hinit Hinits =>
      simp only [InitStateInjective Hinit Hinit'] at *
      assumption
  . simp only [InitStateUpdated Hinit']
    exact Hup

/-- Evaluating a list of expressions yields exactly one value per expression. -/
theorem EvalExpressionsLength :
  EvalExpressions (P := Expression) fac σ ks vs →
  ks.length = vs.length := by
  intros Hrd
  induction Hrd <;> simp_all

theorem InitVarsInitStates : InitVars σ vars σ' →
  ∃ modvals, InitStates σ vars modvals σ' := by
  intros Hinit
  induction Hinit
  case init_none =>
    refine ⟨[], InitStates.init_none⟩
  case init_some σ x v σ₁ xs σ'' Hup Hhav ih =>
    cases ih with
    | intro vs Hups =>
    refine ⟨v::vs,?_⟩
    constructor <;> assumption

/-- Values read from a store remain readable after `InitVars` extends it. -/
theorem InitVarsReadValuesMonotone
  {P : PureExpr} [HasVal P] {f : P.Factory} {σ σ' : SemanticStore P}
  {ks vs' : List P.Ident} {vs : List P.Val} :
  ReadValues f σ ks vs →
  InitVars σ vs' σ' →
  ReadValues f σ' ks vs := by
  intros Hdef Hinit
  have Hinit' := InitVarsInitStates Hinit
  cases Hinit' with
  | intro es' Hinit' =>
  exact InitStatesReadValuesMonotone Hdef Hinit'

theorem updatedStateComm
  {P : PureExpr} {σ : SemanticStore P}
  {k k' : P.Ident} {v v' : P.Val} :
  k ≠ k' →
  updatedState (updatedState σ k v) k' v' =
  updatedState (updatedState σ k' v') k v := by
  intros Hne
  funext x
  unfold updatedState
  by_cases Hxk' : x = k' <;> simp only [Hxk', decide_true, ↓reduceIte, decide_eq_true_eq, right_eq_ite_iff, Option.some.injEq]
  intros Heq
  by_cases Hxk : x = k <;> simp_all

theorem updatedStateComm'
  {P : PureExpr} {σ : SemanticStore P}
  {k : P.Ident} {v : P.Val}
  {kvs : List (P.Ident × P.Val)} :
  ¬ k ∈ kvs.unzip.1 →
  (updatedState (updatedStates' σ kvs) k v) =
  (updatedStates' (updatedState σ k v) kvs) := by
  intros Hnd
  induction kvs generalizing σ <;> simp [updatedStates']
  case cons h t ih =>
  rw [ih]
  rw [updatedStateComm]
  simp_all only [List.unzip_fst, List.mem_map, Prod.exists, exists_and_right, exists_eq_right, not_exists, List.unzip_cons, List.unzip_snd, List.mem_cons, not_or, ne_eq, not_false_eq_true, implies_true, forall_const]; exact fun a => Hnd.1 (Eq.symm a)
  simp_all

theorem updatedStatesComm
  {P : PureExpr} {σ : SemanticStore P}
  {kvs : List (P.Ident × P.Val)} {kvs' : List (P.Ident × P.Val)} :
  kvs.unzip.1.Disj kvs'.unzip.1 →
  updatedStates' (updatedStates' σ kvs) kvs' =
  updatedStates' (updatedStates' σ kvs') kvs := by
  intros Hnd
  induction kvs generalizing kvs' σ <;> simp [updatedStates']
  case cons h t ih =>
  induction kvs' generalizing σ h <;> simp [updatedStates']
  case cons h' t' ih' =>
    rw [← ih']
    rw [updatedStateComm]
    rw [updatedStateComm']
    . simp only [List.unzip_cons, List.unzip_fst, List.unzip_snd] at Hnd
      have Hnd' := List.Disj.symm Hnd
      apply List.Disjoint_cons_head
      apply List.Disj.mono_right _ Hnd'
      simp_all
    . intros Hin
      simp_all [List.Disj]
    . simp only [List.unzip_fst, List.unzip_cons, List.unzip_snd, Prod.forall] at *
      refine List.Disj.mono_right ?_ Hnd
      simp_all

theorem InitsUpdatesComm
  {P : PureExpr} {σ σ' σ'' : SemanticStore P}
  {ks ks' : List P.Ident} {vs vs' : List P.Val} :
  UpdateStates σ ks vs σ' →
  InitStates σ' ks' vs' σ'' →
  ∃ σ₁,
    σ₁ = (updatedStates σ ks' vs') ∧
    InitStates σ ks' vs' σ₁ ∧
    UpdateStates σ₁ ks vs σ'' := by
  intros Hup Hinit
  exists (updatedStates σ ks' vs')
  have Hk : (SemanticStore.varsDefined (· ∈ ks) σ') := UpdateStatesDefined Hup
  have Hlen1 := InitStatesLength Hinit
  have Hlen2 := UpdateStatesLength Hup
  induction Hup generalizing σ''
  case update_none =>
    simp_all only [List.length_nil, true_and]
    apply And.intro
    refine updatedStatesInit Hlen1 ?_ ?_
    exact InitStatesNotDefined Hinit
    exact InitStatesNodup Hinit
    simp [InitStatesUpdated Hinit]
    constructor
  case update_some σ x v σ₀ xs vs σ₁ Hup Hups ih =>
    refine ⟨rfl, ?_, ?_⟩
    . apply updatedStatesInit Hlen1
      apply UpdateStateNotDefMonotone' ?_ Hup
      apply UpdateStatesNotDefMonotone' ?_ Hups
      exact InitStatesNotDefined Hinit
      exact InitStatesNodup Hinit
    . apply UpdateStates.update_some (σ':=updatedStates σ₀ ks' vs')
      . simp only [updatedStates, UpdateStateUpdated Hup]
        rw [← updatedStateComm']
        . have Hdef := UpdateStateDefined' Hup
          simp [SemanticStore.varsDefined, Option.isSome] at Hdef
          split at Hdef <;> simp_all
          next val heq =>
          apply updatedStateUpdate (v':=val)
          apply InitStatesSomeMonotone heq
          apply updatedStatesInit
          . simp_all
          . apply UpdateStateNotDefMonotone' ?_ Hup
            apply UpdateStatesNotDefMonotone' ?_ Hups
            apply InitStatesNotDefined Hinit
          . exact InitStatesNodup Hinit
        . rw [List.unzip_zip] <;> simp_all only [true_and, List.length_cons, Nat.add_right_cancel_iff, forall_const, and_true]
          have Hnd := InitStatesNotDefined Hinit
          simp only [SemanticStore.varsDefined, List.mem_cons, forall_eq_or_imp, SemanticStore.varsUndefined] at *
          apply Not.intro
          intros Hin
          specialize Hnd _ Hin
          simp_all
      . apply (ih Hinit ?_ ?_).2.2
        . simp [SemanticStore.varsDefined] at * <;> simp_all
        . simp_all

theorem InitUpdateComm
  {P : PureExpr} {σ σ' σ'' : SemanticStore P}
  {k k' : P.Ident} {v v' : P.Val}
  :
  UpdateState P σ k v σ' →
  InitState P σ' k' v' σ'' →
  ∃ σ₁,
    σ₁ = (updatedState σ k' v') ∧
    InitState P σ k' v' σ₁ ∧
    UpdateState P σ₁ k v σ'' := by
  intros Hup Hinit
  exists (updatedState σ k' v')
  have Hk : (SemanticStore.varsDefined (· ∈ [k]) σ') := UpdateStateDefined Hup
  have Hups : UpdateStates σ [k] [v] σ' := by
    apply UpdateStates.update_some Hup UpdateStates.update_none
  have Hinits : InitStates σ' [k'] [v'] σ'' := by
    apply InitStates.init_some Hinit InitStates.init_none
  have Hcomms := InitsUpdatesComm Hups Hinits
  simp only [exists_eq_left] at Hcomms
  refine ⟨rfl, ?_, ?_⟩
  . have Hinit := Hcomms.1
    cases Hinit with
    | init_some Hinit Hinits =>
    simp [InitStatesEmpty Hinits, updatedStates, updatedStates'] at Hinit
    assumption
  . have Hup := Hcomms.2
    cases Hup with
    | update_some Hup Hups =>
    simp [UpdateStatesEmpty Hups, updatedStates, updatedStates'] at Hup
    assumption

theorem substStoresInitInv :
substDefined σ σ' substs →
substStores σ σ' substs →
InitState Expression σ' k v σ'' →
substStores σ σ'' substs := by
  intros Hdef Hsubst Hinit
  simp only [substDefined, substStores] at *
  intros k1 k2 Hin
  cases Hinit with
  | init Hnone Hsome' Heq =>
  rw [Heq] <;> simp_all only [ne_eq]
  rw [Hsubst] <;> simp_all
  apply Not.intro
  intro Heq'
  simp only [Heq'] at *
  specialize Hdef k1 k2 Hin
  simp [Option.isSome] at Hdef
  split at Hdef <;> simp_all

theorem substDefinedIsDefined :
  substDefined σ σ' substs →
  SemanticStore.varsDefined (· ∈ substs.unzip.1) σ ∧
  SemanticStore.varsDefined (· ∈ substs.unzip.2) σ' := by
  intros Hsubst
  cases substs <;> simp [SemanticStore.varsDefined, substDefined] at *
  case cons h t =>
    apply And.intro
    . apply And.intro
      . exact (Hsubst h.1 h.2 (Or.inl rfl)).1
      . intros k1 k2 Hin
        exact (Hsubst k1 k2 (Or.inr Hin)).1
    . apply And.intro
      . exact (Hsubst h.1 h.2 ((Or.inl rfl))).2
      . intros k2 k1 Hin
        exact (Hsubst k1 k2 (Or.inr Hin)).2

/--
We require substNodup on keys here, because
if we want σ [(x, y), (y, z)] σ' by constructing σ' from σ
there are two ways:
1. σ₁ := σ [y → x], σ' := σ₁ [z → y]. This way, z = σ(x) in σ'
2. σ₁ := σ [z → y], σ' := σ₁ [y → x]. This way, z = σ(y) in σ'
This creates ambiguity when we deterministically compute the substitution.
It is more common to assume commutativity of substitution, meaning it stays non-order sensitive.
This is why Nodup is included as a part of substStores
-/
theorem substStoresCons' :
  substNodup ((h,h') :: substs) →
  substDefined σ σ'' ((h,h') :: substs) →
  substStores σ σ'' ((h,h') :: substs) →
  ∃ σ' v,
    σ h = some v ∧
    σ' = updatedState σ h' v ∧
    substStores σ σ' [(h,h')] ∧
    substStores σ' σ'' substs := by
  intros Hnd Hdef Hsubst
  simp only [substDefined, List.mem_cons, Prod.mk.injEq, substStores, List.not_mem_nil, or_false, and_imp, forall_eq_apply_imp_iff, forall_eq] at *
  have Hsome : (σ h).isSome = true := by
    simp [Option.isSome]
    specialize Hdef h h'
    split <;> simp_all
  cases Hh: σ h with
  | none =>
    exfalso
    specialize Hdef h h'
    simp_all
  | some v =>
    exists (updatedState σ h' v)
    simp only [Option.some.injEq, updatedState, decide_true, ↓reduceIte, decide_eq_true_eq, true_and, exists_eq_left']
    simp [substNodup] at Hnd
    intros k1 k2 Hin
    split <;> simp_all
    next heq =>
      have Hnd' := Hnd.2
      have Hin' : h' ∈ substs.unzip.1 := by
        simp_all only [and_true, List.unzip_fst, List.mem_map, Prod.exists, exists_and_right, exists_eq_right]
        exists k2
      exfalso
      have Hnd' := nodup_middle Hnd'
      simp_all
    next hne =>
      apply Hsubst
      exact Or.inr Hin

theorem HavocVarsApp {P : PureExpr} [HasVal P] {f : P.Factory} {σ σ' σ'' : SemanticStore P} {vs₁ vs₂ : List P.Ident} :
  HavocVars f σ vs₁ σ' →
  HavocVars f σ' vs₂ σ'' →
  HavocVars f σ (vs₁ ++ vs₂) σ'' := by
  intros Hv1 Hv2
  induction vs₁ generalizing σ
  case nil =>
    simp only [List.nil_append]
    have Heq := HavocVarsEmpty Hv1
    simp only [Heq]
    assumption
  case cons h t ih =>
    simp
    cases Hv1
    next exp σ1 Hup Hval Hhavoc =>
    apply HavocVars.update_some <;> try assumption
    exact ih Hhavoc

theorem HavocVarsApp' {P : PureExpr} [HasVal P] {f : P.Factory} {σ σ'' : SemanticStore P} {vs₁ vs₂ : List P.Ident} :
  HavocVars f σ (vs₁ ++ vs₂) σ'' →
  ∃ σ',
  HavocVars f σ vs₁ σ' ∧
  HavocVars f σ' vs₂ σ'' := by
  intros Hv
  induction vs₁ generalizing σ
  case nil =>
    exists σ
    simp_all
    constructor
  case cons h t ih =>
    cases Hv
    next exp σ1 Hup Hval Hhavoc =>
    specialize ih Hhavoc
    cases ih with
    | intro σ₁ Hand =>
    cases Hand with
    | intro Havoc1 Havoc2 =>
    exists σ₁
    simp_all only [List.append_eq, and_true]
    constructor <;> assumption

theorem InitVarsApp :
  InitVars σ vs₁ σ' →
  InitVars σ' vs₂ σ'' →
  InitVars σ (vs₁ ++ vs₂) σ'' := by
  intros Hv1 Hv2
  induction vs₁ generalizing σ
  case nil =>
    simp only [List.nil_append]
    have Heq := InitVarsEmpty Hv1
    simp only [Heq]
    assumption
  case cons h t ih =>
    simp
    cases Hv1
    next exp σ1 Hup Hhavoc =>
    apply InitVars.init_some <;> try assumption
    exact ih Hhavoc

theorem TouchVarsApp :
  TouchVars σ vs₁ σ' →
  TouchVars σ' vs₂ σ'' →
  TouchVars σ (vs₁ ++ vs₂) σ'' := by
  intros Hv1 Hv2
  induction vs₁ generalizing σ
  case nil =>
    simp only [List.nil_append]
    have Heq := TouchVarsEmpty Hv1
    simp only [Heq]
    assumption
  case cons h t ih =>
    simp only [List.cons_append]
    cases Hv1 with
    | init_some Hinit Htouch =>
      exact TouchVars.init_some Hinit (ih Htouch)
    | update_some Hup Htouch =>
      exact TouchVars.update_some Hup (ih Htouch)

theorem HavocVarsCons {P : PureExpr} [HasVal P] {f : P.Factory} {σ σ' σ'' : SemanticStore P} {v : P.Ident} {vs : List P.Ident} :
  HavocVars f σ [v] σ' →
  HavocVars f σ' vs σ'' →
  HavocVars f σ (v :: vs) σ'' := by
  intros Hv1 Hv2
  have Heq : (v :: vs = [v] ++ vs) := by rfl
  rw [Heq]
  exact HavocVarsApp Hv1 Hv2

/-- A store can havoc a list of typed slots to their existing values. -/
theorem HavocVarsId {P : PureExpr} [HasVal P] {f : P.Factory}
    {σ : SemanticStore P} {vs : List P.Ident}
    (htyped : ∀ x ∈ vs, ∃ v ty,
      σ x = some v ∧ HasVal.valueOfTy f v ty) :
    HavocVars f σ vs σ := by
  induction vs with
  | nil => constructor
  | cons x xs ih =>
    obtain ⟨v, ty, hx, hv⟩ := htyped x List.mem_cons_self
    apply HavocVars.update_some (σ' := σ) (v := v)
    · exact UpdateState.update hx hx (fun _ _ => rfl)
    · exact ⟨v, ty, hx, hv, hv⟩
    · apply ih
      intro y hy
      exact htyped y (List.mem_cons_of_mem x hy)

theorem TouchVarsId :
  SemanticStore.varsDefined (· ∈ vs) σ →
  TouchVars σ vs σ := by
  intros Hdef
  induction vs
  constructor
  next P h t ih =>
  have Hh := Hdef h List.mem_cons_self
  simp [Option.isSome] at Hh
  split at Hh <;> simp_all
  next x v' heq =>
  apply @TouchVars.update_some (σ':=σ) (v:=v')
  exact UpdateState.update heq heq fun y => congrFun rfl
  apply ih
  simp only [SemanticStore.varsDefined, forall_eq_or_imp] at *
  intros v Hin
  apply Hdef.2 v Hin

theorem InitVarsDefMonotone {vs : List _} :
  SemanticStore.varsDefined (· ∈ vs) σ →
  InitVars σ vs' σ' →
  SemanticStore.varsDefined (· ∈ vs) σ' := by
  intros Hdef Hhavoc
  induction Hhavoc with
  | init_some Hup Hhav ih =>
  apply ih
  apply InitStateDefMonotone <;> assumption
  | init_none => simp_all

theorem InitVarsDefMonotone' {vs vs' : List _} :
  vs.Disj vs' →
  SemanticStore.varsDefined (· ∈ vs) σ' →
  InitVars σ vs' σ' →
  SemanticStore.varsDefined (· ∈ vs) σ := by
  intros Hdisj Hdef Hinit
  have Hinit := InitVarsInitStates Hinit
  cases Hinit with
  | intro es Hinit =>
  exact InitStatesDefMonotone' Hdisj Hdef Hinit

-- theorem InitVarsNotDefMonotone' :
--   vs.Disj vs' →
--   SemanticStore.varsDefined (· ∈ vs) σ' →
--   InitVars σ vs' σ' →
--   SemanticStore.varsUndefined (· ∈ vs) σ := by
--   intros Hdisj Hdef Hinit
--   have Hinit := InitVarsInitStates Hinit
--   cases Hinit
--   | intro es Hinit =>
--   exact InitStatesDefMonotone' Hdisj Hdef Hinit

theorem HavocVarsDefMonotone {P : PureExpr} [HasVal P] {f : P.Factory} {σ σ' : SemanticStore P} {vs vs' : List P.Ident} :
  SemanticStore.varsDefined (· ∈ vs) σ →
  HavocVars f σ vs' σ' →
  SemanticStore.varsDefined (· ∈ vs) σ' := by
  intros Hdef Hhavoc
  induction Hhavoc with
  | update_some Hup Hval Hhav ih =>
  apply ih
  apply UpdateStateDefMonotone <;> assumption
  | update_none => simp_all

theorem HavocVarsUpdateStates {P : PureExpr} [HasVal P] [HasFvars P] [LawfulHasVal P]
    {f : P.Factory} {σ σ' : SemanticStore P} {vars : List P.Ident} :
    HavocVars f σ vars σ' →
    ∃ modvals, UpdateStates σ vars modvals σ' ∧
      ∀ v, v ∈ modvals → HasVal.value f v := by
  intros Hhav
  induction Hhav with
  | update_none =>
    exact ⟨[], UpdateStates.update_none, by intro v hv; simp at hv⟩
  | update_some Hup Htyped Hhav ih =>
    obtain ⟨vs, Hups, Hvals⟩ := ih
    obtain ⟨_, _, _, _, Hv⟩ := Htyped
    refine ⟨_, UpdateStates.update_some Hup Hups, ?_⟩
    intro w hw
    cases hw with
    | head => exact LawfulHasVal.valueOfTy_isVal _ _ _ Hv
    | tail _ hm => exact Hvals w hm

theorem HavocVarsDefMonotone' {P : PureExpr} [HasVal P] [HasFvars P] [LawfulHasVal P] {f : P.Factory} {σ σ' : SemanticStore P} {vs vs' : List P.Ident} :
  SemanticStore.varsDefined (· ∈ vs) σ' →
  HavocVars f σ vs' σ' →
  SemanticStore.varsDefined (· ∈ vs) σ := by
  intros Hdef Hhavoc
  have Hup := HavocVarsUpdateStates Hhavoc
  obtain ⟨es, Hinit, _⟩ := Hup
  exact UpdateStatesDefMonotone' Hdef Hinit

theorem InitVarsDefined :
  InitVars σ vs σ' →
  SemanticStore.varsDefined (· ∈ vs) σ' := by
  intros Hhavoc
  induction vs generalizing σ σ'
  case nil => simp [SemanticStore.varsDefined]
  case cons h t ih =>
    cases Hhavoc with
    | @init_some _ _ v σ₁ _ _ Hup Hhav =>
    apply isDefinedCons
    apply InitVarsDefMonotone (σ:=σ₁)
    apply InitStateDefined <;> assumption
    assumption
    apply ih <;> assumption

/-- Variables introduced by `InitVars` can be read back as values when the
    resulting store contains only value bindings. -/
theorem InitVarsReadValues {P : PureExpr} [HasVal P] {f : P.Factory}
  {σ σ' : SemanticStore P} {ks : List P.Ident} :
  WellFormedStore σ' f →
  InitVars σ ks σ' →
  ∃ vs, ReadValues f σ' ks vs := by
  intro hwf hinit
  exact isDefinedReadValues hwf (InitVarsDefined hinit)

theorem HavocVarsDefined {P : PureExpr} [HasVal P] {f : P.Factory} {σ σ' : SemanticStore P} {vs : List P.Ident} :
  HavocVars f σ vs σ' →
  SemanticStore.varsDefined (· ∈ vs) σ' := by
  intros Hhavoc
  induction Hhavoc with
  | update_none => simp [SemanticStore.varsDefined]
  | update_some Hup Hval Hhav ih =>
    exact isDefinedCons (HavocVarsDefMonotone (UpdateStateDefined Hup) Hhav) ih

theorem UpdateStatesTouchVars : UpdateStates σ vars modvals σ' → TouchVars σ vars σ' := by
  intros H
  induction vars generalizing σ modvals
  case nil =>
    cases modvals
    . have Heq := UpdateStatesEmpty H
      simp only [Heq]
      apply TouchVars.none
    . cases H
  case cons h t ih =>
    have HH := H
    cases H
    next Hup2 =>
    apply TouchVars.update_some <;> try assumption
    apply ih
    apply Hup2

theorem InvStoresUpdatedStateDisjRightMono :
  ¬ k' ∈ ks →
  invStores σ σ' ks →
  invStores σ (updatedState σ' k' v') ks := by
  intros Hnin Hinv
  induction ks generalizing k' v'
  case nil =>
    intros k1 k2 Hin
    cases Hin
  case cons h t ih =>
    intros k1 k2 Hin
    simp_all
    cases Hin
    case inl H =>
      simp only [updatedState, decide_eq_true_eq]
      split
      · simp_all
      · simp_all only
        apply Hinv
        exact List.mem_of_mem_head? rfl
    case inr H =>
      apply ih Hnin.2
      intros k1 k2 Hin
      apply Hinv
      exact List.mem_of_mem_tail Hin
      exact H

theorem InvStoresUpdatedStatesDisjRightMono :
  ks.Disj ks' →
  invStores σ σ' ks →
  ks'.length = vs'.length →
  invStores σ (updatedStates σ' ks' vs') ks := by
  intros Hdis Hinv Hlen k1 k2 Hin
  simp only [updatedStates]
  simp only [zip_self_eq Hin] at *
  induction ks' generalizing vs' σ σ'
  case nil =>
    simp only [List.zip_nil_left, updatedStates']
    exact Hinv k2 k2 Hin
  case cons h t ih =>
    induction vs' generalizing h t σ σ' <;> simp_all
    case cons h' t' ih' =>
      simp only [updatedStates']
      rw [← ih] <;> try simp_all
      . intros k Hin1 Hin2
        apply Hdis Hin1
        exact List.mem_cons_of_mem h Hin2
      . refine InvStoresUpdatedStateDisjRightMono ?_ Hinv
        intros Hin
        exact Hdis Hin List.mem_cons_self

theorem InvStoresUpdatedStateDisjLeftMono :
  ¬ k' ∈ ks →
  invStores σ σ' ks →
  invStores (updatedState σ k' v') σ' ks := by
  intros Hnin Hinv
  have Hinv' := substStoresFlip Hinv
  simp only [invStores]
  apply substStoresFlip'
  simp only [substSwap, zip_swap] at *
  rw [← invStores]
  exact InvStoresUpdatedStateDisjRightMono Hnin Hinv'

theorem InvStoresUpdatedStatesDisjLeftMono :
  ks.Disj ks' →
  invStores σ σ' ks →
  ks'.length = vs'.length →
  invStores (updatedStates σ ks' vs') σ' ks := by
  intros Hnin Hinv Hlen
  have Hinv' := substStoresFlip Hinv
  simp only [invStores]
  apply substStoresFlip'
  simp only [substSwap, zip_swap] at *
  rw [← invStores]
  apply InvStoresUpdatedStatesDisjRightMono Hnin Hinv' Hlen

theorem InvStoresExceptEmpty : invStoresExcept σ σ [] :=
  fun _ _ _ _ Hin => congrArg σ (zip_self_eq Hin)

theorem InvStoresExceptId : invStoresExcept σ σ ls :=
  fun _ _ _ _ Hin => congrArg σ (zip_self_eq Hin)

theorem InvStoresExceptApp :
  invStoresExcept σ σ' ks →
  invStoresExcept σ σ' (ks ++ ks') := by
  intros Hinv x Hdisj
  apply Hinv
  exact List.DisjAppRight' Hdisj

theorem InvStoresExceptUpdated :
  invStoresExcept σ σ' ks →
  ks'.length = vs'.length →
  invStoresExcept (updatedStates σ ks' vs') σ' (ks ++ ks') := by
  intros Hinv Hlen
  simp only [invStoresExcept] at *
  intros vsInv Hdisj
  refine InvStoresUpdatedStatesDisjLeftMono ?_ ?_ Hlen
  exact List.DisjAppLeft' Hdisj
  apply Hinv
  exact List.DisjAppRight' Hdisj

theorem UpdatedStatesInSame :
  k ∈ ks' →
  ks'.length = vs'.length →
  ks'.Nodup →
  updatedStates σ ks' vs' k = updatedStates σ' ks' vs' k := by
  intros Hin Hlen Hnd
  induction ks' generalizing vs' k σ σ' <;>
    simp [updatedStates, updatedStates'] <;> simp_all
  case cons h t ih =>
    cases vs'
    case nil => simp_all
    case cons =>
    simp only [List.zip_cons_cons, updatedStates']
    cases Hin with
    | inl Heq =>
      simp_all only [List.length_cons, Nat.add_right_cancel_iff]
      rw [← updatedStateComm']
      rw [← updatedStateComm']
      simp [updatedState]
      . simp_all only [List.unzip_fst, List.mem_map, Prod.exists, exists_and_right, exists_eq_right, not_exists]
        intros x Hin
        have HH := List.of_mem_zip Hin
        simp_all
      . simp_all only [List.unzip_fst, List.mem_map, Prod.exists, exists_and_right, exists_eq_right, not_exists]
        intros x Hin
        have HH := List.of_mem_zip Hin
        simp_all
    | inr Hin =>
      apply ih <;> simp_all

theorem UpdatedStatesNotinSame :
  σ k = σ' k →
  ¬ k ∈ ks' →
  ks'.length = vs'.length →
  ks'.Nodup →
  updatedStates σ ks' vs' k = updatedStates σ' ks' vs' k := by
  intros Heq Hnin Hlen Hnd
  induction ks' generalizing vs' k σ σ' <;>
    simp [updatedStates, updatedStates'] <;> simp_all
  case cons h t ih =>
    cases vs'
    case nil => simp_all
    case cons =>
    simp only [List.zip_cons_cons, updatedStates']
    rw [← updatedStateComm']
    rw [← updatedStateComm']
    . simp only [updatedState, decide_eq_true_eq]
      split
      · simp_all
      · simp_all only [not_false_eq_true, true_and, List.length_cons, Nat.add_right_cancel_iff]
        apply ih <;> simp_all
    . simp_all only [List.length_cons, Nat.add_right_cancel_iff, List.unzip_fst, List.mem_map, Prod.exists, exists_and_right, exists_eq_right, not_exists]
      intros x Hin
      have HH := List.of_mem_zip Hin
      simp_all
    . simp_all only [List.length_cons, Nat.add_right_cancel_iff, List.unzip_fst, List.mem_map, Prod.exists, exists_and_right, exists_eq_right, not_exists]
      intros x Hin
      have HH := List.of_mem_zip Hin
      simp_all

theorem InvStoresExceptUpdatedSame :
  invStoresExcept σ σ' ks →
  ks'.length = vs'.length →
  ks'.Nodup →
  invStoresExcept (updatedStates σ ks' vs') (updatedStates σ' ks' vs') ks := by
  intros Hinv Hlen Hnd
  simp only [invStoresExcept] at *
  intros vsInv Hdisj k1 k2 Hin
  have Heq := zip_self_eq Hin
  simp only [Heq]
  by_cases Hin : k2 ∈ ks'
  case pos =>
    exact UpdatedStatesInSame Hin Hlen Hnd
  case neg =>
    refine UpdatedStatesNotinSame ?_ Hin Hlen Hnd
    apply Hinv _ Hdisj
    simp_all

theorem InvStoresExceptUpdatedMem :
  invStoresExcept σ σ' ks →
  ks'.length = vs'.length →
  ks'.Subset ks →
  invStoresExcept (updatedStates σ ks' vs') σ' ks := by
  intros Hinv Hlen
  simp only [invStoresExcept] at *
  intros Hsub vs Hdisj
  refine InvStoresUpdatedStatesDisjLeftMono ?_ ?_ Hlen
  exact List.Disjoint_Subset_right Hdisj Hsub
  exact Hinv _ Hdisj

theorem InvStoresExceptHavocVars {P : PureExpr} [HasVal P] [HasFvars P] [LawfulHasVal P] {f : P.Factory} {σ σ' σ'' : SemanticStore P} {ks ks' : List P.Ident} :
  invStoresExcept σ σ' ks →
  HavocVars f σ ks' σ'' →
  invStoresExcept σ'' σ' (ks ++ ks') := by
  intros Hinv Hup
  have Hup' := HavocVarsUpdateStates Hup
  obtain ⟨vs', Hups, _⟩ := Hup'
  exact InvStoresExceptUpdateStates Hinv Hups

theorem InvStoresExceptInitVars :
  invStoresExcept σ σ' ks →
  InitVars σ ks' σ'' →
  invStoresExcept σ'' σ' (ks ++ ks') := by
  intros Hinv Hup
  have Hup' := InitVarsInitStates Hup
  cases Hup' with
  | intro vs' Hups =>
  exact InvStoresExceptInitStates Hinv Hups

theorem InvStoresExceptInvStores :
  invStoresExcept σ σ' ks →
  List.Disj ks ks' →
  invStores σ σ' ks' := by
  intros Hinv Hdis k1 k2 Hin
  apply Hinv ks'
  exact List.Disj.symm Hdis
  assumption

/-- A structured body consisting of one `assert` preserves its entry store on every
completed event run. The assertion does not write, and leaving the procedure block
projects the unchanged inner store through the identical parent store. -/
theorem assertBodyE_preserves_store
    (π : String → Option Procedure)

    (l : String) (e : Expression.Expr) (md : MetaData Expression)
    (σ_entry : CoreStore) (fac : Expression.Factory) (ρ' : Env Expression)
    (emitted : Trace Expression)
    (hrun : CoreStepStarE π
      (.stmt (Stmt.block "" [Stmt.cmd (CmdExt.cmd (Cmd.assert l e md))] #[])
        ⟨σ_entry, fac⟩) emitted (.terminal ρ')) :
    ρ'.store = σ_entry := by
  obtain ⟨ρ_inner, hinner, hρ'⟩ :=
    stmt_block_reaches_doneE (P := Expression) (EvalCmd := EvalCommandE π)
      (.inl hrun)
  have hbody_store : ρ_inner.store = σ_entry := by
    rcases hinner with hterm | ⟨lbl, hexit⟩
    · rcases stmts_cons_headE (EvalCmd := EvalCommandE π)
        hterm with ⟨hcfg, _⟩ | hseq
      · exact absurd hcfg (by simp)
      · rcases seq_run_decomposeE (EvalCmd := EvalCommandE π)
          hseq with
          ⟨_, hcfg, _⟩ | ⟨ρ₁, tr₁, tr₂, _htr, hhead, htail⟩ | ⟨_, _, hcfg, _⟩
        · exact absurd hcfg (by simp)
        · obtain ⟨_, htailcfg⟩ := stmts_nil_runE (EvalCmd := EvalCommandE π)
            htail
          have hρ_inner : ρ_inner = ρ₁ := by
            rcases htailcfg with h | h
            · exact absurd h (by simp)
            · exact Config.terminal.injEq _ _ ▸ h
          cases hhead with
          | step _ _ _ _ _ hstep hrest =>
            cases hstep with
            | step_cmd hcmd =>
              obtain ⟨hz, _⟩ := stepStmtStarE_from_terminal
                (EvalCmd := EvalCommandE π) hrest
              cases hcmd with
              | cmd_sem hbase =>
                cases hbase with
                | eval_assert =>
                  rw [hρ_inner]
                  injection hz with hz'
                  rw [hz']
        · exact absurd hcfg (by simp)
    · rcases stmts_cons_headE (EvalCmd := EvalCommandE π)
        hexit with ⟨hcfg, _⟩ | hseq
      · exact absurd hcfg (by simp)
      · rcases seq_run_decomposeE (EvalCmd := EvalCommandE π)
          hseq with
          ⟨_, hcfg, _⟩ | ⟨ρ₁, tr₁, tr₂, _htr, hhead, htail⟩ | ⟨lbl2, ρ₁, hcfg, hhead⟩
        · exact absurd hcfg (by simp)
        · obtain ⟨_, htailcfg⟩ := stmts_nil_runE (EvalCmd := EvalCommandE π)
            htail
          rcases htailcfg with h | h
          · exact absurd h (by simp)
          · exact absurd h (by simp)
        · cases hhead with
          | step _ _ _ _ _ hstep hrest =>
            cases hstep with
            | step_cmd hcmd =>
              obtain ⟨hz, _⟩ := stepStmtStarE_from_terminal
                (EvalCmd := EvalCommandE π) hrest
              exact absurd hz (by simp)
  rw [hρ']
  show projectStore σ_entry ρ_inner.store = σ_entry
  rw [hbody_store, projectStore_self]

/-- Agreement off a single key `k` yields `invStoresExcept _ _ [k]`. -/
private theorem invStoresExcept_singleton_of_agree_off
    {σ σ' : CoreStore} {k : Expression.Ident}
    (h : ∀ y, k ≠ y → σ y = σ' y) : Imperative.invStoresExcept σ σ' [k] := by
  intro vs' hdisj k1 k2 hin
  have heq : k1 = k2 := zip_self_eq hin
  subst heq
  have hmem : k1 ∈ vs' := (List.of_mem_zip hin).1
  have hnotin : k1 ∉ [k] := hdisj hmem
  have hne : k ≠ k1 := by
    intro hc; exact hnotin (hc ▸ List.mem_singleton.mpr rfl)
  exact h k1 hne

/-- An `UpdateState` that writes only `k` gives `invStoresExcept` (to the
projected store) with exception `[k]`. -/
private theorem invStoresExcept_projectStore_of_update
    {σ σ' : CoreStore} {k : Expression.Ident} {v : Expression.Val}
    (hupd : Imperative.UpdateState Expression σ k v σ') :
    Imperative.invStoresExcept σ (Imperative.projectStore σ σ') [k] := by
  cases hupd with
  | update hv' hv hother =>
    refine invStoresExcept_singleton_of_agree_off (fun y hy => ?_)
    unfold Imperative.projectStore
    by_cases hs : (σ y).isSome
    · rw [ite_eq_left hs]; exact (hother y hy).symm
    · rw [ite_eq_right hs]; exact Option.not_isSome_iff_eq_none.mp hs

/-- **A one-`set` structured body respects the write set `[x]`.** Every completed
event run of `{ x := e }` from `σ_entry` leaves a procedure-exit store that agrees
with `σ_entry` everywhere except `x`. -/
theorem setBodyE_frame
    (π : String → Option Procedure)

    (x : Expression.Ident) (e : Expression.Expr) (md : MetaData Expression)
    (σ_entry : CoreStore) (fac : Expression.Factory) (ρ' : Env Expression)
    (emitted : Trace Expression)
    (hrun : CoreStepStarE π
      (.stmt (Stmt.block "" [Stmt.cmd (CmdExt.cmd (Cmd.set x (.det e) md))] #[])
        ⟨σ_entry, fac⟩) emitted (.terminal ρ')) :
    Imperative.invStoresExcept σ_entry ρ'.store [x] := by
  obtain ⟨ρ_inner, hinner, hρ'⟩ :=
    stmt_block_reaches_doneE (P := Expression) (EvalCmd := EvalCommandE π)
      (.inl hrun)
  rw [hρ']
  show Imperative.invStoresExcept σ_entry
    (Imperative.projectStore σ_entry ρ_inner.store) [x]
  -- The single-command `UpdateState` that produced `ρ_inner.store`.
  rcases hinner with hterm | ⟨lbl, hexit⟩
  · rcases stmts_cons_headE (EvalCmd := EvalCommandE π)
      hterm with ⟨hcfg, _⟩ | hseq
    · exact absurd hcfg (by simp)
    · rcases seq_run_decomposeE (EvalCmd := EvalCommandE π)
        hseq with
        ⟨_, hcfg, _⟩ | ⟨ρ₁, tr₁, tr₂, _htr, hhead, htail⟩ | ⟨_, _, hcfg, _⟩
      · exact absurd hcfg (by simp)
      · obtain ⟨_, htailcfg⟩ := stmts_nil_runE (EvalCmd := EvalCommandE π)
          htail
        have hρ_inner : ρ_inner = ρ₁ := by
          rcases htailcfg with h | h
          · exact absurd h (by simp)
          · exact Config.terminal.injEq _ _ ▸ h
        cases hhead with
        | step _ _ _ _ _ hstep hrest =>
          cases hstep with
          | step_cmd hcmd =>
            obtain ⟨hz, _⟩ := stepStmtStarE_from_terminal
              (EvalCmd := EvalCommandE π) hrest
            cases hcmd with
            | cmd_sem hbase =>
              cases hbase with
              | eval_set heval hupd hwfv =>
                subst hρ_inner
                injection hz with hz'
                subst hz'
                exact invStoresExcept_projectStore_of_update hupd
      · exact absurd hcfg (by simp)
  · rcases stmts_cons_headE (EvalCmd := EvalCommandE π)
      hexit with ⟨hcfg, _⟩ | hseq
    · exact absurd hcfg (by simp)
    · rcases seq_run_decomposeE (EvalCmd := EvalCommandE π)
        hseq with
        ⟨_, hcfg, _⟩ | ⟨ρ₁, tr₁, tr₂, _htr, hhead, htail⟩ | ⟨lbl2, ρ₁, hcfg, hhead⟩
      · exact absurd hcfg (by simp)
      · obtain ⟨_, htailcfg⟩ := stmts_nil_runE (EvalCmd := EvalCommandE π)
          htail
        rcases htailcfg with h | h
        · exact absurd h (by simp)
        · exact absurd h (by simp)
      · cases hhead with
        | step _ _ _ _ _ hstep hrest =>
          cases hstep with
          | step_cmd hcmd =>
            obtain ⟨hz, _⟩ := stepStmtStarE_from_terminal
              (EvalCmd := EvalCommandE π) hrest
            exact absurd hz (by simp)

variable (π : String → Option Procedure)

/-! ## Store-domain preservation along a Core run

Command-level store facts for `UpdateState`/`UpdateStates`, used by the
event-trace store-domain results below. -/

/-- `UpdateState` cannot define a slot that was undefined: it requires its
    target to already hold a value, and leaves every other slot unchanged. -/
private theorem updateState_preserves_none
    {σ σ' : SemanticStore Expression} {x : Expression.Ident} {v : Expression.Val}
    (h : UpdateState Expression σ x v σ') :
    ∀ y, σ y = none → σ' y = none := by
  cases h with
  | update h_some _ h_other =>
    intro y hy
    by_cases hxy : x = y
    · subst hxy; rw [hy] at h_some; exact absurd h_some (by simp)
    · rw [h_other y hxy]; exact hy

/-- `UpdateState` cannot undefine a slot: the target keeps a value and every
    other slot is unchanged. -/
private theorem updateState_preserves_isSome
    {σ σ' : SemanticStore Expression} {x : Expression.Ident} {v : Expression.Val}
    (h : UpdateState Expression σ x v σ') :
    ∀ y, (σ y).isSome = true → (σ' y).isSome = true := by
  cases h with
  | update _ h_some' h_other =>
    intro y hy
    by_cases hxy : x = y
    · subst hxy; rw [h_some']; simp
    · rw [h_other y hxy]; exact hy

/-- Pointwise lift of `updateState_preserves_none` along a whole write-back. -/
private theorem updateStates_preserves_none
    {σ σ' : SemanticStore Expression} {xs : List Expression.Ident}
    {vs : List Expression.Val}
    (h : UpdateStates σ xs vs σ') :
    ∀ y, σ y = none → σ' y = none := by
  induction h with
  | update_none => exact fun _ hy => hy
  | update_some hupd _ ih =>
    exact fun y hy => ih y (updateState_preserves_none hupd y hy)

/-- Pointwise lift of `updateState_preserves_isSome` along a whole write-back. -/
private theorem updateStates_preserves_isSome
    {σ σ' : SemanticStore Expression} {xs : List Expression.Ident}
    {vs : List Expression.Val}
    (h : UpdateStates σ xs vs σ') :
    ∀ y, (σ y).isSome = true → (σ' y).isSome = true := by
  induction h with
  | update_none => exact fun _ hy => hy
  | update_some hupd _ ih =>
    exact fun y hy => ih y (updateState_preserves_isSome hupd y hy)

/-- Writing a list of *values* into a store that holds only values leaves a store
    that holds only values. -/
private theorem updateStates_preserves_wellFormedStore {f : Expression.Factory}
    {σ σ' : SemanticStore Expression} {xs : List Expression.Ident}
    {vs : List Expression.Val}
    (h : UpdateStates σ xs vs σ') (hvs : ∀ v ∈ vs, HasVal.value f v)
    (hsv : Imperative.WellFormedStore σ f) :
    Imperative.WellFormedStore σ' f := by
  induction h with
  | update_none => exact hsv
  | update_some hupd _hrest ih =>
    rename_i x v _xs _vs _σa _σb
    refine ih (fun w hw => hvs w (List.mem_cons_of_mem _ hw)) ?_
    cases hupd with
    | update _hold hnew hoth =>
      intro z w hz
      by_cases hzx : x = z
      · subst hzx; rw [hnew] at hz; cases hz
        exact hvs v List.mem_cons_self
      · rw [hoth z hzx] at hz; exact hsv z w hz

/-- An `EvalCommandE` step preserves a `none` slot it does not declare; a `call`
    declares nothing. -/
theorem evalCommandE_preserves_none_of_not_def
    {f : Expression.Factory} {σ σ' : SemanticStore Expression} {c : Command}
    {emitted : Imperative.Trace Expression} {y : Expression.Ident}
    (h_eval : EvalCommandE π f σ c σ' emitted)
    (h_none : σ y = none)
    (h_not_def : y ∉ HasVarsImp.definedVars (P := Expression) c false) :
    σ' y = none := by
  cases h_eval with
  | cmd_sem h =>
    exact Imperative.evalCmdE_preserves_none_of_not_def h h_none
      (by simpa [HasVarsImp.definedVars, Command.definedVars, CmdExt.definedVars] using h_not_def)
  | call_sem _ _ _ hexit =>
    unfold Calls.CallExit at hexit
    obtain ⟨_, _, _, hupd, -⟩ := hexit
    exact updateStates_preserves_none hupd y h_none

/-! ### Event-trace store-domain characterization

Store-domain lemmas for `StepStmtStarE` / `EvalCommandE` runs, needed to
re-establish `BlockInitEnvWF` on the tail of a statement list after a run.
`EvalCommandE` base commands are the event-native `EvalCmdE`; a `call` writes
only through `CallExit`'s `UpdateStates`. -/

/-- An `EvalCommandE` step never undefines a store slot that was already
defined. -/
theorem evalCommandE_preserves_isSome
    {f : Expression.Factory} {σ σ' : SemanticStore Expression} {c : Command}
    {emitted : Imperative.Trace Expression} {y : Expression.Ident}
    (h_eval : EvalCommandE π f σ c σ' emitted)
    (h_some : (σ y).isSome = true) :
    (σ' y).isSome = true := by
  cases h_eval with
  | cmd_sem h => exact Imperative.evalCmdE_preserves_isSome h h_some
  | call_sem _ _ _ hexit =>
    unfold Calls.CallExit at hexit
    obtain ⟨_, _, _, hupd, -⟩ := hexit
    exact updateStates_preserves_isSome hupd y h_some

/-- An `EvalCommandE` step preserves the property that every store binding is
a value. -/
theorem evalCommandE_storeWellDefined
    {fac : Expression.Factory} {σ σ' : CoreStore} {c : Command}
    {emitted : Imperative.Trace Expression}
    (h : EvalCommandE π fac σ c σ' emitted)
    (hsv : Imperative.WellFormedStore σ fac) :
    Imperative.WellFormedStore σ' fac := by
  cases h with
  | cmd_sem hcmd =>
    exact Imperative.evalCmdE_storeWellDefined
      (coreEvaluator_WellFormedSemanticEvalVal fac) hcmd hsv
  | call_sem _ _ _ hexit =>
    unfold Calls.CallExit at hexit
    obtain ⟨_, _, hread, hupd, -⟩ := hexit
    exact updateStates_preserves_wellFormedStore hupd
      (ReadValues.all_values hread) hsv

/-- An `EvalCommandE` step keeps a typed slot at its type; a `call` writes back to each
caller variable a value of the type the variable held. -/
theorem evalCommandE_preserves_typedAt
    {f : Expression.Factory} {σ σ' : SemanticStore Expression} {c : Command}
    {emitted : Imperative.Trace Expression} {y : Expression.Ident} {ty : Expression.Ty}
    (h_eval : EvalCommandE π f σ c σ' emitted)
    (hy : ∃ v, σ y = some v ∧ HasVal.valueOfTy f v ty) :
    ∃ v, σ' y = some v ∧ HasVal.valueOfTy f v ty := by
  cases h_eval with
  | cmd_sem h => exact Imperative.EvalCmdE_preserves_typedAt h hy
  | call_sem _ _ _ hexit =>
    obtain ⟨_, _, _, hupd, hrel⟩ := hexit
    exact Imperative.UpdateStates_typedAt hupd hrel hy hy

/-- A slot that holds a value of type `ty` at the start of a terminating event-native
`.stmt` run holds a value of type `ty` at the end. -/
theorem core_stmt_preserves_typedAtE
    {s : Statement} {ρ ρ' : Env Expression} {tr : Imperative.Trace Expression}
    (h_run : CoreStepStarE π (.stmt s ρ) tr (.terminal ρ'))
    {y : Expression.Ident} {ty : Expression.Ty}
    (hy : ∃ v, ρ.store y = some v ∧ HasVal.valueOfTy ρ.factory v ty) :
    ∃ v, ρ'.store y = some v ∧ HasVal.valueOfTy ρ'.factory v ty := by
  have hv : (ρ.store y).isSome = true := by obtain ⟨v, hv, _⟩ := hy; simp [hv]
  exact Config.typedAt_star_ofE
    (fun he hs => evalCommandE_preserves_isSome π he hs)
    (fun he hs => evalCommandE_preserves_typedAt π he hs) h_run
    (show Config.varDefined y (.stmt s ρ) from fun _ hz => hz ▸ hv) hy

/-- A slot that holds a value of type `ty` at the start of a terminating event-native
`.stmts` run holds a value of type `ty` at the end. -/
theorem core_stmts_preserves_typedAtE
    {ss : Statements} {ρ ρ' : Env Expression} {tr : Imperative.Trace Expression}
    (h_run : CoreStepStarE π (.stmts ss ρ) tr (.terminal ρ'))
    {y : Expression.Ident} {ty : Expression.Ty}
    (hy : ∃ v, ρ.store y = some v ∧ HasVal.valueOfTy ρ.factory v ty) :
    ∃ v, ρ'.store y = some v ∧ HasVal.valueOfTy ρ'.factory v ty := by
  have hv : (ρ.store y).isSome = true := by obtain ⟨v, hv, _⟩ := hy; simp [hv]
  exact Config.typedAt_star_ofE
    (fun he hs => evalCommandE_preserves_isSome π he hs)
    (fun he hs => evalCommandE_preserves_typedAt π he hs) h_run
    (show Config.varDefined y (.stmts ss ρ) from fun _ hz => hz ▸ hv) hy

/-- A terminating event-native `.stmt s` run keeps the store conforming to a typing of its
start store, extended with the typed definitions of `s`. -/
theorem core_stmt_run_storeHasTyping_extendE
    {s : Statement} {ρ ρ' : Env Expression} {tr : Imperative.Trace Expression}
    {Γ : VarTyping Expression}
    (h_run : CoreStepStarE π (.stmt s ρ) tr (.terminal ρ'))
    (hσ : StoreHasTyping ρ.factory ρ.store Γ) :
    StoreHasTyping ρ'.factory ρ'.store (Γ.extend (Stmt.typedDefinedVars s)) := by
  by_cases hinit : ∃ x ty e md, s = .cmd (.cmd (.init x ty e md))
  · obtain ⟨x, ty, e, md, rfl⟩ := hinit
    cases h_run with
    | step _ _ _ _ _ hstep hrest =>
      cases hstep with
      | step_cmd h_eval =>
        obtain ⟨hcfg, _⟩ := Imperative.stepStmtStarE_from_terminal hrest
        injection hcfg with hρ
        subst hρ
        cases h_eval with
        | cmd_sem h =>
          simp only [Stmt.typedDefinedVars, HasTypedVarsImp.typedDefinedVars,
            CmdExt.typedDefinedVars, Cmd.typedDefinedVars]
          rw [VarTyping.extend_singleton]
          exact Imperative.EvalCmdE.init_storeHasTyping h hσ
  · have hnil : Stmt.typedDefinedVars s = [] := by
      match s with
      | .cmd (.cmd (.init x ty e md)) => exact absurd ⟨x, ty, e, md, rfl⟩ hinit
      | .cmd (.cmd (.set ..)) | .cmd (.cmd (.assert ..)) | .cmd (.cmd (.assume ..))
      | .cmd (.cmd (.cover ..)) | .cmd (.call ..) | .block .. | .ite .. | .loop ..
      | .exit .. | .typeDecl .. => rfl
    rw [hnil, VarTyping.extend_nil]
    intro y ty hy
    exact core_stmt_preserves_typedAtE π h_run (hσ y ty hy)

/-- An event-semantics command defines every slot it declares. A `call`
declares nothing, so that case is vacuous. -/
private theorem evalCommandE_definedVars_isSome
    {f : Expression.Factory} {σ σ' : SemanticStore Expression} {c : Command}
    {emitted : Imperative.Trace Expression} {y : Expression.Ident}
    (h_eval : EvalCommandE π f σ c σ' emitted)
    (h_def : y ∈ HasVarsImp.definedVars (P := Expression) c true) :
    (σ' y).isSome = true := by
  cases h_eval with
  | cmd_sem h =>
    exact Imperative.evalCmdE_definedVars_isSome h
      (by simpa [HasVarsImp.definedVars, Command.definedVars, CmdExt.definedVars] using h_def)
  | call_sem => simp [HasVarsImp.definedVars, CmdExt.definedVars] at h_def

/-- A store slot defined at the start of a terminating event-native `.stmt`
run remains defined at the end. -/
private theorem core_stmt_preserves_isSomeE
    {y : Expression.Ident} {s : Statement} {ρ ρ' : Env Expression}
    {tr : Imperative.Trace Expression}
    (h_run : CoreStepStarE π
      (.stmt s ρ) tr (.terminal ρ'))
    (h_some : (ρ.store y).isSome = true) :
    (ρ'.store y).isSome = true :=
  Config.varsDefined_star_ofE
    (fun he hs => evalCommandE_preserves_isSome π he hs)
    h_run
    (show Config.varDefined y (.stmt s ρ) from fun _ hz => hz ▸ h_some) y rfl

/-- A slot defined at the start
of a terminating event-native `.stmts` run is still defined at the end. -/
theorem core_stmts_preserves_isSomeE
    {y : Expression.Ident} {ss : Statements} {ρ ρ' : Env Expression}
    {tr : Imperative.Trace Expression}
    (h_run : CoreStepStarE π
      (.stmts ss ρ) tr (.terminal ρ'))
    (h_some : (ρ.store y).isSome = true) :
    (ρ'.store y).isSome = true :=
  Config.varsDefined_star_ofE
    (fun he hs => evalCommandE_preserves_isSome π he hs)
    h_run
    (show Config.varDefined y (.stmts ss ρ) from fun _ hz => hz ▸ h_some) y rfl

/-- A store slot that starts undefined and is not defined by the statement
remains undefined after a terminating event-native `.stmt` run. -/
theorem core_stmt_run_terminal_preserves_none_of_not_definedVars_trueE
    {y : Expression.Ident} {s : Statement} {ρ ρ' : Env Expression}
    {tr : Imperative.Trace Expression}
    (h_y_not_def : y ∉ Stmt.definedVars (P := Expression) (C := Command) s true)
    (h_none : ρ.store y = none)
    (h_run : CoreStepStarE π
      (.stmt s ρ) tr (.terminal ρ')) :
    ρ'.store y = none :=
  Config.varsUndefinedScoped_star_ofE
    (fun he hn hnd => evalCommandE_preserves_none_of_not_def π he hn hnd)
    h_run
    (by rintro z rfl; exact ⟨h_none, h_y_not_def⟩) y rfl

/-- After a terminating event-native `.stmt` run, a store slot is defined
exactly when it was defined initially or the statement defines it. -/
theorem core_stmt_run_terminal_store_isSome_eqE
    {s : Statement} {ρ ρ' : Env Expression} {tr : Imperative.Trace Expression}
    (h_run : CoreStepStarE π
      (.stmt s ρ) tr (.terminal ρ')) (n : Expression.Ident) :
    (ρ'.store n).isSome
      = ((ρ.store n).isSome ||
          decide (n ∈ Stmt.definedVars (P := Expression) (C := Command) s true)) := by
  by_cases hd : n ∈ Stmt.definedVars (P := Expression) (C := Command) s true
  · simp only [hd, decide_true, Bool.or_true]
    match s with
    | .cmd c =>
      cases h_run with
      | step _ _ _ _ _ hstep hrest =>
        cases hstep with
        | step_cmd h_eval =>
          obtain ⟨hcfg, _⟩ := Imperative.stepStmtStarE_from_terminal hrest
          injection hcfg with hρ
          subst hρ
          simp only [Stmt.definedVars] at hd
          exact evalCommandE_definedVars_isSome π h_eval hd
    | .block .. | .ite .. | .loop .. | .exit .. | .typeDecl .. =>
      simp [Stmt.definedVars] at hd
  · simp only [hd, decide_false, Bool.or_false]
    by_cases hs : (ρ.store n).isSome = true
    · rw [hs, core_stmt_preserves_isSomeE π h_run hs]
    · have hnone : ρ.store n = none := by
        cases h : ρ.store n with
        | none => rfl
        | some v => rw [h] at hs; simp at hs
      rw [hnone] at hs
      rw [core_stmt_run_terminal_preserves_none_of_not_definedVars_trueE π hd hnone h_run,
        hnone]

/-! ## projectStore and expression evaluation -/

/-- If an expression evaluates in the projected store, it evaluates identically
    in the full store. The projected store only removes variables, and expression
    evaluation depends only on the variables it references. The `hdom` hypothesis
    ensures all free variables of `e` are bound in the projected store. -/
theorem eval_projectStore_to_full
    {f : Expression.Factory} {σ₀ σ : SemanticStore Expression}
    {e : Expression.Expr} {v : Expression.Val}
    (h_eval : Expression.eval f (projectStore σ₀ σ) e = some v)
    (h_wfStore : WellFormedStore σ f)
    (hdom : ∀ x ∈ HasFvars.getFvars e, (projectStore σ₀ σ) x ≠ none) :
    Expression.eval f σ e = some v := by
  have h_wfStoreProj : WellFormedStore (projectStore σ₀ σ) f := by
    intro x w hx
    simp only [projectStore] at hx
    split at hx
    · exact h_wfStore x w hx
    · exact absurd hx (by simp)
  have h_agree : ∀ x ∈ HasFvars.getFvars e, (projectStore σ₀ σ) x = σ x := by
    intro x hx
    have h_ne := hdom x hx
    simp only [projectStore] at h_ne ⊢
    split
    · rfl
    · simp [*] at h_ne
  rw [← coreEvaluator_WellFormedSemanticEvalExprCongr f e _ _ h_wfStoreProj h_wfStore h_agree]
  exact h_eval

/-! ## Assert-only blocks preserve store -/

/-! ## mapExprs identity -/

private theorem block_mapExpr_id_of_forall {ss : List Statement}
    (h : ∀ s, s ∈ ss → Statement.mapExprs id s = s) :
    Imperative.Block.mapExpr id (Command.mapExpr id) ss = ss := by
  induction ss with
  | nil => simp [Imperative.Block.mapExpr]
  | cons s rest ih =>
    simp only [Imperative.Block.mapExpr, List.cons.injEq]
    exact ⟨h s (.head _), ih (fun s hs => h s (.tail _ hs))⟩

private theorem list_mapExprs_id_of_forall {ss : List Statement}
    (h : ∀ s, s ∈ ss → Statement.mapExprs id s = s) :
    ss.map (Statement.mapExprs id) = ss := by
  induction ss with
  | nil => rfl
  | cons s rest ih =>
    simp only [List.map_cons, List.cons.injEq]
    exact ⟨h s (.head _), ih (fun s hs => h s (.tail _ hs))⟩

private theorem Command.mapExpr_id (c : Command) : Command.mapExpr id c = c := by
  cases c with
  | cmd c =>
    cases c with
    | assert _ _ _ | assume _ _ _ | cover _ _ _ => simp [Command.mapExpr]
    | init n ty e md => cases e <;> simp [Command.mapExpr]
    | set n e md => cases e <;> simp [Command.mapExpr]
  | call pname args md =>
    simp only [mapExpr, CmdExt.call.injEq, and_true, true_and]
    induction args with
    | nil => rfl
    | cons h t ih => simp [ih]; cases h <;> rfl

theorem Statement.mapExprs_id (s : Statement) : Statement.mapExprs id s = s := by
  induction s using Stmt.inductionOn with
  | cmd_case c =>
    simp only [Statement.mapExprs, Imperative.Stmt.mapExpr]
    exact congrArg Stmt.cmd (Command.mapExpr_id c)
  | block_case l ss md ih =>
    simp [Statement.mapExprs, Imperative.Stmt.mapExpr, block_mapExpr_id_of_forall ih]
  | ite_case cond tss ess md iht ihe =>
    cases cond <;> simp [Statement.mapExprs, Imperative.Stmt.mapExpr,
                          block_mapExpr_id_of_forall iht, block_mapExpr_id_of_forall ihe]
  | loop_case guard measure inv body md ihb =>
    cases guard <;> simp [Statement.mapExprs, Imperative.Stmt.mapExpr,
                           block_mapExpr_id_of_forall ihb]
  | exit_case l md => simp [Statement.mapExprs, Imperative.Stmt.mapExpr]
  | typeDecl_case tc md => simp [Statement.mapExprs, Imperative.Stmt.mapExpr]

theorem Statements.mapExprs_id (ss : Statements) : Statements.mapExprs id ss = ss := by
  exact list_mapExprs_id_of_forall (fun s _ => Statement.mapExprs_id s)

/-! ## A statement and the one-element list holding it -/

section SingletonRuns

variable {π : String → Option Procedure}

/-- A run of a statement is a run of the one-element list holding it, with the
    same trace. -/
theorem stmt_run_to_singleton_runE {s : Statement} {ρ : Imperative.Env Expression}
    {cfg : CoreConfig} {tr : Trace Expression}
    (h : CoreStepStarE π (.stmt s ρ) tr cfg) :
    CoreStepStarE π (.stmts [s] ρ) tr (.seq cfg []) := by
  have hcons : CoreStepE π (.stmts [s] ρ) [] (.seq (.stmt s ρ) []) :=
    .step_stmts_cons
  simpa using ReflTransTrace.step _ _ _ _ _ hcons
    (Imperative.seq_inner_starE _ (ss := []) h)

/-- Every trace of the one-element list holding a statement is a trace of the
    statement itself. -/
theorem singleton_run_to_stmt_runE {s : Statement} {ρ : Imperative.Env Expression}
    {cfg : CoreConfig} {tr : Trace Expression}
    (h : CoreStepStarE π (.stmts [s] ρ) tr cfg) :
    ∃ cfg', CoreStepStarE π (.stmt s ρ) tr cfg' := by
  rcases Imperative.stmts_cons_headE _ h with ⟨_, rfl⟩ | h
  · exact ⟨_, .refl _⟩
  · rcases Imperative.seq_run_decomposeE _ h with
      ⟨inner', _, hi⟩ | ⟨ρ₁, tr₁, tr₂, rfl, h1, h2⟩ | ⟨_, _, _, hi⟩
    · exact ⟨_, hi⟩
    · obtain ⟨rfl, _⟩ := Imperative.stmts_nil_runE _ h2
      exact ⟨_, by simpa using h1⟩
    · exact ⟨_, hi⟩

end SingletonRuns

end Core

end -- public section
