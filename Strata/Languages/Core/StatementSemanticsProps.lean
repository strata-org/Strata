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

Metatheory of Core's own statement semantics (`EvalCommand`, `CoreStepStar`).  Key
results include `initStates_preserves_wf` and `withOldSnapshots_preserves_wf` for
constructing well-formed call frames, beyond the remaining
`InitStates`/`UpdateStates`/`HavocVars` plumbing:

- Store-domain characterization of a run: `evalCommand_preserves_none_of_not_def`
  and `evalCommand_preserves_isSome` at the command level, lifted to
  `core_stmt_run_terminal_preserves_none_of_not_definedVars_true`,
  `core_block_run_terminal_preserves_none_of_not_definedVars` and
  `core_stmts_preserves_isSome`, and combined in
  `core_stmt_run_terminal_store_isSome_eq`, which pins the store domain after a
  statement *exactly*: an inclusion either way is not enough, because
  `defUseWellFormed` uses its definedness predicate in both directions.
- `EvalExpressionsInjective`, `EvalChecksInjective`,
  `InitCallFrameUniqueResult`, `CallEntryUniqueResult`, and
  `CallExitUniqueResult`: deterministic expression/check lists and store-update
  relations uniquely determine call frames, caller result stores, and aggregate
  failure flags.
- `CoreBodyExec.empty_unique` / `CoreBodyExecE.empty_unique`, the singleton
  command inversion/uniqueness theorems, and
  `EvalCommand.call_unique_of_body_unique` /
  `EvalCommandE.call_unique_of_body_unique` compose body determinism into a
  unique caller store together with its failure flag or chronological trace.
  `EvalCommandContract.call_unique_of_outputs_nil` and its event counterpart give the corresponding
  full-result guarantee when contract abstraction has no outputs to havoc.
- `evalCommand_storeWellDefined`: a command leaves a store that holds only values,
  given that it started from one.
- `assertBodyE_preserves_store` and `setBodyE_frame`: one-command procedure
  bodies establish exact store preservation or an output write frame.
- Event-trace store-domain results:
  `evalCommandE_preserves_none_of_not_def`, `evalCommandE_preserves_isSome`,
  `evalCommandE_storeWellDefined`, `core_stmts_preserves_isSomeE`,
  `core_stmt_run_terminal_preserves_none_of_not_definedVars_trueE`, and
  `core_stmt_run_terminal_store_isSome_eqE` provide the corresponding
  guarantees for `EvalCommandE` / `StepStmtStarE` runs.
- `CoreStepStar_to_StepStmtStar` / `StepStmtStar_to_CoreStepStar`: the Core
  failure-flag closure is a separate mutual inductive, so results over the
  generic closure transfer only through these theorems. `CoreStepStarE` directly
  reuses the generic `ReflTransTrace` closure.
-/

namespace Core
open Imperative

/-- Initializing distinct store slots with values preserves store well-formedness. -/
theorem initStates_preserves_wf {P : PureExpr} [HasVal P] {fac : P.Factory} :
    ∀ {ids : List P.Ident} {vals : List P.Expr} {σ σ' : SemanticStore P},
      InitStates σ ids vals σ' →
      WellFormedStore σ fac →
      (∀ v ∈ vals, HasVal.value fac v) →
      WellFormedStore σ' fac := by
  intro ids vals σ σ' h
  induction h with
  | init_none => intro hσ _; exact hσ
  | @init_some σ0 x v σ1 xs vs σ2 hinit hrest ih =>
    intro hσ hvals
    refine ih ?_ (fun w hw => hvals w (List.mem_cons_of_mem _ hw))
    intro w vw hw
    cases hinit with
    | init _hxnone hxv hxoth =>
      by_cases hwx : w = x
      · subst hwx
        rw [hxv] at hw
        obtain rfl := Option.some.inj hw
        exact hvals _ List.mem_cons_self
      · rw [hxoth w (Ne.symm hwx)] at hw
        exact hσ w vw hw

/-- Adding `old` snapshots only copies existing bindings, so it preserves store
well-formedness. -/
theorem withOldSnapshots_preserves_wf {fac : Expression.Factory}
    (snap : List Expression.Ident) (σ : CoreStore)
    (hσ : WellFormedStore σ fac) :
    WellFormedStore (withOldSnapshots snap σ) fac := by
  intro w vw hw
  simp only [withOldSnapshots] at hw
  split at hw
  · exact hσ _ _ hw
  · exact hσ _ _ hw

theorem InitStatesEmpty :
  @InitStates P σ [] [] σ' → σ = σ' := by
  intros H; cases H <;> simp

theorem UpdateStatesEmpty :
  @UpdateStates P σ [] [] σ' → σ = σ' := by
  intros H; cases H <;> simp

theorem HavocVarsEmpty {P : PureExpr} [HasVal P] {f : P.Factory} {σ σ' : SemanticStore P} :
  HavocVars f σ [] σ' → σ = σ' := by
  intros H; cases H <;> simp

theorem InitVarsEmpty :
  @InitVars P σ [] σ' → σ = σ' := by
  intros H; cases H <;> simp

theorem TouchVarsEmpty :
  @TouchVars P σ [] σ' → σ = σ' := by
  intros H; cases H <;> simp

theorem EvalBlockEmpty' {P : PureExpr} {Cmd : Type} {EvalCmd : EvalCmdParam P Cmd}
  {extendFactory : ExtendFactory P}
  { ρ ρ' : Env P }
  [HasBool P] [HasBoolOps P] [HasFvars P] [HasInt P] [HasIntOps P] :
  EvalStmtsSmall P EvalCmd extendFactory ρ ([]: (List (Stmt P Cmd))) ρ' → ρ = ρ' := by
  intro H
  match H with
  | .step _ _ _ .step_stmts_nil (.refl _) => rfl

theorem EvalStatementsEmpty :
  EvalStatements π φ ρ [] ρ' → ρ = ρ' := by
  intro H
  unfold EvalStatements EvalStmtsSmall at H
  match H with
  | .step _ _ _ .step_stmts_nil (.refl _) => rfl

theorem EvalStatementsContractEmpty :
  EvalStatementsContract π φ ρ [] ρ' → ρ = ρ' := by
  intro H
  unfold EvalStatementsContract EvalStmtsSmall at H
  match H with
  | .step _ _ _ .step_stmts_nil (.refl _) => rfl

theorem UpdateStateNotDefMonotone
  {P : PureExpr} {σ σ' : SemanticStore P}
  {vs : List P.Ident} {e : P.Expr} {v : P.Ident} :
  isNotDefined σ vs →
  UpdateState P σ v e σ' →
  isNotDefined σ' vs := by
  intros Hdef Heval
  cases Heval with
  | update Hold HH Hsome =>
  simp [isNotDefined] at *
  intros v' Hv'
  by_cases Heq: (v = v')
  case pos =>
    simp_all
  case neg =>
    specialize Hsome v' Heq
    specialize Hdef v'
    simp [Hsome]
    exact Hdef Hv'

theorem UpdateStatesNotDefMonotone
  {P : PureExpr} {σ σ' : SemanticStore P}
  {vs : List P.Ident} {es' : List P.Expr} {vs' : List P.Ident} :
  isNotDefined σ vs →
  UpdateStates σ vs' es' σ' →
  isNotDefined σ' vs := by
  intros Hdef Heval
  induction Heval with
  | update_none => assumption
  | update_some Hup Hups ih =>
  intros v Hv
  apply ih
  exact UpdateStateNotDefMonotone Hdef Hup
  assumption

theorem UpdateStateNotDefMonotone'
  {P : PureExpr} {σ σ' : SemanticStore P}
  {vs : List P.Ident} {e : P.Expr} {v : P.Ident} :
  isNotDefined σ' vs →
  UpdateState P σ v e σ' →
  isNotDefined σ vs := by
  intros Hdef Heval
  cases Heval with
  | update Hold HH Hsome =>
  simp [isNotDefined] at *
  intros v' Hv'
  by_cases Heq: (v = v')
  case pos =>
    simp_all
  case neg =>
    specialize Hsome v' Heq
    specialize Hdef v'
    simp [← Hsome]
    exact Hdef Hv'

theorem UpdateStatesNotDefMonotone'
  {P : PureExpr} {σ σ' : SemanticStore P}
  {vs : List P.Ident} {es' : List P.Expr} {vs' : List P.Ident} :
  isNotDefined σ' vs →
  UpdateStates σ vs' es' σ' →
  isNotDefined σ vs := by
  intros Hdef Heval
  induction Heval with
  | update_none => assumption
  | update_some Hup Hups ih =>
  intros v Hv
  apply UpdateStateNotDefMonotone' (ih Hdef) Hup
  exact Hv

theorem InitStateDefined
  {P : PureExpr} {σ σ' : SemanticStore P} {e : P.Expr} {v : P.Ident} :
  @InitState P σ v e σ' →
  isDefined σ' [v] := by
  intros Hup
  cases Hup with
  | init Hold Hsome Hall =>
  simp [isDefined, Option.isSome, Hsome]

theorem UpdateStateDefined
  {P : PureExpr} {σ σ' : SemanticStore P} {e : P.Expr} {v : P.Ident} :
  @UpdateState P σ v e σ' →
  isDefined σ' [v] := by
  intros Hup
  cases Hup with
  | update Hold Hsome Hall =>
  simp [isDefined, Option.isSome, Hsome]

theorem UpdateStateDefined'
  {P : PureExpr} {σ σ' : SemanticStore P} {e : P.Expr} {v : P.Ident} :
  @UpdateState P σ v e σ' →
  isDefined σ [v] := by
  intros Hup
  cases Hup with
  | update Hold Hsome Hall =>
  simp [isDefined, Option.isSome]
  split <;> simp_all

theorem UpdateStateDefMonotone
  {P : PureExpr} {σ σ' : SemanticStore P}
  {vs : List P.Ident} {e : P.Expr} {v : P.Ident} :
  isDefined σ vs →
  UpdateState P σ v e σ' →
  isDefined σ' vs := by
  intros Hdef Heval
  cases Heval with
  | update Hold HH Hsome =>
  simp [isDefined] at *
  intros v' Hv'
  by_cases Heq: (v = v')
  case pos =>
    simp [Option.isSome]
    simp [Heq] at *
    split <;> simp_all
  case neg =>
    specialize Hsome v' Heq
    specialize Hdef v'
    simp [Hsome]
    exact Hdef Hv'

theorem UpdateStatesDefMonotone
  {P : PureExpr} {σ σ' : SemanticStore P}
  {vs : List P.Ident} {es' : List P.Expr} {vs' : List P.Ident} :
  isDefined σ vs →
  UpdateStates σ vs' es' σ' →
  isDefined σ' vs := by
  intros Hdef Heval
  induction Heval with
  | update_none => assumption
  | update_some Hup Hups ih =>
  intros v Hv
  apply ih
  exact UpdateStateDefMonotone Hdef Hup
  assumption

theorem UpdateStateDefMonotone'
  {P : PureExpr} {σ σ' : SemanticStore P}
  {vs : List P.Ident} {e : P.Expr} {v : P.Ident} :
  isDefined σ' vs →
  UpdateState P σ v e σ' →
  isDefined σ vs := by
  intros Hdef Heval
  cases Heval with
  | update Hold HH Hsome =>
  simp [isDefined] at *
  intros v' Hv'
  by_cases Heq: (v = v')
  case pos =>
    simp [Option.isSome]
    simp [Heq] at *
    split <;> simp_all
  case neg =>
    specialize Hsome v' Heq
    specialize Hdef v'
    simp [← Hsome]
    exact Hdef Hv'

theorem UpdateStatesDefMonotone'
  {P : PureExpr} {σ σ' : SemanticStore P}
  {vs : List P.Ident} {es' : List P.Expr} {vs' : List P.Ident} :
  isDefined σ' vs →
  UpdateStates σ vs' es' σ' →
  isDefined σ vs := by
  intros Hdef Heval
  induction Heval with
  | update_none => assumption
  | update_some Hup Hups ih =>
  intros v Hv
  apply UpdateStateDefMonotone' (ih Hdef) Hup
  exact Hv

theorem UpdateStatesDefined :
  UpdateStates σ vs es σ' →
  isDefined σ' vs := by
  intros Hhavoc
  induction vs generalizing es σ σ'
  case nil => simp [isDefined]
  case cons h t ih =>
    cases Hhavoc with
    | @update_some _ _ v σ₁ _ _ Hup Hhav =>
    apply isDefinedCons
    apply UpdateStatesDefMonotone <;> try assumption
    exact UpdateStateDefined Hhav
    apply ih <;> assumption

theorem UpdateStatesDefined' :
  UpdateStates σ vs es σ' →
  isDefined σ vs := by
  intros Hhavoc
  induction vs generalizing es σ σ'
  case nil => simp [isDefined]
  case cons h t ih =>
    cases Hhavoc with
    | update_some Hup Hups =>
    apply isDefinedCons
    exact UpdateStateDefined' Hup
    apply UpdateStatesDefMonotone'
    apply ih Hups
    exact UpdateStates.update_some Hup UpdateStates.update_none

theorem updatedStateUpdate {P : PureExpr}
  {σ : SemanticStore P} {h : P.Ident} {v v' : P.Expr} :
  σ h = some v' →
  UpdateState P σ h v (@updatedState P σ h v) := by
  intros Hsome
  constructor <;> try simp [updatedState]
  assumption
  intros v Hneq Heq; simp_all

theorem updatedStateId {P : PureExpr}
  {σ : SemanticStore P} {h : P.Ident} {v : P.Expr} :
  σ h = some v →
  @updatedState P σ h v = σ := by
  intros Hsome
  funext x
  simp_all [updatedState]

theorem updatedStateDefMonotone :
  isDefined σ vs →
  isDefined (updatedState σ v' e') vs := by
  intros Hdef
  induction vs
  case nil => simp [isDefined]
  case cons h t ih =>
    simp [isDefined] at *
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
  {vs : List P.Ident} {ves : List (P.Ident × P.Expr)} :
  isDefined σ vs →
  isDefined (updatedStates' σ ves) vs := by
  intros Hdef
  induction ves generalizing σ <;>
  unfold updatedStates' <;> try simp_all
  case cons h t ih =>
    simp [isDefined]
    intros v Hin
    apply ih
    exact updatedStateDefMonotone Hdef
    assumption

  theorem updatedStatesDefined :
  ks.length = vs.length →
  isDefined (updatedStates σ ks vs) ks := by
    intros Hlen k Hin
    induction ks generalizing σ vs <;> simp_all
    case cons h t ih =>
    simp [updatedStates] at *
    cases vs <;> simp at Hlen
    case cons h' t' =>
    cases Hin with
    | inl Hin =>
      simp [updatedStates']
      have Hdef : isDefined (updatedStates' (updatedState σ h h') (t.zip t')) [h] := by
        apply updatedStatesDefMonotone
        simp [isDefined, updatedState]
      simp_all [isDefined]
    | inr Hin =>
      apply ih <;> assumption
  
theorem updatedStatesUpdate {P : PureExpr}
  {σ : SemanticStore P} {hs : List P.Ident} {vs : List P.Expr} :
  hs.length = vs.length →
  isDefined σ hs →
  UpdateStates σ hs vs (updatedStates σ hs vs) := by
  intros Hlen Hdef
  induction hs generalizing vs σ
  case nil =>
    simp_all
    have Hemp : vs = [] := by
      exact List.length_eq_zero_iff.mp (id (Eq.symm Hlen))
    simp [Hemp, updatedStates]
    exact UpdateStates.update_none
  case cons h t ih =>
    induction vs <;> simp_all
    case cons h' t' =>
    simp [isDefined] at Hdef
    have Hlkup := Hdef.1
    simp [Option.isSome] at Hlkup
    split at Hlkup <;> simp_all
    next x val heq =>
    apply UpdateStates.update_some (updatedStateUpdate heq)
    exact ih rfl (updatedStateDefMonotone Hdef)

theorem updatedStateInit {P : PureExpr}
  {σ : SemanticStore P} {h : P.Ident} {v : P.Expr} :
  σ h = none →
  InitState P σ h v (@updatedState P σ h v) := by
  intros Hsome
  constructor <;> try simp [updatedState]
  assumption
  intros v Hneq Heq; simp_all

theorem updatedStatesInit {P : PureExpr}
  {σ : SemanticStore P} {hs : List P.Ident} {vs : List P.Expr} :
  hs.length = vs.length →
  isNotDefined σ hs →
  hs.Nodup →
  InitStates σ hs vs (updatedStates σ hs vs) := by
  intros Hlen Hdef Hnd
  induction hs generalizing vs σ
  case nil =>
    simp_all
    have Hemp : vs = [] := by
      exact List.length_eq_zero_iff.mp (id (Eq.symm Hlen))
    simp [Hemp, updatedStates]
    exact InitStates.init_none
  case cons h t ih =>
    induction vs <;> simp_all
    case cons h' t' =>
    simp [isNotDefined] at Hdef
    have Hlkup := Hdef.1
    apply InitStates.init_some (updatedStateInit Hlkup)
    apply ih rfl
    simp [isNotDefined, updatedState]
    intros v Hin
    simp_all
    exact ne_of_mem_of_not_mem Hin Hnd.1

/-- use the zipped version to avoid needing to prove length equivalent -/
theorem updatedStates'App :
  updatedStates' σ (a ++ b) =
  updatedStates' (updatedStates' σ a) b := by
  induction a generalizing σ
  case nil =>
    simp [updatedStates']
  case cons h t ih =>
    simp [updatedStates']
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

theorem InitStatesNotDefined :
  InitStates σ hs vs σ' → isNotDefined σ hs := by
  intros Hinit
  induction Hinit <;> simp [isNotDefined]
  case init_some x v σ' xs vs σ'' Hinit Hinits ih =>
    simp [isNotDefined] at *
    cases Hinit with
    | init Hnone Hsome Heq =>
    refine ⟨Hnone, ?_⟩
    intros x' Hin
    by_cases Heqx : x = x' <;> simp_all
    specialize Heq x' Heqx
    specialize ih x' Hin
    simp_all

theorem InitStatesNodup :
  InitStates σ hs vs σ' → hs.Nodup := by
  intros Hinit
  induction Hinit <;> simp_all
  case init_some x v σ' xs vs σ'' Hinit Hinits ih =>
  apply Not.intro
  intros Hin
  cases Hinit with
  | init Hnone Hsome Heq =>
    have Hnd := InitStatesNotDefined Hinits
    specialize Hnd x Hin
    simp_all

theorem InitStateInjective :
  InitState P σ k1 k2 σ' →
  InitState P σ k1 k2 σ'' →
  σ' = σ'' := by
  intros Hinit1 Hinit2
  cases Hinit1
  case init Hnone1 Heq1 Hsome1 =>
  cases Hinit2
  case init Hnone2 Heq2 Hsome2 =>
  funext x
  by_cases H : k1 = x
  . simp_all
  . rw [Heq1, Heq2] <;> simp_all

theorem InitStatesInjective :
  InitStates σ k1 k2 σ' →
  InitStates σ k1 k2 σ'' →
  σ' = σ'' := by
  intros Hinit1 Hinit2
  induction Hinit1 generalizing σ''
  case init_none =>
    have Heq := InitStatesEmpty Hinit2
    simp_all
  case init_some Hinit Hinits ih =>
    cases Hinit2 with
    | init_some Hinit2 Hinits2 =>
    apply ih
    have Hinj := InitStateInjective Hinit Hinit2
    simp_all
/-- Every expression returned by `ReadValues` is a value in its factory. -/
private theorem ReadValues.all_values
    {P : PureExpr} [HasVal P] {f : P.Factory} {σ : SemanticStore P}
    {ks : List P.Ident} {vs : List P.Expr} (h : ReadValues f σ ks vs) :
    ∀ v ∈ vs, HasVal.value f v := by
  induction h with
  | read_none => simp
  | read_some _ hval _ ih =>
    intro v hv
    cases hv with
    | head => exact hval
    | tail _ hmem => exact ih v hmem


/-- Reading the same keys from the same store yields the same value list. -/
theorem ReadValuesInjective {P : PureExpr} [HasVal P] {f : P.Factory}
  {σ : SemanticStore P} {ks : List P.Ident} {vs vs' : List P.Expr} :
  ReadValues f σ ks vs →
  ReadValues f σ ks vs' →
  vs = vs' := by
  intros Hrd1 Hrd2
  induction Hrd1 generalizing vs'
  case read_none =>
    cases Hrd2
    rfl
  case read_some Hrd Hrds ih =>
    cases Hrd2 with
    | read_some Hrd2 _ Hrds2 =>
    congr
    . simp_all
    . apply ih
      simp_all

/-- Evaluating the same expression list in the same factory and store yields the
same value list. -/
theorem EvalExpressionsInjective {f : Expression.Factory} {σ : CoreStore}
    {es vs vs' : List Expression.Expr} :
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


/-- Evaluating the same check list in the same factory and store yields the same
aggregate failure flag. -/
theorem EvalChecksInjective {fac : Expression.Factory} {σ : CoreStore}
    {es : List Expression.Expr} {failed₁ failed₂ : Bool}
    (h₁ : EvalChecks fac σ es failed₁) (h₂ : EvalChecks fac σ es failed₂) :
    failed₁ = failed₂ := by
  induction h₁ generalizing failed₂ with
  | eval_none => cases h₂; rfl
  | eval_pass _ heval _ ih =>
    cases h₂ with
    | eval_pass _ _ hrest => exact ih hrest
    | eval_fail _ heval' _ =>
      have hcontra := Option.some.inj (heval.symm.trans heval')
      change (Lambda.LExpr.boolConst () true : Expression.Expr) =
        Lambda.LExpr.boolConst () false at hcontra
      simp [Lambda.LExpr.boolConst] at hcontra
  | eval_fail _ heval _ _ =>
    cases h₂ with
    | eval_pass _ heval' _ =>
      have hcontra := Option.some.inj (heval.symm.trans heval')
      change (Lambda.LExpr.boolConst () false : Expression.Expr) =
        Lambda.LExpr.boolConst () true at hcontra
      simp [Lambda.LExpr.boolConst] at hcontra
    | eval_fail => rfl
theorem InitStateUpdated :
    InitState P σ' k v σ'' →
    σ'' = updatedState σ' k v := by
  intros Hinit
  cases Hinit with
  | init Hnone Hsome Heq =>
  funext x
  simp [updatedState]
  by_cases Hxk : x = k <;> simp_all
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
  simp [updatedState]
  by_cases Hxk : x = k <;> simp_all
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
theorem InitCallFrameUniqueResult {p : Procedure} {inputVals outOnlyVals : List Expression.Expr}
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
  rintro ⟨outputs₁, hRead₁, hUpdate₁⟩ ⟨outputs₂, hRead₂, hUpdate₂⟩
  have hOutputs : outputs₁ = outputs₂ := ReadValuesInjective hRead₁ hRead₂
  subst outputs₂
  exact (UpdateStatesUpdated hUpdate₁).trans (UpdateStatesUpdated hUpdate₂).symm

/-- A call with no left-hand-side arguments cannot change the caller store. -/
theorem CallExit.store_eq_of_getLhs_nil {fac : Expression.Factory} {σ : CoreStore}
    {p : Procedure} {callArgs : List (CallArg Expression)} {σEnd σ' : CoreStore}
    (hLhs : CallArg.getLhs callArgs = [])
    (h : CallExit fac σ p callArgs σEnd σ') : σ' = σ := by
  obtain ⟨outputs, _, hUpdate⟩ := h
  rw [hLhs] at hUpdate
  cases hUpdate
  rfl

/-- Executing a concrete call with no left-hand-side arguments leaves the caller
store unchanged. -/
theorem EvalCommand.store_eq_of_call_getLhs_nil
    {π : String → Option Procedure}
    {φ : Expression.Factory → PureFunc Expression → Expression.Factory}
    {fac : Expression.Factory} {σ σ' : CoreStore} {n : String}
    {callArgs : List (CallArg Expression)} {md : MetaData Expression} {failed : Bool}
    (hLhs : CallArg.getLhs callArgs = [])
    (h : EvalCommand π φ fac σ (.call n callArgs md) σ' failed) : σ' = σ := by
  cases h with
  | call_sem _ _ _ _ _ hExit => exact hExit.store_eq_of_getLhs_nil hLhs

/-- Executing an event-producing concrete call with no left-hand-side arguments
leaves the caller store unchanged. -/
theorem EvalCommandE.store_eq_of_call_getLhs_nil
    {π : String → Option Procedure}
    {φ : Expression.Factory → PureFunc Expression → Expression.Factory}
    {fac : Expression.Factory} {σ σ' : CoreStore} {n : String}
    {callArgs : List (CallArg Expression)} {md : MetaData Expression}
    {emitted : Trace Expression}
    (hLhs : CallArg.getLhs callArgs = [])
    (h : EvalCommandE π φ fac σ (.call n callArgs md) σ' emitted) : σ' = σ := by
  cases h with
  | call_sem _ _ _ hExit => exact hExit.store_eq_of_getLhs_nil hLhs

/-- Executing an abstract contract call with no left-hand-side arguments leaves
the caller store unchanged. -/
theorem EvalCommandContract.store_eq_of_call_getLhs_nil
    {π : String → Option Procedure} {fac : Expression.Factory} {σ σ' : CoreStore}
    {n : String} {callArgs : List (CallArg Expression)} {md : MetaData Expression}
    {failed : Bool}
    (hLhs : CallArg.getLhs callArgs = [])
    (h : EvalCommandContract π fac σ (.call n callArgs md) σ' failed) : σ' = σ := by
  cases h with
  | call_sem _ _ _ _ _ hExit => exact hExit.store_eq_of_getLhs_nil hLhs

/-- Executing an event-producing abstract contract call with no left-hand-side
arguments leaves the caller store unchanged. -/
theorem EvalCommandContractE.store_eq_of_call_getLhs_nil
    {π : String → Option Procedure} {fac : Expression.Factory} {σ σ' : CoreStore}
    {n : String} {callArgs : List (CallArg Expression)} {md : MetaData Expression}
    {emitted : Trace Expression}
    (hLhs : CallArg.getLhs callArgs = [])
    (h : EvalCommandContractE π fac σ (.call n callArgs md) σ' emitted) : σ' = σ := by
  cases h with
  | call_sem _ _ _ hExit => exact hExit.store_eq_of_getLhs_nil hLhs

/-- Abstract contract calls for a procedure with no outputs have a unique caller
store and failure result. -/
theorem EvalCommandContract.call_unique_of_outputs_nil
    {π : String → Option Procedure} {fac : Expression.Factory}
    {σ σ₁ σ₂ : CoreStore} {n : String} {p : Procedure}
    {callArgs : List (CallArg Expression)} {md : MetaData Expression}
    {failed₁ failed₂ : Bool}
    (hLookup : π n = some p) (hOutputs : ListMap.keys p.header.outputs = [])
    (h₁ : EvalCommandContract π fac σ (.call n callArgs md) σ₁ failed₁)
    (h₂ : EvalCommandContract π fac σ (.call n callArgs md) σ₂ failed₂) :
    σ₁ = σ₂ ∧ failed₁ = failed₂ := by
  cases h₁ with
  | @call_sem _ out₁ _ p₁ _ _ pre₁ _ _ frame₁
      lookup₁ entry₁ evalPre₁ havoc₁ _ exit₁ =>
    cases h₂ with
    | @call_sem _ out₂ _ p₂ _ _ pre₂ _ _ frame₂
        lookup₂ entry₂ evalPre₂ havoc₂ _ exit₂ =>
      have hp₁ : p₁ = p := Option.some.inj (lookup₁.symm.trans hLookup)
      have hp₂ : p₂ = p := Option.some.inj (lookup₂.symm.trans hLookup)
      subst p₁
      subst p₂
      have hframe : frame₁ = frame₂ := CallEntryUniqueResult entry₁ entry₂
      subst frame₂
      rw [hOutputs] at havoc₁ havoc₂
      cases havoc₁
      cases havoc₂
      exact ⟨CallExitUniqueResult exit₁ exit₂,
        EvalChecksInjective evalPre₁ evalPre₂⟩

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
      rw [hOutputs] at havoc₁ havoc₂
      cases havoc₁
      cases havoc₂
      exact ⟨CallExitUniqueResult exit₁ exit₂, rfl⟩

/-- An empty structured body uniquely preserves its input store and factory and
reports no failure. -/
theorem CoreBodyExec.empty_unique
    (π : String → Option Procedure)
    (φ : Expression.Factory → PureFunc Expression → Expression.Factory)
    (σ σ' : CoreStore) (fac fac' : Expression.Factory) (failed : Bool)
    (h : CoreBodyExec π φ (.structured []) σ fac σ' fac' failed) :
    σ' = σ ∧ fac' = fac ∧ failed = false := by
  cases h with
  | structured hstar =>
    cases hstar with
    | step hs1 hr1 =>
      cases hs1
      case step_block =>
        cases hr1 with
        | step hs2 hr2 =>
          cases hs2
          case step_block_body hinner =>
            cases hinner
            case step_stmts_nil =>
              cases hr2 with
              | step hs3 hr3 =>
                cases hs3
                case step_block_body hinner => cases hinner
                case step_block_done =>
                  cases hr3 with
                  | refl => simp [projectStore_self]
                  | step hs4 _ => cases hs4

/-- A singleton-command structured body exposes exactly the command result before
the procedure block projects its store and restores its factory. -/
theorem CoreBodyExec.singleton_cmd_invert
    {π : String → Option Procedure}
    {φ : Expression.Factory → PureFunc Expression → Expression.Factory}
    {fac fac' : Expression.Factory} {σ σ' : CoreStore}
    {cmd : Command} {failed : Bool}
    (h : CoreBodyExec π φ (.structured [.cmd cmd]) σ fac σ' fac' failed) :
    ∃ σCmd, EvalCommand π φ fac σ cmd σCmd failed ∧
      σ' = projectStore σ σCmd ∧ fac' = fac := by
  cases h with
  | structured hstar =>
    cases hstar with
    | step hs1 hr1 =>
      cases hs1
      case step_block =>
        cases hr1 with
        | step hs2 hr2 =>
          cases hs2
          case step_block_body hinner2 =>
            cases hinner2
            case step_stmts_cons =>
              cases hr2 with
              | step hs3 hr3 =>
                cases hs3
                case step_block_body hinner3 =>
                  cases hinner3
                  case step_seq_inner hcmdStep =>
                    cases hcmdStep
                    case step_cmd hcmd =>
                      cases hr3 with
                      | step hs4 hr4 =>
                        cases hs4
                        case step_block_body hinner4 =>
                          cases hinner4
                          case step_seq_inner hterminal =>
                            exact (terminalIsTerminal Expression (EvalCommand π φ)
                              (EvalPureFunc φ) _ _ hterminal).elim
                          case step_seq_done =>
                            cases hr4 with
                            | step hs5 hr5 =>
                              cases hs5
                              case step_block_body hinner5 =>
                                cases hinner5
                                case step_stmts_nil =>
                                  cases hr5 with
                                  | step hs6 hr6 =>
                                    cases hs6
                                    case step_block_body hterminal =>
                                      exact (terminalIsTerminal Expression (EvalCommand π φ)
                                        (EvalPureFunc φ) _ _ hterminal).elim
                                    case step_block_done =>
                                      cases hr6 with
                                      | refl => exact ⟨_, hcmd, rfl, rfl⟩
                                      | step hs7 _ =>
                                        exact (terminalIsTerminal Expression (EvalCommand π φ)
                                          (EvalPureFunc φ) _ _ hs7).elim
/-- A terminal configuration cannot take an event-producing statement step. -/
private theorem no_stepE_from_terminal
    (π : String → Option Procedure)
    (φ : Expression.Factory → PureFunc Expression → Expression.Factory)
    (ρ : Env Expression) (emitted : Trace Expression) (c : Config Expression Command)
    (h : StepStmtE Expression (EvalCommandE π φ) (EvalPureFunc φ)
      (.terminal ρ) emitted c) : False := by
  cases h with
  | step_admin hadmin => cases hadmin

/-- Invert an event step from a command statement into its command result. -/
private theorem stepE_stmt_cmd_inv
    {π : String → Option Procedure}
    {φ : Expression.Factory → PureFunc Expression → Expression.Factory}
    {cmd : Command} {ρ : Env Expression} {e : Trace Expression}
    {c' : Config Expression Command}
    (h : CoreStepE π φ (.stmt (.cmd cmd) ρ) e c') :
    ∃ σ', EvalCommandE π φ ρ.factory ρ.store cmd σ' e ∧
      c' = .terminal { ρ with store := σ' } := by
  cases h with
  | step_cmd hcmd => exact ⟨_, hcmd, rfl⟩
  | step_admin hadmin =>
    cases hadmin with
    | step_cmd hf => exact hf.elim

/-- Invert an event step from a statement-list configuration. -/
private theorem stepE_stmts_inv
    {π : String → Option Procedure}
    {φ : Expression.Factory → PureFunc Expression → Expression.Factory}
    {ss : List (Stmt Expression Command)} {ρ : Env Expression}
    {e : Trace Expression} {c' : Config Expression Command}
    (h : CoreStepE π φ (.stmts ss ρ) e c') :
    (ss = [] ∧ e = [] ∧ c' = .terminal ρ) ∨
      (∃ s ss', ss = s :: ss' ∧ e = [] ∧ c' = .seq (.stmt s ρ) ss') := by
  cases h with
  | step_admin hadmin =>
    cases hadmin with
    | step_stmts_nil => exact .inl ⟨rfl, rfl, rfl⟩
    | step_stmts_cons => exact .inr ⟨_, _, rfl, rfl, rfl⟩

/-- Invert an event step from a sequence, identifying an inner step or one of
its two administrative exits. -/
private theorem stepE_seq_inv
    {π : String → Option Procedure}
    {φ : Expression.Factory → PureFunc Expression → Expression.Factory}
    {inner : Config Expression Command} {ss : List (Stmt Expression Command)}
    {e : Trace Expression} {c' : Config Expression Command}
    (h : CoreStepE π φ (.seq inner ss) e c') :
    (∃ inner', CoreStepE π φ inner e inner' ∧ c' = .seq inner' ss) ∨
      (∃ ρ₁ : Env Expression,
        inner = .terminal ρ₁ ∧ e = [] ∧ c' = .stmts ss ρ₁) ∨
      (∃ (l : String) (ρ₁ : Env Expression),
        inner = .exiting l ρ₁ ∧ e = [] ∧ c' = .exiting l ρ₁) := by
  cases h with
  | step_admin hadmin =>
    cases hadmin with
    | step_seq_inner hstep => exact .inl ⟨_, .step_admin hstep, rfl⟩
    | step_seq_done => exact .inr (.inl ⟨_, rfl, rfl, rfl⟩)
    | step_seq_exit => exact .inr (.inr ⟨_, _, rfl, rfl, rfl⟩)
  | step_seq_inner hE => exact .inl ⟨_, hE, rfl⟩

/-- Invert an event step from a block, merging the direct and administratively
wrapped forms of inner steps. -/
private theorem stepE_block_inv
    {π : String → Option Procedure}
    {φ : Expression.Factory → PureFunc Expression → Expression.Factory}
    {label : Option String} {σp : SemanticStore Expression}
    {fp : Expression.Factory} {inner : Config Expression Command}
    {e : Trace Expression} {c' : Config Expression Command}
    (h : CoreStepE π φ (.block label σp fp inner) e c') :
    (∃ inner', CoreStepE π φ inner e inner' ∧
      c' = .block label σp fp inner') ∨
    (∃ ρ₁ : Env Expression, inner = .terminal ρ₁ ∧ e = [] ∧
      c' = .terminal { ρ₁ with store := projectStore σp ρ₁.store, factory := fp }) ∨
    (∃ (l : String) (ρ₁ : Env Expression),
      inner = .exiting l ρ₁ ∧ label = some l ∧ e = [] ∧
      c' = .terminal { ρ₁ with store := projectStore σp ρ₁.store, factory := fp }) ∨
    (∃ (l : String) (ρ₁ : Env Expression),
      inner = .exiting l ρ₁ ∧ label ≠ some l ∧ e = [] ∧
      c' = .exiting l
        { ρ₁ with store := projectStore σp ρ₁.store, factory := fp }) := by
  cases h with
  | step_admin hadmin =>
    cases hadmin with
    | step_block_body hstep => exact .inl ⟨_, .step_admin hstep, rfl⟩
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
    {φ : Expression.Factory → PureFunc Expression → Expression.Factory}
    {fac fac' : Expression.Factory} {σ σ' : CoreStore}
    {cmd : Command} {emitted : Trace Expression}
    (h : CoreBodyExecE π φ (.structured [.cmd cmd]) σ fac σ' fac' emitted) :
    ∃ σCmd, EvalCommandE π φ fac σ cmd σCmd emitted ∧
      σ' = projectStore σ σCmd ∧ fac' = fac := by
  cases h with
  | structured hstar =>
    cases hstar with
    | step _ _ _ _ _ hs1 hr1 =>
      cases hs1 with
      | step_admin hadmin1 =>
        cases hadmin1 with
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
                          · exact (no_stepE_from_terminal π φ _ _ _ hseq4).elim
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
                                    · exact (no_stepE_from_terminal π φ _ _ _ hin6).elim
                                    · injection he6 with he6
                                      subst he6
                                      cases hr6 with
                                      | refl => exact ⟨σCmd, by simpa using hcmd, rfl, rfl⟩
                                      | step _ _ _ _ _ hs7 _ =>
                                        exact (no_stepE_from_terminal π φ _ _ _ hs7).elim
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

/-- A concrete call has a unique store and failure result when every execution
of its selected body has a unique store, factory, and failure result. -/
theorem EvalCommand.call_unique_of_body_unique
    {π : String → Option Procedure}
    {φ : Expression.Factory → PureFunc Expression → Expression.Factory}
    {fac : Expression.Factory} {σ σ₁ σ₂ : CoreStore}
    {n : String} {p : Procedure} {callArgs : List (CallArg Expression)}
    {md : MetaData Expression} {failed₁ failed₂ : Bool}
    (hLookup : π n = some p)
    (hBodyUnique : ∀ {frame end₁ end₂ : CoreStore}
      {endFac₁ endFac₂ : Expression.Factory} {bodyFailed₁ bodyFailed₂ : Bool},
      CoreBodyExec π φ p.body frame fac end₁ endFac₁ bodyFailed₁ →
      CoreBodyExec π φ p.body frame fac end₂ endFac₂ bodyFailed₂ →
      end₁ = end₂ ∧ endFac₁ = endFac₂ ∧ bodyFailed₁ = bodyFailed₂)
    (h₁ : EvalCommand π φ fac σ (.call n callArgs md) σ₁ failed₁)
    (h₂ : EvalCommand π φ fac σ (.call n callArgs md) σ₂ failed₂) :
    σ₁ = σ₂ ∧ failed₁ = failed₂ := by
  cases h₁ with
  | @call_sem _ _ p₁ _ _ end₁ endFac₁ bodyFailed₁ preFailed₁ postFailed₁ _ _ frame₁
      lookup₁ entry₁ evalPre₁ bodyExec₁ evalPost₁ exit₁ =>
    cases h₂ with
    | @call_sem _ _ p₂ _ _ end₂ endFac₂ bodyFailed₂ preFailed₂ postFailed₂ _ _ frame₂
        lookup₂ entry₂ evalPre₂ bodyExec₂ evalPost₂ exit₂ =>
      have hp₁ : p₁ = p := Option.some.inj (lookup₁.symm.trans hLookup)
      have hp₂ : p₂ = p := Option.some.inj (lookup₂.symm.trans hLookup)
      subst p₁
      subst p₂
      have hframe : frame₁ = frame₂ := CallEntryUniqueResult entry₁ entry₂
      subst frame₂
      obtain ⟨hend, hfac, hbody⟩ := hBodyUnique bodyExec₁ bodyExec₂
      subst end₂
      subst endFac₂
      subst bodyFailed₂
      have hpre : preFailed₁ = preFailed₂ := EvalChecksInjective evalPre₁ evalPre₂
      have hpost : postFailed₁ = postFailed₂ := EvalChecksInjective evalPost₁ evalPost₂
      subst preFailed₂
      subst postFailed₂
      exact ⟨CallExitUniqueResult exit₁ exit₂, rfl⟩

/-- A singleton-command body has a unique store, factory, and failure result when
that command has a unique store and failure result. -/
theorem CoreBodyExec.singleton_cmd_unique
    {π : String → Option Procedure}
    {φ : Expression.Factory → PureFunc Expression → Expression.Factory}
    {fac : Expression.Factory} {σ end₁ end₂ : CoreStore}
    {cmd : Command} {endFac₁ endFac₂ : Expression.Factory}
    {failed₁ failed₂ : Bool}
    (hCmdUnique : ∀ {σ₁ σ₂ : CoreStore} {result₁ result₂ : Bool},
      EvalCommand π φ fac σ cmd σ₁ result₁ →
      EvalCommand π φ fac σ cmd σ₂ result₂ →
      σ₁ = σ₂ ∧ result₁ = result₂)
    (h₁ : CoreBodyExec π φ (.structured [.cmd cmd]) σ fac end₁ endFac₁ failed₁)
    (h₂ : CoreBodyExec π φ (.structured [.cmd cmd]) σ fac end₂ endFac₂ failed₂) :
    end₁ = end₂ ∧ endFac₁ = endFac₂ ∧ failed₁ = failed₂ := by
  obtain ⟨σCmd₁, hcmd₁, hend₁, hfac₁⟩ := h₁.singleton_cmd_invert
  obtain ⟨σCmd₂, hcmd₂, hend₂, hfac₂⟩ := h₂.singleton_cmd_invert
  obtain ⟨hcmdStore, hresult⟩ := hCmdUnique hcmd₁ hcmd₂
  subst σCmd₂
  exact ⟨hend₁.trans hend₂.symm, hfac₁.trans hfac₂.symm, hresult⟩

/-- An event-producing call has a unique store and trace when every execution of
its selected body has a unique store, factory, and trace. -/
theorem EvalCommandE.call_unique_of_body_unique
    {π : String → Option Procedure}
    {φ : Expression.Factory → PureFunc Expression → Expression.Factory}
    {fac : Expression.Factory} {σ σ₁ σ₂ : CoreStore}
    {n : String} {p : Procedure} {callArgs : List (CallArg Expression)}
    {md : MetaData Expression} {emitted₁ emitted₂ : Trace Expression}
    (hLookup : π n = some p)
    (hBodyUnique : ∀ {frame end₁ end₂ : CoreStore}
      {endFac₁ endFac₂ : Expression.Factory} {bodyEvents₁ bodyEvents₂ : Trace Expression},
      CoreBodyExecE π φ p.body frame fac end₁ endFac₁ bodyEvents₁ →
      CoreBodyExecE π φ p.body frame fac end₂ endFac₂ bodyEvents₂ →
      end₁ = end₂ ∧ endFac₁ = endFac₂ ∧ bodyEvents₁ = bodyEvents₂)
    (h₁ : EvalCommandE π φ fac σ (.call n callArgs md) σ₁ emitted₁)
    (h₂ : EvalCommandE π φ fac σ (.call n callArgs md) σ₂ emitted₂) :
    σ₁ = σ₂ ∧ emitted₁ = emitted₂ := by
  cases h₁ with
  | @call_sem _ _ p₁ _ _ end₁ endFac₁ bodyEvents₁ _ _ frame₁
      lookup₁ entry₁ bodyExec₁ exit₁ =>
    cases h₂ with
    | @call_sem _ _ p₂ _ _ end₂ endFac₂ bodyEvents₂ _ _ frame₂
        lookup₂ entry₂ bodyExec₂ exit₂ =>
      have hp₁ : p₁ = p := Option.some.inj (lookup₁.symm.trans hLookup)
      have hp₂ : p₂ = p := Option.some.inj (lookup₂.symm.trans hLookup)
      subst p₁
      subst p₂
      have hframe : frame₁ = frame₂ := CallEntryUniqueResult entry₁ entry₂
      subst frame₂
      obtain ⟨hend, hfac, hbody⟩ := hBodyUnique bodyExec₁ bodyExec₂
      subst end₂
      subst endFac₂
      subst bodyEvents₂
      exact ⟨CallExitUniqueResult exit₁ exit₂, rfl⟩

/-- A singleton-command event body has a unique store, factory, and trace when
that command has a unique store and trace. -/
theorem CoreBodyExecE.singleton_cmd_unique
    {π : String → Option Procedure}
    {φ : Expression.Factory → PureFunc Expression → Expression.Factory}
    {fac : Expression.Factory} {σ end₁ end₂ : CoreStore}
    {cmd : Command} {endFac₁ endFac₂ : Expression.Factory}
    {emitted₁ emitted₂ : Trace Expression}
    (hCmdUnique : ∀ {σ₁ σ₂ : CoreStore} {result₁ result₂ : Trace Expression},
      EvalCommandE π φ fac σ cmd σ₁ result₁ →
      EvalCommandE π φ fac σ cmd σ₂ result₂ →
      σ₁ = σ₂ ∧ result₁ = result₂)
    (h₁ : CoreBodyExecE π φ (.structured [.cmd cmd]) σ fac end₁ endFac₁ emitted₁)
    (h₂ : CoreBodyExecE π φ (.structured [.cmd cmd]) σ fac end₂ endFac₂ emitted₂) :
    end₁ = end₂ ∧ endFac₁ = endFac₂ ∧ emitted₁ = emitted₂ := by
  obtain ⟨σCmd₁, hcmd₁, hend₁, hfac₁⟩ := h₁.singleton_cmd_invert
  obtain ⟨σCmd₂, hcmd₂, hend₂, hfac₂⟩ := h₂.singleton_cmd_invert
  obtain ⟨hcmdStore, hresult⟩ := hCmdUnique hcmd₁ hcmd₂
  subst σCmd₂
  exact ⟨hend₁.trans hend₂.symm, hfac₁.trans hfac₂.symm, hresult⟩

/-- A fixed assertion command has a unique output store and failure result. -/
theorem EvalCommand.assert_unique
    {π : String → Option Procedure}
    {φ : Expression.Factory → PureFunc Expression → Expression.Factory}
    {fac : Expression.Factory} {σ σ₁ σ₂ : CoreStore}
    {label : String} {e : Expression.Expr} {md : MetaData Expression}
    {failed₁ failed₂ : Bool}
    (h₁ : EvalCommand π φ fac σ (.cmd (.assert label e md)) σ₁ failed₁)
    (h₂ : EvalCommand π φ fac σ (.cmd (.assert label e md)) σ₂ failed₂) :
    σ₁ = σ₂ ∧ failed₁ = failed₂ := by
  cases h₁ with
  | cmd_sem cmd₁ =>
    cases h₂ with
    | cmd_sem cmd₂ =>
      cases cmd₁ with
      | eval_assert_pass heval₁ _ =>
        cases cmd₂ with
        | eval_assert_pass => exact ⟨rfl, rfl⟩
        | eval_assert_fail heval₂ _ =>
          have hcontra := Option.some.inj (heval₁.symm.trans heval₂)
          change (Lambda.LExpr.boolConst () true : Expression.Expr) =
            Lambda.LExpr.boolConst () false at hcontra
          simp [Lambda.LExpr.boolConst] at hcontra
      | eval_assert_fail heval₁ _ =>
        cases cmd₂ with
        | eval_assert_pass heval₂ _ =>
          have hcontra := Option.some.inj (heval₁.symm.trans heval₂)
          change (Lambda.LExpr.boolConst () false : Expression.Expr) =
            Lambda.LExpr.boolConst () true at hcontra
          simp [Lambda.LExpr.boolConst] at hcontra
        | eval_assert_fail => exact ⟨rfl, rfl⟩

/-- A fixed event-producing assertion command has a unique output store and
single-event trace. -/
theorem EvalCommandE.assert_unique
    {π : String → Option Procedure}
    {φ : Expression.Factory → PureFunc Expression → Expression.Factory}
    {fac : Expression.Factory} {σ σ₁ σ₂ : CoreStore}
    {label : String} {e : Expression.Expr} {md : MetaData Expression}
    {emitted₁ emitted₂ : Trace Expression}
    (h₁ : EvalCommandE π φ fac σ (.cmd (.assert label e md)) σ₁ emitted₁)
    (h₂ : EvalCommandE π φ fac σ (.cmd (.assert label e md)) σ₂ emitted₂) :
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
    (φ : Expression.Factory → PureFunc Expression → Expression.Factory)
    (σ σ' : CoreStore) (fac fac' : Expression.Factory) (emitted : Trace Expression)
    (h : CoreBodyExecE π φ (.structured []) σ fac σ' fac' emitted) :
    σ' = σ ∧ fac' = fac ∧ emitted = [] := by
  cases h with
  | structured hstar =>
    cases hstar with
    | step _ _ _ _ _ hs1 hr1 =>
      cases hs1 with
      | step_admin hadmin =>
        cases hadmin
        case step_block =>
          cases hr1 with
          | step _ _ _ _ _ hs2 hr2 =>
            cases hs2 with
            | step_admin hadmin2 =>
              cases hadmin2
              case step_block_body hinner =>
                cases hinner
                case step_stmts_nil =>
                  cases hr2 with
                  | step _ _ _ _ _ hs3 hr3 =>
                    cases hs3 with
                    | step_admin hadmin3 =>
                      cases hadmin3
                      case step_block_body hinner => cases hinner
                      case step_block_done =>
                        cases hr3 with
                        | refl => simp [projectStore_self]
                        | step _ _ _ _ _ hs4 _ =>
                          exact (no_stepE_from_terminal π φ _ _ _ hs4).elim
                    | step_block_body hinner3 =>
                      exact (no_stepE_from_terminal π φ _ _ _ hinner3).elim
            | step_block_body hinnerE =>
              cases hinnerE with
              | step_admin hadmin2 =>
                cases hadmin2
                case step_stmts_nil =>
                  cases hr2 with
                  | step _ _ _ _ _ hs3 hr3 =>
                    cases hs3 with
                    | step_admin hadmin3 =>
                      cases hadmin3
                      case step_block_body hinner => cases hinner
                      case step_block_done =>
                        cases hr3 with
                        | refl => simp [projectStore_self]
                        | step _ _ _ _ _ hs4 _ =>
                          exact (no_stepE_from_terminal π φ _ _ _ hs4).elim
                    | step_block_body hinner3 =>
                      exact (no_stepE_from_terminal π φ _ _ _ hinner3).elim

/-- A concrete call to an empty body has the unique caller result obtained from
its uniquely determined entry frame and expected call exit. -/
theorem EvalCommand.empty_body_call_store_unique
    {π : String → Option Procedure}
    {φ : Expression.Factory → PureFunc Expression → Expression.Factory}
    {fac : Expression.Factory} {σ σAO expected σ' : CoreStore}
    {n : String} {p : Procedure} {callArgs : List (CallArg Expression)}
    {md : MetaData Expression} {failed : Bool}
    (hLookup : π n = some p) (hBody : p.body = .structured [])
    (hEntry : CallEntry fac σ p callArgs σAO)
    (hExit : CallExit fac σ p callArgs σAO expected)
    (h : EvalCommand π φ fac σ (.call n callArgs md) σ' failed) : σ' = expected := by
  cases h with
  | @call_sem _ _ q _ _ σFinal facFinal bodyFailed preFailed postFailed _ _ frame
      hLookup' hEntry' _ hBodyExec _ hExit' =>
    have hp : q = p := Option.some.inj (hLookup'.symm.trans hLookup)
    subst q
    have hFrame : frame = σAO := CallEntryUniqueResult hEntry' hEntry
    subst frame
    rw [hBody] at hBodyExec
    obtain ⟨rfl, _, _⟩ := hBodyExec.empty_unique π φ σAO σFinal fac facFinal bodyFailed
    exact CallExitUniqueResult hExit' hExit

/-- An event-producing concrete call to an empty body has the unique caller
result obtained from its uniquely determined entry frame and expected call exit. -/
theorem EvalCommandE.empty_body_call_store_unique
    {π : String → Option Procedure}
    {φ : Expression.Factory → PureFunc Expression → Expression.Factory}
    {fac : Expression.Factory} {σ σAO expected σ' : CoreStore}
    {n : String} {p : Procedure} {callArgs : List (CallArg Expression)}
    {md : MetaData Expression} {emitted : Trace Expression}
    (hLookup : π n = some p) (hBody : p.body = .structured [])
    (hEntry : CallEntry fac σ p callArgs σAO)
    (hExit : CallExit fac σ p callArgs σAO expected)
    (h : EvalCommandE π φ fac σ (.call n callArgs md) σ' emitted) : σ' = expected := by
  cases h with
  | @call_sem _ _ q _ _ σFinal facFinal bodyEvents _ _ frame
      hLookup' hEntry' hBodyExec hExit' =>
    have hp : q = p := Option.some.inj (hLookup'.symm.trans hLookup)
    subst q
    have hFrame : frame = σAO := CallEntryUniqueResult hEntry' hEntry
    subst frame
    rw [hBody] at hBodyExec
    obtain ⟨rfl, _, _⟩ := hBodyExec.empty_unique π φ σAO σFinal fac facFinal bodyEvents
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
      simp [isNotDefined] at *
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
      simp [InitStateInjective Hinit Hinit'] at *
      assumption
  . simp [InitStateUpdated Hinit']
    exact Hup

/-- Concatenating two reads from one store reads the concatenated keys and values. -/
theorem ReadValuesApp {P : PureExpr} [HasVal P] {f : P.Factory}
  {σ : SemanticStore P} {k1 k2 : List P.Ident} {v1 v2 : List P.Expr} :
  ReadValues f σ k1 v1 →
  ReadValues f σ k2 v2 →
  ReadValues f σ (k1 ++ k2) (v1 ++ v2) := by
  intros Hrd1 Hrd2
  induction Hrd1 <;> simp_all
  case read_some Hsome Hrd Hrds =>
  constructor <;> assumption

/-- A read over appended key lists splits into corresponding value lists and reads. -/
theorem ReadValuesAppKeys' {P : PureExpr} [HasVal P] {f : P.Factory}
  {σ : SemanticStore P} {k1 k2 : List P.Ident} {vs : List P.Expr} :
  ReadValues f σ (k1 ++ k2) vs →
  exists v1 v2,
  v1 ++ v2 = vs ∧
  ReadValues f σ k1 v1 ∧
  ReadValues f σ k2 v2 := by
  intros Hrd
  induction vs generalizing k1 k2
  case nil =>
    exists [],[]
    generalize Hk12 : k1 ++ k2 = k12 at Hrd
    cases Hrd
    simp_all
    constructor
  case cons vh vt vih =>
    cases k1
    case nil =>
      exists [],vh :: vt
      simp_all
      constructor
    case cons kh kt =>
      cases Hrd with
      | read_some Hsome _ Hrd =>
        specialize vih Hrd
        cases vih with
        | intro v1' vih =>
        cases vih with
        | intro v2 vih =>
        exists vh::v1',v2
        simp_all
        constructor <;> simp_all

/-- A read returns exactly one value for each requested key. -/
theorem ReadValuesLength {P : PureExpr} [HasVal P] {f : P.Factory}
  {σ : SemanticStore P} {ks : List P.Ident} {vs : List P.Expr} :
  ReadValues f σ ks vs →
  ks.length = vs.length := by
  intros Hrd
  induction Hrd <;> simp_all

theorem EvalExpressionsLength :
  EvalExpressions fac σ ks vs →
  ks.length = vs.length := by
  intros Hrd
  induction Hrd <;> simp_all

theorem InitStatesLength :
  InitStates σ ks vs σ' →
  ks.length = vs.length := by
  intros Hinit
  induction Hinit <;> simp_all

theorem UpdateStatesLength {P : PureExpr}
  {σ σ' : Imperative.SemanticStore P}
  {ks : List P.Ident}
  {vs : List P.Expr}
  :
  UpdateStates (P:=P) σ ks vs σ' →
  List.length ks = List.length vs := by
  intros Hup
  induction Hup <;> simp_all

/-- Initializing a fresh slot preserves every existing `ReadValues` derivation. -/
theorem InitStateReadValuesMonotone {P : PureExpr} [HasVal P] {f : P.Factory}
  {σ σ' : SemanticStore P}
  {ks : List P.Ident} {vs : List P.Expr} {e : P.Expr} {v : P.Ident} :
  ReadValues f σ ks vs →
  InitState P σ v e σ' →
  ReadValues f σ' ks vs := by
  intros Hdef Heval
  cases Heval with
  | init Hold HH Hsome =>
  induction Hdef
  case read_none => constructor
  case read_some xs vs' x v' Hsome' Hrd Hrds =>
  constructor <;> simp_all
  rw [Hsome] <;> try simp_all
  apply Not.intro
  intros Heq
  simp_all

/-- Initializing several fresh slots preserves every existing `ReadValues` derivation. -/
theorem InitStatesReadValuesMonotone
  {P : PureExpr} [HasVal P] {f : P.Factory} {σ σ' : SemanticStore P}
  {ks : List P.Ident} {vs : List P.Expr}
  {es' : List P.Expr} {vs' : List P.Ident} :
  ReadValues f σ ks vs →
  InitStates σ vs' es' σ' →
  ReadValues f σ' ks vs := by
  intros Hdef Heval
  induction Heval with
  | init_none => assumption
  | init_some Hinit Hinits ih =>
    apply ih
    apply InitStateReadValuesMonotone <;> assumption

/-- Updating a slot outside the requested keys preserves a `ReadValues` derivation. -/
theorem UpdateStateReadValuesMonotone {P : PureExpr} [HasVal P] {f : P.Factory}
  {σ σ' : SemanticStore P}
  {ks : List P.Ident} {vs : List P.Expr} {e : P.Expr} {v : P.Ident} :
  ¬ v ∈ ks →
  ReadValues f σ ks vs →
  UpdateState P σ v e σ' →
  ReadValues f σ' ks vs := by
  intros Hnin Hdef Heval
  cases Heval with
  | update Hold HH Hsome =>
  induction Hdef
  case read_none => constructor
  case read_some xs vs' x v' Hsome' Hrd Hrds =>
  constructor <;> simp_all

/-- Updating distinct slots disjoint from the requested keys preserves a `ReadValues`
derivation. -/
theorem UpdateStatesReadValuesMonotone
  {P : PureExpr} [HasVal P] {f : P.Factory} {σ σ' : SemanticStore P}
  {ks : List P.Ident} {vs : List P.Expr}
  {es' : List P.Expr} {vs' : List P.Ident} :
  (ks ++ vs').Nodup →
  ReadValues f σ ks vs →
  UpdateStates σ vs' es' σ' →
  ReadValues f σ' ks vs := by
  intros Hnd Hdef Heval
  induction Heval with
  | update_none => assumption
  | update_some Hinit Hinits ih =>
    have Hnd' := nodup_middle Hnd
    simp_all
    apply ih
    apply UpdateStateReadValuesMonotone _ Hdef Hinit <;> try assumption
    simp_all

/-- Initializing one slot with a canonical expression makes that expression readable
    from the slot in the resulting store. -/
theorem InitStateReadValues {P : PureExpr} [HasVal P] {f : P.Factory}
  {σ σ' : SemanticStore P} {v : P.Ident} {e : P.Expr} :
  HasVal.value f e →
  InitState P σ v e σ' →
  ReadValues f σ' [v] [e] := by
  intro hval Hinit
  cases Hinit with
  | init _ Hsome _ => exact .read_some Hsome hval .read_none

/-- Updating one slot with a canonical expression makes that expression readable
    from the slot in the resulting store. -/
theorem UpdateStateReadValues {P : PureExpr} [HasVal P] {f : P.Factory}
  {σ σ' : SemanticStore P} {v : P.Ident} {e : P.Expr} :
  HasVal.value f e →
  UpdateState P σ v e σ' →
  ReadValues f σ' [v] [e] := by
  intro hval Hupdate
  cases Hupdate with
  | update _ Hsome _ => exact .read_some Hsome hval .read_none

/-- Initializing slots from canonical expressions makes the expressions readable
    at the corresponding slots in the resulting store. -/
theorem InitStatesReadValues {P : PureExpr} [HasVal P] {f : P.Factory}
  {σ σ' : SemanticStore P} {vs : List P.Ident} {es : List P.Expr} :
  (∀ v ∈ es, HasVal.value f v) →
  InitStates σ vs es σ' →
  ReadValues f σ' vs es := by
  intro hvals Hinit
  induction Hinit with
  | init_none => exact .read_none
  | init_some Hinit Hinits ih =>
    rename_i x v σ₁ xs es' σ''
    have hv : HasVal.value f v := hvals v List.mem_cons_self
    have hrd : ReadValues f σ'' [x] [v] :=
      InitStatesReadValuesMonotone (σ := σ₁)
        (InitStateReadValues hv Hinit) Hinits
    cases hrd with
    | read_some hx _ _ =>
      exact .read_some hx hv
        (ih (fun w hw => hvals w (List.mem_cons_of_mem _ hw)))

/-- Updating distinct slots from canonical expressions makes the expressions
    readable at the corresponding slots in the resulting store. -/
theorem UpdateStatesReadValues {P : PureExpr} [HasVal P] {f : P.Factory}
  {σ σ' : SemanticStore P} {vs : List P.Ident} {es : List P.Expr} :
  vs.Nodup →
  (∀ v ∈ es, HasVal.value f v) →
  UpdateStates σ vs es σ' →
  ReadValues f σ' vs es := by
  intro hnd hvals Hupdates
  induction Hupdates with
  | update_none => exact .read_none
  | update_some Hupdate Hupdates ih =>
    rename_i x v σ₁ xs es' σ''
    have hv : HasVal.value f v := hvals v List.mem_cons_self
    have hrd : ReadValues f σ'' [x] [v] :=
      UpdateStatesReadValuesMonotone (σ := σ₁) hnd
        (UpdateStateReadValues hv Hupdate) Hupdates
    cases hrd with
    | read_some hx _ _ =>
      exact .read_some hx hv
        (ih hnd.tail (fun w hw => hvals w (List.mem_cons_of_mem _ hw)))

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
  {ks vs' : List P.Ident} {vs : List P.Expr} :
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
  {k k' : P.Ident} {v v' : P.Expr} :
  k ≠ k' →
  updatedState (updatedState σ k v) k' v' =
  updatedState (updatedState σ k' v') k v := by
  intros Hne
  funext x
  unfold updatedState
  by_cases Hxk' : x = k' <;> simp [Hxk']
  intros Heq
  by_cases Hxk : x = k <;> simp_all

theorem updatedStateComm'
  {P : PureExpr} {σ : SemanticStore P}
  {k : P.Ident} {v : P.Expr}
  {kvs : List (P.Ident × P.Expr)} :
  ¬ k ∈ kvs.unzip.1 →
  (updatedState (updatedStates' σ kvs) k v) =
  (updatedStates' (updatedState σ k v) kvs) := by
  intros Hnd
  induction kvs generalizing σ <;> simp [updatedStates']
  case cons h t ih =>
  rw [ih]
  rw [updatedStateComm]
  simp_all; exact fun a => Hnd.1 (Eq.symm a)
  simp_all

theorem updatedStatesComm
  {P : PureExpr} {σ : SemanticStore P}
  {kvs kvs' : List (P.Ident × P.Expr)} :
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
    . simp at Hnd
      have Hnd' := List.Disj.symm Hnd
      apply List.Disjoint_cons_head
      apply List.Disj.mono_right _ Hnd'
      simp_all
    . intros Hin
      simp_all [List.Disj]
    . simp at *
      refine List.Disj.mono_right ?_ Hnd
      simp_all

theorem UpdateStateSomeMonotone
  {P : PureExpr} {σ σ' : SemanticStore P}
  {k' : P.Ident} {v' : P.Expr} {e : P.Expr} {v : P.Ident} :
  v ≠ k' →
  σ k' = some v' →
  UpdateState P σ v e σ' →
  σ' k' = some v' := by
  intro hne hdef hupdate
  cases hupdate with
  | update _ _ hother => simpa [hother k' hne] using hdef

theorem UpdateStatesSomeMonotone
  {P : PureExpr} {σ σ' : SemanticStore P}
  {k' : P.Ident} {v' : P.Expr}
  {ks': List P.Ident} {vs': List P.Expr} :
  ¬ k' ∈ ks' →
  σ k' = some v' →
  UpdateStates σ ks' vs' σ' →
  σ' k' = some v' := by
  intros Hnin Hsome Hinit
  induction Hinit <;> try simp_all
  next Hinit Hinits ih =>
  apply ih
  apply UpdateStateSomeMonotone ?_ Hsome Hinit
  exact fun a => Hnin.1 (Eq.symm a)

theorem InitStateSomeMonotone
  {P : PureExpr} {σ σ' : SemanticStore P}
  {k' : P.Ident} {v' : P.Expr} {e : P.Expr} {v : P.Ident} :
  σ k' = some v' →
  InitState P σ v e σ' →
  σ' k' = some v' := by
  intro hdef hinit
  cases hinit with
  | init hnone _ hother =>
    by_cases h : v = k'
    · subst h; simp_all
    · simpa [hother k' h] using hdef

theorem InitStateSomeMonotone'
  {P : PureExpr} {σ σ' : SemanticStore P}
  {k' : P.Ident} {v' : P.Expr} {e : P.Expr} {v : P.Ident} :
  k' ≠ v →
  σ' k' = some v' →
  InitState P σ v e σ' →
  σ k' = some v' := by
  intro hne hdef hinit
  cases hinit with
  | init _ _ hother => simpa [hother k' (Ne.symm hne)] using hdef

theorem InitStatesSomeMonotone
  {P : PureExpr} {σ σ' : SemanticStore P}
  {k' : P.Ident} {v' : P.Expr}
  {ks': List P.Ident} {vs': List P.Expr} :
  σ k' = some v' →
  InitStates σ ks' vs' σ' →
  σ' k' = some v' := by
  intros Hsome Hinit
  induction Hinit <;> try simp_all
  next Hinit Hinits ih =>
  apply ih
  apply InitStateSomeMonotone Hsome Hinit

theorem InitStatesSomeMonotone'
  {P : PureExpr} {σ σ' : SemanticStore P}
  {k' : P.Ident} {v' : P.Expr}
  {ks': List P.Ident} {vs': List P.Expr} :
  ¬ k' ∈ ks' →
  σ' k' = some v' →
  InitStates σ ks' vs' σ' →
  σ k' = some v' := by
  intros Hnin Hsome Hinit
  induction Hinit
  case init_none => simp_all
  case init_some Hinit Hinits ih =>
  apply InitStateSomeMonotone' ?_ ?_ Hinit
  . simp_all
  . apply ih <;> simp_all

theorem InitsUpdatesComm
  {P : PureExpr} {σ σ' σ'' : SemanticStore P}
  {ks ks' : List P.Ident} {vs vs' : List P.Expr} :
  UpdateStates σ ks vs σ' →
  InitStates σ' ks' vs' σ'' →
  ∃ σ₁,
    σ₁ = (updatedStates σ ks' vs') ∧
    InitStates σ ks' vs' σ₁ ∧
    UpdateStates σ₁ ks vs σ'' := by
  intros Hup Hinit
  exists (updatedStates σ ks' vs')
  have Hk : (isDefined σ' ks) := UpdateStatesDefined Hup
  have Hlen1 := InitStatesLength Hinit
  have Hlen2 := UpdateStatesLength Hup
  induction Hup generalizing σ''
  case update_none =>
    simp_all
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
      . simp [UpdateStateUpdated Hup, updatedStates]
        rw [← updatedStateComm']
        . have Hdef := UpdateStateDefined' Hup
          simp [isDefined, Option.isSome] at Hdef
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
        . rw [List.unzip_zip] <;> simp_all
          have Hnd := InitStatesNotDefined Hinit
          simp [isNotDefined, isDefined] at *
          apply Not.intro
          intros Hin
          specialize Hnd _ Hin
          simp_all
      . apply (ih Hinit ?_ ?_).2.2
        . simp [isDefined] at * <;> simp_all
        . simp_all

theorem InitUpdateComm
  {P : PureExpr} {σ σ' σ'' : SemanticStore P}
  {k k' : P.Ident} {v v' : P.Expr}
  :
  UpdateState P σ k v σ' →
  InitState P σ' k' v' σ'' →
  ∃ σ₁,
    σ₁ = (updatedState σ k' v') ∧
    InitState P σ k' v' σ₁ ∧
    UpdateState P σ₁ k v σ'' := by
  intros Hup Hinit
  exists (updatedState σ k' v')
  have Hk : (isDefined σ' [k]) := UpdateStateDefined Hup
  have Hups : UpdateStates σ [k] [v] σ' := by
    apply UpdateStates.update_some Hup UpdateStates.update_none
  have Hinits : InitStates σ' [k'] [v'] σ'' := by
    apply InitStates.init_some Hinit InitStates.init_none
  have Hcomms := InitsUpdatesComm Hups Hinits
  simp at Hcomms
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

/-- If a store defines every requested key and all of its bindings are canonical
    values, those keys admit a corresponding `ReadValues` derivation. -/
theorem isDefinedReadValues {P : PureExpr} [HasVal P] {f : P.Factory}
  {σ : SemanticStore P} {ks : List P.Ident} :
  WellFormedStore σ f →
  isDefined σ ks →
  ∃ vs, ReadValues f σ ks vs := by
  intro hwf hdef
  induction ks with
  | nil => exact ⟨[], .read_none⟩
  | cons x xs ih =>
    have hx := hdef x List.mem_cons_self
    rw [Option.isSome_iff_exists] at hx
    obtain ⟨v, hx⟩ := hx
    obtain ⟨vs, hvs⟩ := ih (fun y hy => hdef y (List.mem_cons_of_mem _ hy))
    exact ⟨v :: vs, .read_some hx (hwf x v hx) hvs⟩

/-- Successfully reading a key list implies that every requested key is defined in
the store. -/
theorem ReadValuesIsDefined {P : PureExpr} [HasVal P] {f : P.Factory}
  {σ : SemanticStore P} {ks : List P.Ident} {vs : List P.Expr} :
  ReadValues f σ ks vs →
  isDefined σ ks := by
  intros Hrd
  induction Hrd <;> simp [isDefined, Option.isSome]
  apply And.intro
  . split <;> simp_all
  . intros a Hin
    split <;> simp_all
    next ih ex Hnone =>
    specialize ih a Hin
    simp_all

theorem substStoresInitInv :
substDefined σ σ' substs →
substStores σ σ' substs →
InitState Expression σ' k v σ'' →
substStores σ σ'' substs := by
  intros Hdef Hsubst Hinit
  simp [substStores, substDefined] at *
  intros k1 k2 Hin
  cases Hinit with
  | init Hnone Hsome' Heq =>
  rw [Heq] <;> simp_all
  rw [Hsubst] <;> simp_all
  apply Not.intro
  intro Heq'
  simp [Heq'] at *
  specialize Hdef k1 k2 Hin
  simp [Option.isSome] at Hdef
  split at Hdef <;> simp_all

theorem substStoresInitsInv :
substDefined σ σ' substs →
substStores σ σ' substs →
InitStates σ' ks vs σ'' →
substStores σ σ'' substs := by
  intros Hdef Hsubst Hinit
  simp [substStores, substDefined] at *
  intros k1 k2 Hin
  induction Hinit generalizing σ
  case init_none =>
    exact Hsubst k1 k2 Hin
  case init_some Hinit Hinits ih =>
    simp [Hsubst k1 k2 Hin]
    specialize Hdef k1 k2 Hin
    simp [Option.isSome] at Hdef
    split at Hdef <;> simp_all
    split at Hdef <;> simp_all
    next x val Hsome =>
    have Hsome' := InitStateSomeMonotone Hsome Hinit
    have Hsome'' := InitStatesSomeMonotone Hsome' Hinits
    simp_all

theorem substStoresInitsInv' :
substDefined σ σ' substs →
substStores σ σ' substs →
InitStates σ ks vs σ'' →
substStores σ'' σ' substs := by
  intros k1 k2 Hin
  rw [← substSwapId _ substs]
  apply substStoresFlip
  apply substStoresInitsInv <;> try assumption
  . exact substDefinedFlip k1
  . exact substStoresFlip k2

theorem substStoresUpdateInv {k : P.Ident} {substs : List (P.Ident × P.Ident)}:
¬ k ∈ substs.unzip.2 →
substStores (P:=P) σ σ' substs →
UpdateState (P:=P) σ' k v σ'' →
substStores (P:=P) σ σ'' substs := by
  intros Hnin Hsubst Hinit
  simp [substStores] at *
  intros k1 k2 Hin
  cases Hinit with
  | update Hnone Hsome' Heq =>
  rw [Heq] <;> simp_all
  rw [Hsubst] <;> simp_all
  intros Heq'
  specialize Hnin k1
  simp_all

theorem substStoresUpdatesInv :
ks.Disj substs.unzip.2 →
substStores σ σ' substs →
UpdateStates σ' ks vs σ'' →
substStores σ σ'' substs := by
  intros Hnin Hsubst Hup
  simp [substStores] at *
  intros k1 k2 Hin
  induction Hup generalizing σ
  case update_none =>
    exact Hsubst k1 k2 Hin
  case update_some σ x v σ' xs vs σ₁ Hup Hinits ih =>
    have Hnin : ¬ x ∈ substs.unzip.2 := by
      simp [List.Disj] at Hnin
      intros Hin
      have Hprod := List.mem_zip_2 (l₁:=substs.unzip.fst) (by simp) Hin
      rw [List.zip_unzip] at Hprod
      cases Hprod with
      | intro w Hprod =>
      have HH := Hnin.1 w
      contradiction
    have HH := substStoresUpdateInv (σ:=σ) Hnin Hsubst Hup
    apply ih HH
    simp [List.Disj] at *
    simp_all

theorem substStoresUpdatesInv' :
ks.Disj substs.unzip.1 →
substStores σ σ' substs →
UpdateStates σ ks vs σ'' →
substStores σ'' σ' substs := by
  intros Hdisj Hsubst Hup
  rw [← substSwapId _ substs]
  apply substStoresFlip
  apply substStoresUpdatesInv <;> try assumption
  . intros a Hin Hin'
    specialize Hdisj Hin
    simp [substSwap] at Hin'
    simp_all
  . exact substStoresFlip Hsubst

theorem substDefinedIsDefined :
  substDefined σ σ' substs →
  isDefined σ substs.unzip.1 ∧
  isDefined σ' substs.unzip.2 := by
  intros Hsubst
  cases substs <;> simp [isDefined, substDefined] at *
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
  simp [substStores, substDefined] at *
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
    simp [updatedState]
    simp [substNodup] at Hnd
    intros k1 k2 Hin
    split <;> simp_all
    next heq =>
      have Hnd' := Hnd.2
      have Hin' : h' ∈ substs.unzip.1 := by
        simp_all
        exists k2
      exfalso
      have Hnd' := nodup_middle Hnd'
      simp_all
    next hne =>
      apply Hsubst
      exact Or.inr Hin

theorem substStoresCons :
  substStores σ σ' [(h,h')] →
  substStores σ σ' (List.zip t t') →
  substStores σ σ' ((h,h') :: (List.zip t t')) := by
  intros Hh Ht
  intros k1 k2 Hin
  simp at Hin
  cases Hin with
  | inl Hin =>
    apply Hh
    simp_all
  | inr Hin =>
    apply Ht
    simp_all

/-- If two stores read the same values at respective key lists, the stores agree
under the substitution that zips those keys. -/
theorem ReadValuesSubstStores {P : PureExpr} [HasVal P] {f : P.Factory}
  {σ σ' : SemanticStore P} {ks ks' : List P.Ident} {vs : List P.Expr} :
  ReadValues f σ ks vs →
  ReadValues f σ' ks' vs →
  Imperative.substStores σ σ' (List.zip ks ks') := by
  intros H1 H2
  induction vs generalizing ks ks'
  case nil =>
    cases H1
    cases H2
    intros h1 h2 Hin
    cases Hin
  case cons h t ih =>
    cases ks
    cases H1
    cases ks'
    cases H2
    cases H1 with
    | read_some Hh _ Ht =>
    cases H2 with
    | read_some Hh' _ Ht' =>
    simp
    apply substStoresCons
    . simp [substStores]
      simp_all
    . exact ih Ht Ht'

theorem EvalStatementsContractApp' {φ : Expression.Factory → PureFunc Expression → Expression.Factory} :
  EvalStatementsContract π φ ρ (ss₁ ++ ss₂) ρ'' →
  ∃ ρ',
    EvalStatementsContract π φ ρ ss₁ ρ' ∧
    EvalStatementsContract π φ ρ' ss₂ ρ'' := by
  intro Heval
  induction ss₁ generalizing ρ with
  | nil =>
    simp at Heval
    exact ⟨ρ, evalStmtsSmallNil Expression (EvalCommandContract π) (EvalPureFunc φ) ρ, Heval⟩
  | cons s ss₁ ih =>
    simp [List.cons_append] at Heval
    unfold EvalStatementsContract EvalStmtsSmall at Heval
    match Heval with
    | .step _ _ _ .step_stmts_cons hrest =>
      have ⟨ρ₁, hterm_s, htail⟩ :=
        seq_reaches_terminal Expression (EvalCommandContract π) (EvalPureFunc φ) hrest
      have ⟨ρ', Hss₁, Hss₂⟩ := ih htail
      have Hcons : EvalStmtsSmall Expression (EvalCommandContract π) (EvalPureFunc φ) ρ (s :: ss₁) ρ' := by
        unfold EvalStmtsSmall
        apply ReflTrans.step _ _ _ .step_stmts_cons
        exact ReflTrans_Transitive _ _ _ _
          (seq_inner_star Expression (EvalCommandContract π) (EvalPureFunc φ) _ _ ss₁ hterm_s)
          (.step _ _ _ .step_seq_done
            (show StepStmtStar Expression (EvalCommandContract π) (EvalPureFunc φ)
              (.stmts ss₁ ρ₁) (.terminal ρ') from Hss₁))
      exact ⟨ρ', Hcons, Hss₂⟩

theorem EvalStatementsContractApp {φ : Expression.Factory → PureFunc Expression → Expression.Factory} :
  EvalStatementsContract π φ ρ ss₁ ρ' →
  EvalStatementsContract π φ ρ' ss₂ ρ'' →
  EvalStatementsContract π φ ρ (ss₁ ++ ss₂) ρ'' := by
  intro Heval1 Heval2
  induction ss₁ generalizing ρ ρ' with
  | nil =>
    simp
    have Heq := EvalStatementsContractEmpty Heval1
    rw [Heq]; exact Heval2
  | cons s ss₁ ih =>
    simp [List.cons_append]
    -- Peel off s from Heval1
    unfold EvalStatementsContract EvalStmtsSmall at Heval1
    match Heval1 with
    | .step _ _ _ .step_stmts_cons hrest =>
      have ⟨ρ₁, hterm_s, htail⟩ :=
        seq_reaches_terminal Expression (EvalCommandContract π) (EvalPureFunc φ) hrest
      -- hterm_s : .stmt s ρ →* .terminal ρ₁
      -- htail : .stmts ss₁ ρ₁ →* .terminal ρ'
      -- IH: EvalStmtsSmall ρ₁ ss₁ ρ' → EvalStmtsSmall ρ' ss₂ ρ'' → EvalStmtsSmall ρ₁ (ss₁ ++ ss₂) ρ''
      have Hconcat := ih htail Heval2
      -- Hconcat : EvalStmtsSmall ρ₁ (ss₁ ++ ss₂) ρ''
      -- Build: .stmts (s :: (ss₁ ++ ss₂)) ρ →* .terminal ρ''
      show EvalStmtsSmall Expression (EvalCommandContract π) (EvalPureFunc φ) ρ (s :: (ss₁ ++ ss₂)) ρ''
      unfold EvalStmtsSmall
      apply ReflTrans.step _ _ _ .step_stmts_cons
      exact ReflTrans_Transitive _ _ _ _
        (seq_inner_star Expression (EvalCommandContract π) (EvalPureFunc φ) _ _ (ss₁ ++ ss₂) hterm_s)
        (.step _ _ _ .step_seq_done Hconcat)

theorem EvalStatementsApp {φ : Expression.Factory → PureFunc Expression → Expression.Factory} :
  EvalStatements π φ ρ ss₁ ρ' →
  EvalStatements π φ ρ' ss₂ ρ'' →
  EvalStatements π φ ρ (ss₁ ++ ss₂) ρ'' := by
  intro Heval1 Heval2
  induction ss₁ generalizing ρ ρ' with
  | nil =>
    simp
    have Heq := EvalStatementsEmpty Heval1
    rw [Heq]; exact Heval2
  | cons s ss₁ ih =>
    simp [List.cons_append]
    unfold EvalStatements EvalStmtsSmall at Heval1
    match Heval1 with
    | .step _ _ _ .step_stmts_cons hrest =>
      have ⟨ρ₁, hterm_s, htail⟩ :=
        seq_reaches_terminal Expression (EvalCommand π φ) (EvalPureFunc φ) hrest
      have Hconcat := ih htail Heval2
      show EvalStmtsSmall Expression (EvalCommand π φ) (EvalPureFunc φ) ρ (s :: (ss₁ ++ ss₂)) ρ''
      unfold EvalStmtsSmall
      apply ReflTrans.step _ _ _ .step_stmts_cons
      exact ReflTrans_Transitive _ _ _ _
        (seq_inner_star Expression (EvalCommand π φ) (EvalPureFunc φ) _ _ (ss₁ ++ ss₂) hterm_s)
        (.step _ _ _ .step_seq_done Hconcat)

theorem HavocVarsApp {P : PureExpr} [HasVal P] {f : P.Factory} {σ σ' σ'' : SemanticStore P} {vs₁ vs₂ : List P.Ident} :
  HavocVars f σ vs₁ σ' →
  HavocVars f σ' vs₂ σ'' →
  HavocVars f σ (vs₁ ++ vs₂) σ'' := by
  intros Hv1 Hv2
  induction vs₁ generalizing σ
  case nil =>
    simp
    have Heq := HavocVarsEmpty Hv1
    simp [Heq]
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
    simp_all
    constructor <;> assumption

theorem InitVarsApp :
  InitVars σ vs₁ σ' →
  InitVars σ' vs₂ σ'' →
  InitVars σ (vs₁ ++ vs₂) σ'' := by
  intros Hv1 Hv2
  induction vs₁ generalizing σ
  case nil =>
    simp
    have Heq := InitVarsEmpty Hv1
    simp [Heq]
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
    simp
    have Heq := TouchVarsEmpty Hv1
    simp [Heq]
    assumption
  case cons h t ih =>
    simp
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

theorem HavocVarsId {P : PureExpr} [HasVal P] {f : P.Factory} {σ : SemanticStore P} {vs : List P.Ident} :
  WellFormedStore σ f →
  isDefined σ vs →
  HavocVars f σ vs σ := by
  intros Hwf Hdef
  induction vs with
  | nil => constructor
  | cons h t ih =>
    have Hh := Hdef h List.mem_cons_self
    rw [Option.isSome_iff_exists] at Hh
    obtain ⟨v', heq⟩ := Hh
    apply HavocVars.update_some (σ':=σ) (v:=v')
    · exact UpdateState.update heq heq (fun y _ => rfl)
    · exact Hwf h v' heq
    · apply ih
      intro v Hin
      exact Hdef v (List.mem_cons_of_mem _ Hin)

theorem TouchVarsId :
  isDefined σ vs →
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
  simp [isDefined] at *
  intros v Hin
  apply Hdef.2 v Hin

theorem InitStateDefMonotone
  {P : PureExpr} {σ σ' : SemanticStore P}
  {vs : List P.Ident} {e : P.Expr} {v : P.Ident} :
  isDefined σ vs →
  InitState P σ v e σ' →
  isDefined σ' vs := by
  intros Hdef Heval
  cases Heval with
  | init Hold HH Hsome =>
  simp [isDefined] at *
  intros v' Hv'
  by_cases Heq: (v = v')
  case pos =>
    simp [Option.isSome]
    simp [Heq] at *
    split <;> simp_all
  case neg =>
    specialize Hsome v' Heq
    specialize Hdef v'
    simp [Hsome]
    exact Hdef Hv'

theorem InitStatesDefMonotone :
  isDefined σ vs →
  InitStates σ vs' es' σ' →
  isDefined σ' vs := by
  intros Hdef Hhavoc
  induction Hhavoc with
  | init_some Hup Hhav ih =>
  apply ih
  apply InitStateDefMonotone <;> assumption
  | init_none => simp_all

theorem InitVarsDefMonotone :
  isDefined σ vs →
  InitVars σ vs' σ' →
  isDefined σ' vs := by
  intros Hdef Hhavoc
  induction Hhavoc with
  | init_some Hup Hhav ih =>
  apply ih
  apply InitStateDefMonotone <;> assumption
  | init_none => simp_all

theorem InitStateDefMonotone'
  {P : PureExpr} {σ σ' : SemanticStore P}
  {vs : List P.Ident} {e : P.Expr} {v : P.Ident} :
  ¬ v ∈ vs →
  isDefined σ' vs →
  InitState P σ v e σ' →
  isDefined σ vs := by
  intros Hnin Hdef Heval
  cases Heval with
  | init Hold HH Hsome =>
  simp [isDefined] at *
  intros v' Hv'
  by_cases Heq: (v = v')
  case pos =>
    simp [Option.isSome]
    simp [Heq] at *
    split <;> simp_all
  case neg =>
    specialize Hsome v' Heq
    specialize Hdef v'
    simp [← Hsome]
    exact Hdef Hv'

theorem InitStatesDefMonotone' :
  vs.Disj vs' →
  isDefined σ' vs →
  InitStates σ vs' es' σ' →
  isDefined σ vs := by
  intros Hdisj Hdef Hhavoc
  induction Hhavoc with
  | init_none => assumption
  | init_some Hup Hhav ih =>
  next σ x v σ' xs' ys' σ'' =>
  apply InitStateDefMonotone' (σ':=σ') <;> try assumption
  . intros Hin
    apply Hdisj Hin
    exact List.mem_cons_self
  . apply ih
    . apply List.Disj.mono_right _ Hdisj
      exact List.sublist_cons_self x xs'
    . assumption

theorem InitVarsDefMonotone' :
  vs.Disj vs' →
  isDefined σ' vs →
  InitVars σ vs' σ' →
  isDefined σ vs := by
  intros Hdisj Hdef Hinit
  have Hinit := InitVarsInitStates Hinit
  cases Hinit with
  | intro es Hinit =>
  exact InitStatesDefMonotone' Hdisj Hdef Hinit

-- theorem InitVarsNotDefMonotone' :
--   vs.Disj vs' →
--   isDefined σ' vs →
--   InitVars σ vs' σ' →
--   isNotDefined σ vs := by
--   intros Hdisj Hdef Hinit
--   have Hinit := InitVarsInitStates Hinit
--   cases Hinit with
--   | intro es Hinit =>
--   exact InitStatesDefMonotone' Hdisj Hdef Hinit

theorem InitStatesDefined :
  InitStates σ hs vs σ' → isDefined σ' hs := by
  intros Hinit
  induction Hinit <;> simp [isDefined]
  case init_some x v σ' xs vs σ'' Hinit Hinits ih =>
    simp [isDefined] at *
    cases Hinit with
    | init Hnone Hsome Heq =>
    refine ⟨?_, by simp_all⟩
    have Hdef : isDefined σ'' [x] := by
      apply InitStatesDefMonotone ?_ Hinits
      simp [isDefined, Option.isSome]
      split <;> simp_all
    simp [isDefined] at Hdef
    assumption

theorem HavocVarsDefMonotone {P : PureExpr} [HasVal P] {f : P.Factory} {σ σ' : SemanticStore P} {vs vs' : List P.Ident} :
  isDefined σ vs →
  HavocVars f σ vs' σ' →
  isDefined σ' vs := by
  intros Hdef Hhavoc
  induction Hhavoc with
  | update_some Hup Hval Hhav ih =>
  apply ih
  apply UpdateStateDefMonotone <;> assumption
  | update_none => simp_all

theorem HavocVarsUpdateStates {P : PureExpr} [HasVal P] {f : P.Factory} {σ σ' : SemanticStore P} {vars : List P.Ident} : HavocVars f σ vars σ' →
  ∃ modvals, UpdateStates σ vars modvals σ' ∧ ∀ v, v ∈ modvals → HasVal.value f v := by
  intros Hhav
  induction Hhav with
  | update_none =>
    exact ⟨[], UpdateStates.update_none, by intro v hv; simp at hv⟩
  | update_some Hup Hval Hhav ih =>
    obtain ⟨vs, Hups, Hvals⟩ := ih
    refine ⟨_, UpdateStates.update_some Hup Hups, ?_⟩
    intro w hw
    cases hw with
    | head => exact Hval
    | tail _ hm => exact Hvals w hm

theorem HavocVarsDefMonotone' {P : PureExpr} [HasVal P] {f : P.Factory} {σ σ' : SemanticStore P} {vs vs' : List P.Ident} :
  isDefined σ' vs →
  HavocVars f σ vs' σ' →
  isDefined σ vs := by
  intros Hdef Hhavoc
  have Hup := HavocVarsUpdateStates Hhavoc
  obtain ⟨es, Hinit, _⟩ := Hup
  exact UpdateStatesDefMonotone' Hdef Hinit

theorem InitVarsDefined :
  InitVars σ vs σ' →
  isDefined σ' vs := by
  intros Hhavoc
  induction vs generalizing σ σ'
  case nil => simp [isDefined]
  case cons h t ih =>
    cases Hhavoc with
    | @init_some _ _ v σ₁ _ _ Hup Hhav =>
    apply isDefinedCons
    apply InitVarsDefMonotone (σ:=σ₁)
    apply InitStateDefined <;> assumption
    assumption
    apply ih <;> assumption

/-- Variables introduced by `InitVars` can be read back as values when the
    resulting store contains only canonical bindings. -/
theorem InitVarsReadValues {P : PureExpr} [HasVal P] {f : P.Factory}
  {σ σ' : SemanticStore P} {ks : List P.Ident} :
  WellFormedStore σ' f →
  InitVars σ ks σ' →
  ∃ vs, ReadValues f σ' ks vs := by
  intro hwf hinit
  exact isDefinedReadValues hwf (InitVarsDefined hinit)

theorem HavocVarsDefined {P : PureExpr} [HasVal P] {f : P.Factory} {σ σ' : SemanticStore P} {vs : List P.Ident} :
  HavocVars f σ vs σ' →
  isDefined σ' vs := by
  intros Hhavoc
  induction Hhavoc with
  | update_none => simp [isDefined]
  | update_some Hup Hval Hhav ih =>
    exact isDefinedCons (HavocVarsDefMonotone (UpdateStateDefined Hup) Hhav) ih

theorem EvalCmdDefMonotone' :
  isDefined σ v →
  EvalCmd Core.Expression fac σ c σ' f →
  isDefined σ' v := by
  intros Hdef Heval
  cases Heval with
  | eval_init Hsm Hup Hwf => exact InitStateDefMonotone Hdef Hup
  | eval_init_unconstrained Hup Hval Hwf => exact InitStateDefMonotone Hdef Hup
  | eval_set Hsm Hup Hwf => exact UpdateStateDefMonotone Hdef Hup
  | eval_set_nondet Hup Hval Hwf => exact UpdateStateDefMonotone Hdef Hup
  | _ => exact Hdef

theorem UpdateStatesHavocVars {P : PureExpr} [HasVal P] {f : P.Factory} {σ σ' : SemanticStore P} {vars : List P.Ident} {modvals : List P.Expr} :
  (∀ v, v ∈ modvals → HasVal.value f v) →
  UpdateStates σ vars modvals σ' → HavocVars f σ vars σ' := by
  intros Hvals H
  induction vars generalizing σ modvals
  case nil =>
    cases modvals
    . have Heq := UpdateStatesEmpty H
      simp [Heq]
      apply HavocVars.update_none
    . cases H
  case cons h t ih =>
    cases H
    next mv σmid mvs Hup Hups =>
    apply HavocVars.update_some Hup (Hvals mv List.mem_cons_self)
    exact ih (fun v hv => Hvals v (List.mem_cons_of_mem _ hv)) Hups

theorem UpdateStatesTouchVars : UpdateStates σ vars modvals σ' → TouchVars σ vars σ' := by
  intros H
  induction vars generalizing σ modvals
  case nil =>
    cases modvals
    . have Heq := UpdateStatesEmpty H
      simp [Heq]
      apply TouchVars.none
    . cases H
  case cons h t ih =>
    have HH := H
    cases H
    next Hup2 =>
    apply TouchVars.update_some <;> try assumption
    apply ih
    apply Hup2

theorem EvalCmdRefinesContract :
EvalCmd Expression fac σ c σ' f →
EvalCommandContract π fac σ (CmdExt.cmd c) σ' f := by
  intros H; constructor; exact H

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
      simp [updatedState]
      split <;> simp_all
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
  simp [updatedStates]
  simp [zip_self_eq Hin] at *
  induction ks' generalizing vs' σ σ'
  case nil =>
    simp [updatedStates']
    exact Hinv k2 k2 Hin
  case cons h t ih =>
    induction vs' generalizing h t σ σ' <;> simp_all
    case cons h' t' ih' =>
      simp [updatedStates']
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
  simp [invStores]
  apply substStoresFlip'
  simp [substSwap] at *
  rw [← invStores]
  exact InvStoresUpdatedStateDisjRightMono Hnin Hinv'

theorem InvStoresUpdatedStatesDisjLeftMono :
  ks.Disj ks' →
  invStores σ σ' ks →
  ks'.length = vs'.length →
  invStores (updatedStates σ ks' vs') σ' ks := by
  intros Hnin Hinv Hlen
  have Hinv' := substStoresFlip Hinv
  simp [invStores]
  apply substStoresFlip'
  simp [substSwap] at *
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
  simp [invStoresExcept] at *
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
    simp [updatedStates']
    cases Hin with
    | inl Heq =>
      simp_all
      rw [← updatedStateComm']
      rw [← updatedStateComm']
      simp [updatedState]
      . simp_all
        intros x Hin
        have HH := List.of_mem_zip Hin
        simp_all
      . simp_all
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
    simp [updatedStates']
    rw [← updatedStateComm']
    rw [← updatedStateComm']
    . simp [updatedState]
      split <;> simp_all
      apply ih <;> simp_all
    . simp_all
      intros x Hin
      have HH := List.of_mem_zip Hin
      simp_all
    . simp_all
      intros x Hin
      have HH := List.of_mem_zip Hin
      simp_all

theorem InvStoresExceptUpdatedSame :
  invStoresExcept σ σ' ks →
  ks'.length = vs'.length →
  ks'.Nodup →
  invStoresExcept (updatedStates σ ks' vs') (updatedStates σ' ks' vs') ks := by
  intros Hinv Hlen Hnd
  simp [invStoresExcept] at *
  intros vsInv Hdisj k1 k2 Hin
  have Heq := zip_self_eq Hin
  simp [Heq]
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
  simp [invStoresExcept] at *
  intros Hsub vs Hdisj
  refine InvStoresUpdatedStatesDisjLeftMono ?_ ?_ Hlen
  exact List.Disjoint_Subset_right Hdisj Hsub
  exact Hinv _ Hdisj

theorem InvStoresExceptUpdateStates :
  invStoresExcept σ σ' ks →
  UpdateStates σ ks' vs' σ'' →
  invStoresExcept σ'' σ' (ks ++ ks') := by
  intros Hinv Hup
  have Hup' := UpdateStatesUpdated Hup
  simp [Hup']
  refine InvStoresExceptUpdated Hinv ?_
  exact UpdateStatesLength Hup

theorem InvStoresExceptInitStates :
  invStoresExcept σ σ' ks →
  InitStates σ ks' vs' σ'' →
  invStoresExcept σ'' σ' (ks ++ ks') := by
  intros Hinv Hup
  have Hup' := InitStatesUpdated Hup
  simp [Hup']
  refine InvStoresExceptUpdated Hinv ?_
  exact InitStatesLength Hup

theorem InvStoresExceptHavocVars {P : PureExpr} [HasVal P] {f : P.Factory} {σ σ' σ'' : SemanticStore P} {ks ks' : List P.Ident} :
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
    (φ : Expression.Factory → PureFunc Expression → Expression.Factory)
    (l : String) (e : Expression.Expr) (md : MetaData Expression)
    (σ_entry : CoreStore) (fac : Expression.Factory) (ρ' : Env Expression)
    (emitted : Trace Expression)
    (hrun : CoreStepStarE π φ
      (.stmt (Stmt.block "" [Stmt.cmd (CmdExt.cmd (Cmd.assert l e md))] #[])
        ⟨σ_entry, fac, false⟩) emitted (.terminal ρ')) :
    ρ'.store = σ_entry := by
  obtain ⟨ρ_inner, hinner, hρ'⟩ :=
    stmt_block_reaches_doneE (P := Expression) (EvalCmd := EvalCommandE π φ)
      (extendFactory := EvalPureFunc φ) (.inl hrun)
  have hbody_store : ρ_inner.store = σ_entry := by
    rcases hinner with hterm | ⟨lbl, hexit⟩
    · rcases stmts_cons_headE (EvalCmd := EvalCommandE π φ)
        (extendFactory := EvalPureFunc φ) hterm with ⟨hcfg, _⟩ | hseq
      · exact absurd hcfg (by simp)
      · rcases seq_run_decomposeE (EvalCmd := EvalCommandE π φ)
          (extendFactory := EvalPureFunc φ) hseq with
          ⟨_, hcfg, _⟩ | ⟨ρ₁, tr₁, tr₂, _htr, hhead, htail⟩ | ⟨_, _, hcfg, _⟩
        · exact absurd hcfg (by simp)
        · obtain ⟨_, htailcfg⟩ := stmts_nil_runE (EvalCmd := EvalCommandE π φ)
            (extendFactory := EvalPureFunc φ) htail
          have hρ_inner : ρ_inner = ρ₁ := by
            rcases htailcfg with h | h
            · exact absurd h (by simp)
            · exact Config.terminal.injEq _ _ ▸ h
          cases hhead with
          | step _ _ _ _ _ hstep hrest =>
            cases hstep with
            | step_cmd hcmd =>
              obtain ⟨hz, _⟩ := stepStmtStarE_from_terminal
                (EvalCmd := EvalCommandE π φ) (extendFactory := EvalPureFunc φ) hrest
              cases hcmd with
              | cmd_sem hbase =>
                cases hbase with
                | eval_assert =>
                  rw [hρ_inner]
                  injection hz with hz'
                  rw [hz']
            | step_admin hadmin =>
              cases hadmin with
              | step_cmd hfalse => exact hfalse.elim
        · exact absurd hcfg (by simp)
    · rcases stmts_cons_headE (EvalCmd := EvalCommandE π φ)
        (extendFactory := EvalPureFunc φ) hexit with ⟨hcfg, _⟩ | hseq
      · exact absurd hcfg (by simp)
      · rcases seq_run_decomposeE (EvalCmd := EvalCommandE π φ)
          (extendFactory := EvalPureFunc φ) hseq with
          ⟨_, hcfg, _⟩ | ⟨ρ₁, tr₁, tr₂, _htr, hhead, htail⟩ | ⟨lbl2, ρ₁, hcfg, hhead⟩
        · exact absurd hcfg (by simp)
        · obtain ⟨_, htailcfg⟩ := stmts_nil_runE (EvalCmd := EvalCommandE π φ)
            (extendFactory := EvalPureFunc φ) htail
          rcases htailcfg with h | h
          · exact absurd h (by simp)
          · exact absurd h (by simp)
        · cases hhead with
          | step _ _ _ _ _ hstep hrest =>
            cases hstep with
            | step_cmd hcmd =>
              obtain ⟨hz, _⟩ := stepStmtStarE_from_terminal
                (EvalCmd := EvalCommandE π φ) (extendFactory := EvalPureFunc φ) hrest
              exact absurd hz (by simp)
            | step_admin hadmin =>
              cases hadmin with
              | step_cmd hfalse => exact hfalse.elim
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
    {σ σ' : CoreStore} {k : Expression.Ident} {v : Expression.Expr}
    (hupd : Imperative.UpdateState Expression σ k v σ') :
    Imperative.invStoresExcept σ (Imperative.projectStore σ σ') [k] := by
  cases hupd with
  | update hv' hv hother =>
    refine invStoresExcept_singleton_of_agree_off (fun y hy => ?_)
    unfold Imperative.projectStore
    by_cases hs : (σ y).isSome
    · rw [if_pos hs]; exact (hother y hy).symm
    · rw [if_neg hs]; exact Option.not_isSome_iff_eq_none.mp hs

/-- **A one-`set` structured body respects the write set `[x]`.** Every completed
event run of `{ x := e }` from `σ_entry` leaves a procedure-exit store that agrees
with `σ_entry` everywhere except `x`. -/
theorem setBodyE_frame
    (π : String → Option Procedure)
    (φ : Expression.Factory → PureFunc Expression → Expression.Factory)
    (x : Expression.Ident) (e : Expression.Expr) (md : MetaData Expression)
    (σ_entry : CoreStore) (fac : Expression.Factory) (ρ' : Env Expression)
    (emitted : Trace Expression)
    (hrun : CoreStepStarE π φ
      (.stmt (Stmt.block "" [Stmt.cmd (CmdExt.cmd (Cmd.set x (.det e) md))] #[])
        ⟨σ_entry, fac, false⟩) emitted (.terminal ρ')) :
    Imperative.invStoresExcept σ_entry ρ'.store [x] := by
  obtain ⟨ρ_inner, hinner, hρ'⟩ :=
    stmt_block_reaches_doneE (P := Expression) (EvalCmd := EvalCommandE π φ)
      (extendFactory := EvalPureFunc φ) (.inl hrun)
  rw [hρ']
  show Imperative.invStoresExcept σ_entry
    (Imperative.projectStore σ_entry ρ_inner.store) [x]
  -- The single-command `UpdateState` that produced `ρ_inner.store`.
  rcases hinner with hterm | ⟨lbl, hexit⟩
  · rcases stmts_cons_headE (EvalCmd := EvalCommandE π φ)
      (extendFactory := EvalPureFunc φ) hterm with ⟨hcfg, _⟩ | hseq
    · exact absurd hcfg (by simp)
    · rcases seq_run_decomposeE (EvalCmd := EvalCommandE π φ)
        (extendFactory := EvalPureFunc φ) hseq with
        ⟨_, hcfg, _⟩ | ⟨ρ₁, tr₁, tr₂, _htr, hhead, htail⟩ | ⟨_, _, hcfg, _⟩
      · exact absurd hcfg (by simp)
      · obtain ⟨_, htailcfg⟩ := stmts_nil_runE (EvalCmd := EvalCommandE π φ)
          (extendFactory := EvalPureFunc φ) htail
        have hρ_inner : ρ_inner = ρ₁ := by
          rcases htailcfg with h | h
          · exact absurd h (by simp)
          · exact Config.terminal.injEq _ _ ▸ h
        cases hhead with
        | step _ _ _ _ _ hstep hrest =>
          cases hstep with
          | step_cmd hcmd =>
            obtain ⟨hz, _⟩ := stepStmtStarE_from_terminal
              (EvalCmd := EvalCommandE π φ) (extendFactory := EvalPureFunc φ) hrest
            cases hcmd with
            | cmd_sem hbase =>
              cases hbase with
              | eval_set heval hupd hwfv =>
                subst hρ_inner
                injection hz with hz'
                subst hz'
                exact invStoresExcept_projectStore_of_update hupd
          | step_admin hadmin =>
            cases hadmin with
            | step_cmd hfalse => exact hfalse.elim
      · exact absurd hcfg (by simp)
  · rcases stmts_cons_headE (EvalCmd := EvalCommandE π φ)
      (extendFactory := EvalPureFunc φ) hexit with ⟨hcfg, _⟩ | hseq
    · exact absurd hcfg (by simp)
    · rcases seq_run_decomposeE (EvalCmd := EvalCommandE π φ)
        (extendFactory := EvalPureFunc φ) hseq with
        ⟨_, hcfg, _⟩ | ⟨ρ₁, tr₁, tr₂, _htr, hhead, htail⟩ | ⟨lbl2, ρ₁, hcfg, hhead⟩
      · exact absurd hcfg (by simp)
      · obtain ⟨_, htailcfg⟩ := stmts_nil_runE (EvalCmd := EvalCommandE π φ)
          (extendFactory := EvalPureFunc φ) htail
        rcases htailcfg with h | h
        · exact absurd h (by simp)
        · exact absurd h (by simp)
      · cases hhead with
        | step _ _ _ _ _ hstep hrest =>
          cases hstep with
          | step_cmd hcmd =>
            obtain ⟨hz, _⟩ := stepStmtStarE_from_terminal
              (EvalCmd := EvalCommandE π φ) (extendFactory := EvalPureFunc φ) hrest
            exact absurd hz (by simp)
          | step_admin hadmin =>
            cases hadmin with
            | step_cmd hfalse => exact hfalse.elim

/-! ## Properties of CoreStep and CoreStepStar. -/

/-- `CoreStepStar` implies the generic `StepStmtStar` (i.e. `ReflTrans`). -/
theorem CoreStepStar_to_StepStmtStar
    {π : String → Option Procedure}
    {φ : Expression.Factory → PureFunc Expression → Expression.Factory}
    {c c' : Imperative.Config Expression Command}
    (h : CoreStepStar π φ c c') :
    Imperative.StepStmtStar Expression (EvalCommand π φ) (EvalPureFunc φ) c c' :=
  match h with
  | .refl => .refl _
  | .step hstep hrest => .step _ _ _ hstep (CoreStepStar_to_StepStmtStar hrest)

/-- The generic `StepStmtStar` implies `CoreStepStar`. -/
theorem StepStmtStar_to_CoreStepStar
    {π : String → Option Procedure}
    {φ : Expression.Factory → PureFunc Expression → Expression.Factory}
    {c c' : Imperative.Config Expression Command} :
    Imperative.StepStmtStar Expression (EvalCommand π φ) (EvalPureFunc φ) c c' →
    CoreStepStar π φ c c' := by
  intro H
  induction H with
  | refl => exact .refl
  | step _ _ _ hstep _ ih => exact .step hstep ih

/-- Manual induction principle for `CoreStepStar` (the `induction` tactic does
    not support mutual inductives). -/
theorem CoreStepStar_rec
    {π : String → Option Procedure}
    {φ : Expression.Factory → PureFunc Expression → Expression.Factory}
    {motive : CoreConfig → CoreConfig → Prop}
    (h_refl : ∀ c, motive c c)
    (h_step : ∀ c₁ c₂ c₃, CoreStep π φ c₁ c₂ →
      CoreStepStar π φ c₂ c₃ → motive c₂ c₃ → motive c₁ c₃)
    {c₁ c₂ : CoreConfig}
    (h : CoreStepStar π φ c₁ c₂) : motive c₁ c₂ := by
  suffices h_gen : ∀ c₁ c₂,
      Imperative.StepStmtStar Expression (EvalCommand π φ) (EvalPureFunc φ) c₁ c₂ →
      motive c₁ c₂ by
    exact h_gen _ _ (CoreStepStar_to_StepStmtStar h)
  intro c₁ c₂ h'
  induction h' with
  | refl => exact h_refl _
  | step _ _ _ hstep hrest ih =>
    exact h_step _ _ _ hstep (StepStmtStar_to_CoreStepStar hrest) ih

/-- `CoreStepStar` is transitive. -/
theorem CoreStepStar_trans
    {π : String → Option Procedure}
    {φ : Expression.Factory → PureFunc Expression → Expression.Factory}
    {c₁ c₂ c₃ : CoreConfig}
    (h₁ : CoreStepStar π φ c₁ c₂)
    (h₂ : CoreStepStar π φ c₂ c₃) :
    CoreStepStar π φ c₁ c₃ :=
  StepStmtStar_to_CoreStepStar
    (ReflTrans_Transitive _ _ _ _
      (CoreStepStar_to_StepStmtStar h₁)
      (CoreStepStar_to_StepStmtStar h₂))

/-- Lift `seq_inner_star` from `StepStmtStar` to `CoreStepStar`. -/
theorem core_seq_inner_star
    {π : String → Option Procedure}
    {φ : Expression.Factory → PureFunc Expression → Expression.Factory}
    (inner inner' : CoreConfig) (ss : List Statement)
    (h : CoreStepStar π φ inner inner') :
    CoreStepStar π φ (.seq inner ss) (.seq inner' ss) :=
  StepStmtStar_to_CoreStepStar
    (seq_inner_star Expression (EvalCommand π φ) (EvalPureFunc φ) inner inner' ss
      (CoreStepStar_to_StepStmtStar h))

/-- Lift `block_inner_star` from `StepStmtStar` to `CoreStepStar`. -/
theorem core_block_inner_star
    {π : String → Option Procedure}
    {φ : Expression.Factory → PureFunc Expression → Expression.Factory}
    (inner inner' : CoreConfig) (label : Option String) (σ_parent : SemanticStore Expression)
    (f_parent : Expression.Factory)
    (h : CoreStepStar π φ inner inner') :
    CoreStepStar π φ (.block label σ_parent f_parent inner) (.block label σ_parent f_parent inner') :=
  StepStmtStar_to_CoreStepStar
    (block_inner_star Expression (EvalCommand π φ) (EvalPureFunc φ) inner inner' label σ_parent f_parent
      (CoreStepStar_to_StepStmtStar h))

/-- Lift `seq_reaches_terminal` from `StepStmtStar` to `CoreStepStar`. -/
theorem core_seq_reaches_terminal
    {π : String → Option Procedure}
    {φ : Expression.Factory → PureFunc Expression → Expression.Factory}
    {inner : CoreConfig} {ss : List Statement} {ρ' : Env Expression}
    (hstar : CoreStepStar π φ (.seq inner ss) (.terminal ρ')) :
    ∃ ρ₁, CoreStepStar π φ inner (.terminal ρ₁) ∧
      CoreStepStar π φ (.stmts ss ρ₁) (.terminal ρ') := by
  have h := seq_reaches_terminal Expression (EvalCommand π φ) (EvalPureFunc φ)
    (CoreStepStar_to_StepStmtStar hstar)
  obtain ⟨ρ₁, h₁, h₂⟩ := h
  exact ⟨ρ₁, StepStmtStar_to_CoreStepStar h₁, StepStmtStar_to_CoreStepStar h₂⟩


/-! ## Well-formed evaluator extension -/

variable (π : String → Option Procedure)
variable (φ : Expression.Factory → PureFunc Expression → Expression.Factory)

/-! ### Config-level WF predicate for Core

`step_block_done`/`exit_match`/`exit_mismatch` restore `eval := e_parent`, so
preservation of WF along a trace requires WF of every captured `e_parent`
snapshot in addition to WF of the inner eval. -/

@[expose] def CoreConfig.wfEval : CoreConfig → Prop
  | .stmt _ ρ => WellFormedSemanticEval (P := Expression) ρ.factory
  | .stmts _ ρ => WellFormedSemanticEval (P := Expression) ρ.factory
  | .terminal ρ => WellFormedSemanticEval (P := Expression) ρ.factory
  | .exiting _ ρ => WellFormedSemanticEval (P := Expression) ρ.factory
  | .block _ _ f_parent inner =>
    WellFormedSemanticEval (P := Expression) f_parent ∧ CoreConfig.wfEval inner
  | .seq inner _ => CoreConfig.wfEval inner

private theorem core_step_preserves_cfg_wfEval
    (h_wf_ext : Imperative.WFFactoryExtension Expression (EvalPureFunc φ))
    (c₁ c₂ : CoreConfig)
    (hwf : c₁.wfEval)
    (hstep : CoreStep π φ c₁ c₂) :
    c₂.wfEval := by
  induction hstep with
  | step_cmd hcmd => cases hcmd with
    | cmd_sem _ | call_sem _ _ _ _ _ _ =>
        exact hwf
  | step_block | step_ite_true | step_ite_false | step_ite_nondet_true
  | step_ite_nondet_false | step_loop_enter | step_loop_nondet_enter => exact ⟨hwf, hwf⟩
  | step_block_done | step_block_exit_match | step_block_exit_mismatch => exact hwf.1
  | step_seq_inner _ ih => exact ih hwf
  | step_block_body hstep_inner ih =>
    exact ⟨hwf.1, ih hwf.2⟩
  | step_funcDecl => exact h_wf_ext.preserves_wfEval _ _ _ hwf
  | _ => exact hwf

private theorem CoreConfig.wfEval_implies_wfEval (cfg : CoreConfig) :
    cfg.wfEval → WellFormedSemanticEval (P := Expression) cfg.getEnv.factory := by
  induction cfg with
  | stmt | stmts | terminal | exiting => intro h; exact h
  | block _ _ _ inner ih => intro h; exact ih h.2
  | seq inner _ ih => intro h; exact ih h

private theorem core_star_preserves_cfg_wfEval
    (h_wf_ext : Imperative.WFFactoryExtension Expression (EvalPureFunc φ))
    {c₁ c₂ : CoreConfig}
    (hstar : CoreStepStar π φ c₁ c₂)
    (hwf : c₁.wfEval) :
    c₂.wfEval := by
  suffices ∀ (c₁ c₂ : CoreConfig),
      Imperative.StepStmtStar Expression (EvalCommand π φ) (EvalPureFunc φ) c₁ c₂ →
      c₁.wfEval → c₂.wfEval from
    this c₁ c₂ (CoreStepStar_to_StepStmtStar hstar) hwf
  intro c₁ c₂ hstar
  induction hstar with
  | refl => intro h; exact h
  | step _ _ _ hstep _ ih =>
    intro h; exact ih (core_step_preserves_cfg_wfEval π φ h_wf_ext _ _ h hstep)

/-- WF-bundle preservation starting from `.stmt s ρ`. -/
theorem core_wfEval_preserved_stmt
    (h_wf_ext : Imperative.WFFactoryExtension Expression (EvalPureFunc φ))
    {s : Statement} {ρ : Env Expression} {c₂ : CoreConfig}
    (hwf₀ : WellFormedSemanticEval (P := Expression) ρ.factory)
    (hstar : CoreStepStar π φ (.stmt s ρ) c₂) :
    WellFormedSemanticEval (P := Expression) c₂.getEnv.factory :=
  CoreConfig.wfEval_implies_wfEval _
    (core_star_preserves_cfg_wfEval π φ h_wf_ext hstar
      (show CoreConfig.wfEval (.stmt s ρ) from hwf₀))

/-- WF-bundle preservation starting from `.stmts ss ρ`. -/
theorem core_wfEval_preserved_stmts
    (h_wf_ext : Imperative.WFFactoryExtension Expression (EvalPureFunc φ))
    {ss : List Statement} {ρ : Env Expression} {c₂ : CoreConfig}
    (hwf₀ : WellFormedSemanticEval (P := Expression) ρ.factory)
    (hstar : CoreStepStar π φ (.stmts ss ρ) c₂) :
    WellFormedSemanticEval (P := Expression) c₂.getEnv.factory :=
  CoreConfig.wfEval_implies_wfEval _
    (core_star_preserves_cfg_wfEval π φ h_wf_ext hstar
      (show CoreConfig.wfEval (.stmts ss ρ) from hwf₀))

/-! ## Store-domain preservation along a Core run

Two dual facts about a terminating Core run, each an instantiation of the
`Q`-keyed engine in `Strata.DL.Imperative.StmtSemanticsProps` at `EvalCommand`
(the engine's non-`step_cmd` cases are purely structural, so only the
command-level fact below is Core-specific):

* nothing already defined becomes undefined — `core_stmts_preserves_isSome`;
* nothing outside the run's `definedVars` becomes defined —
  `core_block_run_terminal_preserves_none_of_not_definedVars`.

Together they pin the store domain after a run, which is what a compositional
Hoare rule needs in order to re-establish a block-level well-formedness gate on
the tail of a statement list (see `Strata.Languages.Core.Logic.Hoare`). -/

/-- `UpdateState` cannot define a slot that was undefined: it requires its
    target to already hold a value, and leaves every other slot unchanged. -/
private theorem updateState_preserves_none
    {σ σ' : SemanticStore Expression} {x : Expression.Ident} {v : Expression.Expr}
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
    {σ σ' : SemanticStore Expression} {x : Expression.Ident} {v : Expression.Expr}
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
    {vs : List Expression.Expr}
    (h : UpdateStates σ xs vs σ') :
    ∀ y, σ y = none → σ' y = none := by
  induction h with
  | update_none => exact fun _ hy => hy
  | update_some hupd _ ih =>
    exact fun y hy => ih y (updateState_preserves_none hupd y hy)

/-- Pointwise lift of `updateState_preserves_isSome` along a whole write-back. -/
private theorem updateStates_preserves_isSome
    {σ σ' : SemanticStore Expression} {xs : List Expression.Ident}
    {vs : List Expression.Expr}
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
    {vs : List Expression.Expr}
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

/-- An `EvalCommand` step only defines the slots the command itself declares; a `call`
    declares nothing. -/
theorem evalCommand_preserves_none_of_not_def
    {f : Expression.Factory} {σ σ' : SemanticStore Expression} {c : Command}
    {hf : Bool} {y : Expression.Ident}
    (h_eval : EvalCommand π φ f σ c σ' hf)
    (h_none : σ y = none)
    (h_not_def : y ∉ HasVarsImp.definedVars (P := Expression) c false) :
    σ' y = none := by
  cases h_eval with
  | cmd_sem h =>
    exact evalCmd_preserves_none_of_not_def h h_none
      (by simpa [HasVarsImp.definedVars, Command.definedVars] using h_not_def)
  | call_sem _ _ _ _ _ hexit =>
    unfold CallExit at hexit
    obtain ⟨_, _, hupd⟩ := hexit
    exact updateStates_preserves_none hupd y h_none

/-- Event-trace analogue of `evalCommand_preserves_none_of_not_def`: an
    `EvalCommandE` step preserves a `none` slot it does not declare. -/
theorem evalCommandE_preserves_none_of_not_def
    {f : Expression.Factory} {σ σ' : SemanticStore Expression} {c : Command}
    {emitted : Imperative.Trace Expression} {y : Expression.Ident}
    (h_eval : EvalCommandE π φ f σ c σ' emitted)
    (h_none : σ y = none)
    (h_not_def : y ∉ HasVarsImp.definedVars (P := Expression) c false) :
    σ' y = none := by
  cases h_eval with
  | cmd_sem h =>
    exact Imperative.evalCmdE_preserves_none_of_not_def h h_none
      (by simpa [HasVarsImp.definedVars, Command.definedVars] using h_not_def)
  | call_sem _ _ _ hexit =>
    unfold CallExit at hexit
    obtain ⟨_, _, hupd⟩ := hexit
    exact updateStates_preserves_none hupd y h_none

/-- An `EvalCommand` step never undefines a store slot. -/
theorem evalCommand_preserves_isSome
    {f : Expression.Factory} {σ σ' : SemanticStore Expression} {c : Command}
    {hf : Bool} {y : Expression.Ident}
    (h_eval : EvalCommand π φ f σ c σ' hf)
    (h_some : (σ y).isSome = true) :
    (σ' y).isSome = true := by
  cases h_eval with
  | cmd_sem h => exact EvalCmd_preserves_isSome h h_some
  | call_sem _ _ _ _ _ hexit =>
    unfold CallExit at hexit
    obtain ⟨_, _, hupd⟩ := hexit
    exact updateStates_preserves_isSome hupd y h_some

/-- An `EvalCommand` step leaves a store that holds only values. -/
theorem evalCommand_storeWellDefined
    {fac : Expression.Factory} {σ σ' : CoreStore} {c : Command} {fl : Bool}
    (h : EvalCommand π φ fac σ c σ' fl)
    (hsv : Imperative.WellFormedStore σ fac) :
    Imperative.WellFormedStore σ' fac := by
  cases h with
  | cmd_sem hcmd =>
    -- Core's `WellFormedSemanticEvalVal` holds at every factory, so nothing has to
    -- be threaded through the run.
    exact Imperative.evalCmd_storeWellDefined
      (coreEvaluator_WellFormedSemanticEvalVal fac) hcmd hsv
  | call_sem _ _ _ _ _ hexit =>
    unfold CallExit at hexit
    obtain ⟨_, hread, hupd⟩ := hexit
    exact updateStates_preserves_wellFormedStore hupd
      (ReadValues.all_values hread) hsv

/-- Core analogue of `stmts_preserves_isSome`: a slot defined at the start of a
    terminating `.stmts` run is still defined at the end. -/
theorem core_stmts_preserves_isSome
    {y : Expression.Ident} {ss : Statements} {ρ ρ' : Env Expression}
    (h_run : CoreStepStar π φ (.stmts ss ρ) (.terminal ρ'))
    (h_some : (ρ.store y).isSome = true) :
    (ρ'.store y).isSome = true :=
  Config.varsDefined_star_of (evalCmd := EvalCommand π φ)
    (extendFactory := EvalPureFunc φ)
    (fun he hs => evalCommand_preserves_isSome π φ he hs)
    (CoreStepStar_to_StepStmtStar h_run)
    (show Config.varDefined y (.stmts ss ρ) from fun _ hz => hz ▸ h_some) y rfl

/-- Core analogue of `block_run_terminal_preserves_none_of_not_definedVars`: a
    terminating `.stmts bss` run leaves `store y = none` for every
    `y ∉ Block.definedVars bss false`. -/
theorem core_block_run_terminal_preserves_none_of_not_definedVars
    {y : Expression.Ident} {bss : Statements} {ρ ρ' : Env Expression}
    (h_y_not_def : y ∉ Block.definedVars (P := Expression) (C := Command) bss false)
    (h_none : ρ.store y = none)
    (h_run : CoreStepStar π φ (.stmts bss ρ) (.terminal ρ')) :
    ρ'.store y = none :=
  Config.varsUndefinedThroughout_star_of (Q := (· = y)) (evalCmd := EvalCommand π φ)
    (extendFactory := EvalPureFunc φ)
    (fun he hn hnd => evalCommand_preserves_none_of_not_def π φ he hn hnd)
    (CoreStepStar_to_StepStmtStar h_run)
    (by rintro z rfl; exact ⟨h_none, all_not_mem_definedVars_of_block h_y_not_def⟩) y rfl

/-- Scope-aware Core store-domain bound: a terminating run of `s` newly defines
    only `Stmt.definedVars s true`.  Unlike
    `core_block_run_terminal_preserves_none_of_not_definedVars` this permits `s`
    to `init` `y` inside a nested scope, since leaving that scope projects the
    inner store through the parent's. -/
theorem core_stmt_run_terminal_preserves_none_of_not_definedVars_true
    {y : Expression.Ident} {s : Statement} {ρ ρ' : Env Expression}
    (h_y_not_def : y ∉ Stmt.definedVars (P := Expression) (C := Command) s true)
    (h_none : ρ.store y = none)
    (h_run : CoreStepStar π φ (.stmt s ρ) (.terminal ρ')) :
    ρ'.store y = none :=
  Config.varsUndefinedScoped_star_of (Q := (· = y)) (evalCmd := EvalCommand π φ)
    (extendFactory := EvalPureFunc φ)
    (fun he hn hnd => evalCommand_preserves_none_of_not_def π φ he hn hnd)
    (CoreStepStar_to_StepStmtStar h_run)
    (by rintro z rfl; exact ⟨h_none, h_y_not_def⟩) y rfl

/-- A terminating statement run never undefines a store slot: whatever was defined
    on entry is still defined at the terminal environment.  `.stmt` variant of
    `core_stmts_preserves_isSome`. -/
private theorem core_stmt_preserves_isSome
    {y : Expression.Ident} {s : Statement} {ρ ρ' : Env Expression}
    (h_run : CoreStepStar π φ (.stmt s ρ) (.terminal ρ'))
    (h_some : (ρ.store y).isSome = true) :
    (ρ'.store y).isSome = true :=
  Config.varsDefined_star_of (evalCmd := EvalCommand π φ)
    (extendFactory := EvalPureFunc φ)
    (fun he hs => evalCommand_preserves_isSome π φ he hs)
    (CoreStepStar_to_StepStmtStar h_run)
    (show Config.varDefined y (.stmt s ρ) from fun _ hz => hz ▸ h_some) y rfl

/-- Core lift of `evalCmd_definedVars_isSome`.  `Command.definedVars (.call ..) = []`
    — a procedure call declares nothing, writing its results back through
    `UpdateStates` — so that case is vacuous. -/
private theorem evalCommand_definedVars_isSome
    {f : Expression.Factory} {σ σ' : SemanticStore Expression} {c : Command}
    {hf : Bool} {y : Expression.Ident}
    (h_eval : EvalCommand π φ f σ c σ' hf)
    (h_def : y ∈ HasVarsImp.definedVars (P := Expression) c true) :
    (σ' y).isSome = true := by
  cases h_eval with
  | cmd_sem h =>
    exact evalCmd_definedVars_isSome h
      (by simpa [HasVarsImp.definedVars, Command.definedVars] using h_def)
  | call_sem => simp [HasVarsImp.definedVars, Command.definedVars] at h_def

/-- **Exact store domain after a terminating statement run.**  A terminating run
    of `s` from `ρ` leaves exactly `dom(ρ.store) ∪ Stmt.definedVars s true`
    defined.

    Equality, rather than either inclusion, is what `Block.defUseWellFormed` needs: it
    uses its definedness predicate in both directions — reads and writes must be
    defined, and `init` targets must *not* be. -/
theorem core_stmt_run_terminal_store_isSome_eq
    {s : Statement} {ρ ρ' : Env Expression}
    (h_run : CoreStepStar π φ (.stmt s ρ) (.terminal ρ')) (n : Expression.Ident) :
    (ρ'.store n).isSome
      = ((ρ.store n).isSome ||
          decide (n ∈ Stmt.definedVars (P := Expression) (C := Command) s true)) := by
  by_cases hd : n ∈ Stmt.definedVars (P := Expression) (C := Command) s true
  · -- `Stmt.definedVars _ true` is nonempty only for `.cmd`, whose run is one step.
    simp only [hd, decide_true, Bool.or_true]
    match s with
    | .cmd c =>
      cases h_run with
      | step hstep hrest =>
        cases hstep with
        | step_cmd h_eval =>
          cases hrest with
          | refl =>
            simp only [Stmt.definedVars] at hd
            exact evalCommand_definedVars_isSome π φ h_eval hd
          | step hstep' _ => exact nomatch hstep'
    | .block .. | .ite .. | .loop .. | .exit .. | .funcDecl .. | .typeDecl .. =>
      simp [Stmt.definedVars] at hd
  · simp only [hd, decide_false, Bool.or_false]
    by_cases hs : (ρ.store n).isSome = true
    · rw [hs, core_stmt_preserves_isSome π φ h_run hs]
    · have hnone : ρ.store n = none := by
        cases h : ρ.store n with
        | none => rfl
        | some v => rw [h] at hs; simp at hs
      rw [hnone] at hs
      rw [core_stmt_run_terminal_preserves_none_of_not_definedVars_true π φ hd hnone h_run,
        hnone]

/-! ### Event-trace store-domain characterization

Event-trace (`StepStmtStarE` / `EvalCommandE`) analogues of the store-domain
lemmas above, needed to re-establish `BlockInitEnvWF` on the tail of a statement
list after an event-native run.  `EvalCommandE` base commands are the
event-native `EvalCmdE`; a `call` emits `[]` and reuses the failure-flag
`EvalCommand`, so the call cases delegate to the failure-flag results. -/

/-- An `EvalCommandE` step never undefines a store slot that was already
defined. -/
theorem evalCommandE_preserves_isSome
    {f : Expression.Factory} {σ σ' : SemanticStore Expression} {c : Command}
    {emitted : Imperative.Trace Expression} {y : Expression.Ident}
    (h_eval : EvalCommandE π φ f σ c σ' emitted)
    (h_some : (σ y).isSome = true) :
    (σ' y).isSome = true := by
  cases h_eval with
  | cmd_sem h => exact Imperative.evalCmdE_preserves_isSome h h_some
  | call_sem _ _ _ hexit =>
    unfold CallExit at hexit
    obtain ⟨_, _, hupd⟩ := hexit
    exact updateStates_preserves_isSome hupd y h_some

/-- An `EvalCommandE` step preserves the property that every store binding is
a value. -/
theorem evalCommandE_storeWellDefined
    {fac : Expression.Factory} {σ σ' : CoreStore} {c : Command}
    {emitted : Imperative.Trace Expression}
    (h : EvalCommandE π φ fac σ c σ' emitted)
    (hsv : Imperative.WellFormedStore σ fac) :
    Imperative.WellFormedStore σ' fac := by
  cases h with
  | cmd_sem hcmd =>
    exact Imperative.evalCmdE_storeWellDefined
      (coreEvaluator_WellFormedSemanticEvalVal fac) hcmd hsv
  | call_sem _ _ _ hexit =>
    unfold CallExit at hexit
    obtain ⟨_, hread, hupd⟩ := hexit
    exact updateStates_preserves_wellFormedStore hupd
      (ReadValues.all_values hread) hsv

/-- Event analogue of `evalCommand_definedVars_isSome`: a `call` declares
nothing, so that case is vacuous. -/
private theorem evalCommandE_definedVars_isSome
    {f : Expression.Factory} {σ σ' : SemanticStore Expression} {c : Command}
    {emitted : Imperative.Trace Expression} {y : Expression.Ident}
    (h_eval : EvalCommandE π φ f σ c σ' emitted)
    (h_def : y ∈ HasVarsImp.definedVars (P := Expression) c true) :
    (σ' y).isSome = true := by
  cases h_eval with
  | cmd_sem h =>
    exact Imperative.evalCmdE_definedVars_isSome h
      (by simpa [HasVarsImp.definedVars, Command.definedVars] using h_def)
  | call_sem => simp [HasVarsImp.definedVars, Command.definedVars] at h_def

/-- A store slot defined at the start of a terminating event-native `.stmt`
run remains defined at the end. -/
private theorem core_stmt_preserves_isSomeE
    {y : Expression.Ident} {s : Statement} {ρ ρ' : Env Expression}
    {tr : Imperative.Trace Expression}
    (h_run : CoreStepStarE π φ
      (.stmt s ρ) tr (.terminal ρ'))
    (h_some : (ρ.store y).isSome = true) :
    (ρ'.store y).isSome = true :=
  Config.varsDefined_star_ofE
    (fun he hs => evalCommandE_preserves_isSome π φ he hs)
    h_run
    (show Config.varDefined y (.stmt s ρ) from fun _ hz => hz ▸ h_some) y rfl

/-- Event analogue of `core_stmts_preserves_isSome`: a slot defined at the start
of a terminating event-native `.stmts` run is still defined at the end. -/
theorem core_stmts_preserves_isSomeE
    {y : Expression.Ident} {ss : Statements} {ρ ρ' : Env Expression}
    {tr : Imperative.Trace Expression}
    (h_run : CoreStepStarE π φ
      (.stmts ss ρ) tr (.terminal ρ'))
    (h_some : (ρ.store y).isSome = true) :
    (ρ'.store y).isSome = true :=
  Config.varsDefined_star_ofE
    (fun he hs => evalCommandE_preserves_isSome π φ he hs)
    h_run
    (show Config.varDefined y (.stmts ss ρ) from fun _ hz => hz ▸ h_some) y rfl

/-- A store slot that starts undefined and is not defined by the statement
remains undefined after a terminating event-native `.stmt` run. -/
theorem core_stmt_run_terminal_preserves_none_of_not_definedVars_trueE
    {y : Expression.Ident} {s : Statement} {ρ ρ' : Env Expression}
    {tr : Imperative.Trace Expression}
    (h_y_not_def : y ∉ Stmt.definedVars (P := Expression) (C := Command) s true)
    (h_none : ρ.store y = none)
    (h_run : CoreStepStarE π φ
      (.stmt s ρ) tr (.terminal ρ')) :
    ρ'.store y = none :=
  Config.varsUndefinedScoped_star_ofE
    (fun he hn hnd => evalCommandE_preserves_none_of_not_def π φ he hn hnd)
    h_run
    (by rintro z rfl; exact ⟨h_none, h_y_not_def⟩) y rfl

/-- After a terminating event-native `.stmt` run, a store slot is defined
exactly when it was defined initially or the statement defines it. -/
theorem core_stmt_run_terminal_store_isSome_eqE
    {s : Statement} {ρ ρ' : Env Expression} {tr : Imperative.Trace Expression}
    (h_run : CoreStepStarE π φ
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
          exact evalCommandE_definedVars_isSome π φ h_eval hd
        | step_admin hadmin => cases hadmin with | step_cmd hfalse => exact hfalse.elim
    | .block .. | .ite .. | .loop .. | .exit .. | .funcDecl .. | .typeDecl .. =>
      simp [Stmt.definedVars] at hd
  · simp only [hd, decide_false, Bool.or_false]
    by_cases hs : (ρ.store n).isSome = true
    · rw [hs, core_stmt_preserves_isSomeE π φ h_run hs]
    · have hnone : ρ.store n = none := by
        cases h : ρ.store n with
        | none => rfl
        | some v => rw [h] at hs; simp at hs
      rw [hnone] at hs
      rw [core_stmt_run_terminal_preserves_none_of_not_definedVars_trueE π φ hd hnone h_run,
        hnone]

/-! ## projectStore and expression evaluation -/

/-- If an expression evaluates in the projected store, it evaluates identically
    in the full store. The projected store only removes variables, and expression
    evaluation depends only on the variables it references. The `hdom` hypothesis
    ensures all free variables of `e` are bound in the projected store. -/
theorem eval_projectStore_to_full
    {f : Expression.Factory} {σ₀ σ : SemanticStore Expression}
    {e : Expression.Expr} {v : Expression.Expr}
    (h_eval : Expression.eval f (projectStore σ₀ σ) e = some v)
    (h_wfStore : WellFormedStore σ f)
    (hWF : Lambda.FactoryWF f)
    (hClosed : Lambda.FactoryClosed f)
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
  rw [← coreEvaluator_WellFormedSemanticEvalExprCongr f hWF hClosed e _ _ h_wfStoreProj h_wfStore h_agree]
  exact h_eval

/-! ## Assert-only blocks preserve store -/

theorem stmts_allAssert_preserves_store
    (ss : List Statement) (ρ ρ' : Env Expression)
    (h_all : ∀ s ∈ ss, ∃ l e md, s = Statement.assert l e md)
    (hterm : CoreStepStar π φ (.stmts ss ρ) (.terminal ρ')) :
    ρ'.store = ρ.store := by
  induction ss generalizing ρ with
  | nil =>
    cases hterm with
    | step h_step h_rest => cases h_step with
      | step_stmts_nil => cases h_rest with
        | refl => rfl
        | step h _ => exact nomatch h
  | cons s rest ih =>
    have ⟨l, e, md, h_eq⟩ := h_all s (.head _)
    subst h_eq
    cases hterm with
    | step h_step h_rest => cases h_step with
      | step_stmts_cons =>
        have ⟨ρ₁, h_s, h_r⟩ := core_seq_reaches_terminal h_rest
        have h_store₁ : ρ₁.store = ρ.store := by
          suffices h_gen : ∀ (c₁ c₂ : CoreConfig),
              CoreStepStar π φ c₁ c₂ →
              c₁ = .stmt (Statement.assert l e md) ρ →
              c₂ = .terminal ρ₁ →
              ρ₁.store = ρ.store by
            exact h_gen _ _ h_s rfl rfl
          intro c₁ c₂ hstar heq₁ heq₂
          subst heq₁
          cases hstar with
          | refl => exact nomatch heq₂
          | step hstep hrest₂ =>
            cases hstep with
            | step_cmd hcmd =>
              cases hcmd with
              | cmd_sem heval =>
                cases heval with
                | eval_assert_pass =>
                  cases hrest₂ with
                  | refl => simp at heq₂ ⊢; exact heq₂ ▸ rfl
                  | step h _ => exact nomatch h
                | eval_assert_fail =>
                  cases hrest₂ with
                  | refl => simp at heq₂ ⊢; exact heq₂ ▸ rfl
                  | step h _ => exact nomatch h
        exact (ih ρ₁ (fun s' hs' => h_all s' (.tail _ hs')) h_r).trans h_store₁

/-! ## hasFailure preservation (Core-specific)

    `core_noFailure_preserved` reduces to the abstract Imperative
    `step_preserves_noFailure` applied to each step of the multi-step
    derivation, with `coreIsAtAssert` playing the role of the
    `IsAtAssert` parameter. -/

private theorem coreIsAtAssert_seq_of_inner
    {inner : CoreConfig} {ss a}
    (h : coreIsAtAssert inner a) : coreIsAtAssert (.seq inner ss) a := h

private theorem coreIsAtAssert_block_of_inner
    {label} {σ_parent} {e_parent} {inner : CoreConfig} {a}
    (h : coreIsAtAssert inner a) : coreIsAtAssert (.block label σ_parent e_parent inner) a := h

/-- If a command evaluation reports failure while every atomic call reports
    success, then the command is at an assertion whose expression evaluates to
    `ff`. -/
private theorem evalCommand_failure_implies_assert_ff
    {π : String → Option Procedure} {φ : Expression.Factory → PureFunc Expression → Expression.Factory}
    (hcalls : ∀ {fac σ n args md σ' failed},
      EvalCommand π φ fac σ (.call n args md) σ' failed → failed = false)
    {ρ : Env Expression} {c : Command} {σ'}
    (hcmd : EvalCommand π φ ρ.factory ρ.store c σ' true) :
    ∃ a : AssertId Expression,
      coreIsAtAssert (.stmt (.cmd c) ρ) a ∧
      Expression.eval ρ.factory ρ.store a.expr = some HasBool.ff := by
  cases c with
  | cmd base =>
    cases hcmd with
    | cmd_sem heval =>
      cases heval with
      | eval_assert_fail hff _ => exact ⟨⟨_, _⟩, ⟨rfl, rfl⟩, hff⟩
  | call _ _ _ =>
    have hfalse : true = false := hcalls hcmd
    simp at hfalse

/-- A failure-free Core configuration remains failure-free after a run when
    every reachable assertion evaluates to `tt` and every atomic call reports
    success. -/
theorem core_noFailure_preserved
    (c₁ c₂ : CoreConfig)
    (hvalid : ∀ (a : AssertId Expression) (cfg : CoreConfig),
      CoreStepStar π φ c₁ cfg →
      coreIsAtAssert cfg a →
      Expression.eval cfg.getEnv.factory cfg.getStore a.expr = some HasBool.tt)
    (hcalls : ∀ {fac σ n args md σ' failed},
      EvalCommand π φ fac σ (.call n args md) σ' failed → failed = false)
    (hf₀ : c₁.getEnv.hasFailure = Bool.false)
    (hstar : CoreStepStar π φ c₁ c₂) :
    c₂.getEnv.hasFailure = Bool.false := by
  suffices h_gen : ∀ c₁ c₂,
      (∀ (a : AssertId Expression) (cfg : CoreConfig),
        CoreStepStar π φ c₁ cfg →
        coreIsAtAssert cfg a →
        Expression.eval cfg.getEnv.factory cfg.getStore a.expr = some HasBool.tt) →
      c₁.getEnv.hasFailure = Bool.false →
      Imperative.StepStmtStar Expression (EvalCommand π φ) (EvalPureFunc φ) c₁ c₂ →
      c₂.getEnv.hasFailure = Bool.false from
    h_gen c₁ c₂ hvalid hf₀ (CoreStepStar_to_StepStmtStar hstar)
  intro c₁ c₂ hvalid hf₀ h
  induction h with
  | refl => exact hf₀
  | step _ mid _ hstep hrest ih =>
    exact ih
      (fun a cfg h hat => hvalid a _ (.step hstep h) hat)
      (Imperative.step_preserves_noFailure
        (P := Expression) (extendFactory := EvalPureFunc φ)
        coreIsAtAssert
        (evalCommand_failure_implies_assert_ff hcalls)
        coreIsAtAssert_seq_of_inner
        coreIsAtAssert_block_of_inner
        _ _
        (fun a cfg hr hat => hvalid a cfg (StepStmtStar_to_CoreStepStar hr) hat)
        hf₀ hstep)

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
    simp [Command.mapExpr]
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
  | funcDecl_case decl md => simp [Statement.mapExprs, Imperative.Stmt.mapExpr]
  | typeDecl_case tc md => simp [Statement.mapExprs, Imperative.Stmt.mapExpr]

theorem Statements.mapExprs_id (ss : Statements) : Statements.mapExprs id ss = ss := by
  exact list_mapExprs_id_of_forall (fun s _ => Statement.mapExprs_id s)

end Core

end -- public section
