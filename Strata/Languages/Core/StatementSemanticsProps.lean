/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.DL.Imperative.CmdSemantics
import Strata.DL.Imperative.StmtSemantics
import Strata.DL.Imperative.HasVars
import Strata.DL.Util.Nodup
import Strata.DL.Util.ListUtils
import Strata.Languages.Core.Procedure
import Strata.Languages.Core.Statement
import Strata.Languages.Core.OldExpressions
import Strata.Languages.Core.StatementSemantics
import Strata.Util.Tactics

/-! ## Theorems related to StatementSemantics -/

namespace Core
open Imperative

theorem InitStatesEmpty :
  @InitStates P σ [] [] σ' → σ = σ' := by
  intros H; cases H <;> simp

theorem UpdateStatesEmpty :
  @UpdateStates P σ [] [] σ' → σ = σ' := by
  intros H; cases H <;> simp

theorem HavocVarsEmpty :
  @HavocVars P σ [] σ' → σ = σ' := by
  intros H; cases H <;> simp

theorem InitVarsEmpty :
  @InitVars P σ [] σ' → σ = σ' := by
  intros H; cases H <;> simp

theorem TouchVarsEmpty :
  @TouchVars P σ [] σ' → σ = σ' := by
  intros H; cases H <;> simp

theorem EvalBlockEmpty' {P : PureExpr} {Cmd : Type} {EvalCmd : EvalCmdParam P Cmd}
  {extendEval : ExtendEval P}
  { σ σ': SemanticStore P } { δ δ' : SemanticEval P }
  [DecidableEq P.Ident]
  [HasVarsImp P (List (Stmt P Cmd))] [HasVarsImp P Cmd] [HasFvar P] [HasVal P] [HasBool P] [HasNot P] :
  EvalBlock P Cmd EvalCmd extendEval δ σ ([]: (List (Stmt P Cmd))) σ' δ' → σ = σ' := by
  intros H; cases H <;> simp

theorem EvalStatementsEmpty :
  EvalStatements π extendEval δ σ [] σ' δ' → σ = σ' := by
  intros H; cases H <;> simp

theorem EvalStatementsContractEmpty :
  EvalStatementsContract π extendEval δ σ [] σ' δ' → σ = σ' := by
  intros H; cases H <;> simp

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
    simp at Hlkup
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

theorem ReadValuesInjective :
  ReadValues σ ks vs →
  ReadValues σ ks vs' →
  vs = vs' := by
  intros Hrd1 Hrd2
  induction Hrd1 generalizing vs'
  case read_none =>
    cases Hrd2
    rfl
  case read_some Hrd Hrds ih =>
    cases Hrd2 with
    | read_some Hrd2 Hrds2 =>
    congr
    . simp_all
    . apply ih
      simp_all

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

theorem ReadValuesApp :
  ReadValues σ k1 v1 →
  ReadValues σ k2 v2 →
  ReadValues σ (k1 ++ k2) (v1 ++ v2) := by
  intros Hrd1 Hrd2
  induction Hrd1 <;> simp_all
  case read_some Hsome Hrd Hrds =>
  constructor <;> assumption

theorem ReadValuesAppKeys' :
  ReadValues σ (k1 ++ k2) vs →
  exists v1 v2,
  v1 ++ v2 = vs ∧
  ReadValues σ k1 v1 ∧
  ReadValues σ k2 v2 := by
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
      | read_some Hsome Hrd =>
        specialize vih Hrd
        cases vih with
        | intro v1' vih =>
        cases vih with
        | intro v2 vih =>
        exists vh::v1',v2
        simp_all
        constructor <;> simp_all

theorem ReadValuesLength :
  ReadValues σ ks vs →
  ks.length = vs.length := by
  intros Hrd
  induction Hrd <;> simp_all

theorem EvalExpressionsLength :
  EvalExpressions (P:=Core.Expression) δ σ ks vs →
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

theorem InitStateReadValuesMonotone {P : PureExpr} {σ σ' : SemanticStore P}
  {ks : List P.Ident} {vs : List P.Expr} {e : P.Expr} {v : P.Ident} :
  ReadValues σ ks vs →
  InitState P σ v e σ' →
  ReadValues σ' ks vs := by
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

theorem InitStatesReadValuesMonotone
  {P : PureExpr} {σ σ' : SemanticStore P}
  {ks : List P.Ident} {vs : List P.Expr}
  {es' : List P.Expr} {vs' : List P.Ident} :
  ReadValues σ ks vs →
  InitStates σ vs' es' σ' →
  ReadValues σ' ks vs := by
  intros Hdef Heval
  induction Heval with
  | init_none => assumption
  | init_some Hinit Hinits ih =>
    apply ih
    apply InitStateReadValuesMonotone <;> assumption

theorem UpdateStateReadValuesMonotone {P : PureExpr} {σ σ' : SemanticStore P}
  {ks : List P.Ident} {vs : List P.Expr} {e : P.Expr} {v : P.Ident} :
  ¬ v ∈ ks →
  ReadValues σ ks vs →
  UpdateState P σ v e σ' →
  ReadValues σ' ks vs := by
  intros Hnin Hdef Heval
  cases Heval with
  | update Hold HH Hsome =>
  induction Hdef
  case read_none => constructor
  case read_some xs vs' x v' Hsome' Hrd Hrds =>
  constructor <;> simp_all

theorem UpdateStatesReadValuesMonotone
  {P : PureExpr} {σ σ' : SemanticStore P}
  {ks : List P.Ident} {vs : List P.Expr}
  {es' : List P.Expr} {vs' : List P.Ident} :
  (ks ++ vs').Nodup →
  ReadValues σ ks vs →
  UpdateStates σ vs' es' σ' →
  ReadValues σ' ks vs := by
  intros Hnd Hdef Heval
  induction Heval with
  | update_none => assumption
  | update_some Hinit Hinits ih =>
    have Hnd' := nodup_middle Hnd
    simp_all
    apply ih
    apply UpdateStateReadValuesMonotone _ Hdef Hinit <;> try assumption
    simp_all

theorem InitStateReadValues :
  InitState P σ v e σ' →
  ReadValues σ' [v] [e] := by
  intros Hinit
  cases Hinit with
  | init Hold HH Hsome =>
  constructor
  . assumption
  . constructor

theorem UpdateStateReadValues :
  UpdateState P σ v e σ' →
  ReadValues σ' [v] [e] := by
  intros Hinit
  cases Hinit with
  | update Hold HH Hsome =>
  constructor
  . assumption
  . constructor

theorem InitStatesReadValues :
  InitStates σ vs es σ' →
  ReadValues σ' vs es := by
  intros Hinit
  induction Hinit
  case init_none =>
    constructor
  case init_some x v σ₁ x' v' σ'' Hinit Hinits ih =>
    constructor <;> try assumption
    have Hrd : ReadValues σ'' [x] [v] := by
      apply InitStatesReadValuesMonotone (σ:=σ₁)
      apply InitStateReadValues <;> assumption
      assumption
    cases Hrd
    assumption

theorem UpdateStatesReadValues :
  vs.Nodup →
  UpdateStates σ vs es σ' →
  ReadValues σ' vs es := by
  intros Hnd Hinit
  induction Hinit
  case update_none =>
    constructor
  case update_some x v σ₁ x' v' σ'' Hupdate Hupdates ih =>
    constructor <;> try assumption
    have Hrd : ReadValues σ'' [x] [v] := by
      apply UpdateStatesReadValuesMonotone (σ:=σ₁)
      exact Hnd
      apply UpdateStateReadValues <;> assumption
      assumption
    cases Hrd
    assumption
    apply ih
    simp_all

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

theorem InitVarsReadValuesMonotone
  {P : PureExpr} {σ σ' : SemanticStore P}
  {ks vs' : List P.Ident} {vs : List P.Expr} :
  ReadValues σ ks vs →
  InitVars σ vs' σ' →
  ReadValues σ' ks vs := by
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
  kvs.unzip.1.Disjoint kvs'.unzip.1 →
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
      have Hnd' := List.Disjoint.symm Hnd
      apply List.Disjoint_cons_head
      apply List.Disjoint.mono_right _ Hnd'
      simp_all
    . intros Hin
      simp_all [List.Disjoint]
    . simp at *
      refine List.Disjoint.mono_right ?_ Hnd
      simp_all

theorem UpdateStateSomeMonotone
  {P : PureExpr} {σ σ' : SemanticStore P}
  {k' : P.Ident} {v' : P.Expr} {e : P.Expr} {v : P.Ident} :
  v ≠ k' →
  σ k' = some v' →
  UpdateState P σ v e σ' →
  σ' k' = some v' := by
  intros Hne Hdef Heval
  have Hrd : ReadValues σ [k'] [v'] := by
    cases Heval with
    | update Hold HH Hsome =>
    constructor <;> simp_all
    constructor
  have Hrd2 : ReadValues σ' [k'] [v'] := by
    apply UpdateStateReadValuesMonotone ?_ Hrd Heval
    simp_all
  cases Hrd2
  assumption

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
  intros Hdef Heval
  have Hrd : ReadValues σ [k'] [v'] := by
    cases Heval with
    | init Hold HH Hsome =>
    constructor <;> simp_all
    constructor
  have Hrd2 : ReadValues σ' [k'] [v'] :=
    InitStateReadValuesMonotone Hrd Heval
  cases Hrd2
  assumption

theorem InitStateSomeMonotone'
  {P : PureExpr} {σ σ' : SemanticStore P}
  {k' : P.Ident} {v' : P.Expr} {e : P.Expr} {v : P.Ident} :
  k' ≠ v →
  σ' k' = some v' →
  InitState P σ v e σ' →
  σ k' = some v' := by
  intros Hne Hdef Heval
  have Hrd : ReadValues σ [k'] [v'] := by
    cases Heval with
    | init Hold HH Hsome =>
    constructor <;> simp_all
    rw [← Hsome]
    assumption
    exact fun a => Hne (Eq.symm a)
    constructor
  have Hrd2 : ReadValues σ' [k'] [v'] :=
    InitStateReadValuesMonotone Hrd Heval
  cases Hrd
  assumption

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

theorem isDefinedReadValues :
  isDefined σ ks →
  ∃ vs,
  ReadValues σ ks vs := by
  intros Hdef
  simp [isDefined] at Hdef
  induction ks <;> simp_all
  case nil =>
    exists []
    constructor
  case cons h t ih =>
    cases ih with
    | intro t' Hrd =>
    have Hsome := Hdef.1
    simp [Option.isSome] at Hsome
    split at Hsome <;> simp_all
    next h' Hh' =>
    exists (h' :: t')
    constructor <;> simp_all

theorem ReadValuesIsDefined :
  ReadValues σ ks vs →
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

theorem InitStateSubstStores :
σ k' = some v' →
InitState Expression σ k v' σ' →
substStores σ σ' [(k', k)] := by
intros Hsome Hinit
cases Hinit with
| init Hone Hsome' Heq =>
simp [substStores]
simp [Hsome, Hsome']

theorem InitStatesSubstStores :
ReadValues σ ks' vs' →
InitStates σ ks vs' σ' →
substStores σ σ' (ks'.zip ks) := by
intros Hrd Hinit
induction Hinit generalizing ks' with
| init_none =>
  simp [substStores]
| init_some Hinit Hinits ih =>
  next σ x v σ₁ xs vs σ'' =>
  cases Hrd with
  | read_some Hsome'' Hrds =>
  next ys y =>
  have Hinit' := Hinit
  cases Hinit with
  | init Hnone Hsome' Heq =>
  simp [substStores]
  intros k1 k2 Hin
  cases Hin with
  | inl Hin =>
    simp_all
    apply Eq.symm
    apply InitStatesSomeMonotone Hsome' Hinits
  | inr Hin =>
    specialize @ih ys ?_
    exact InitStateReadValuesMonotone Hrds Hinit'
    rw [← Heq]
    exact ih k1 k2 Hin
    apply Not.intro
    intro Heq
    simp_all
    have Hin' := List.of_mem_zip Hin
    have Hdef := ReadValuesIsDefined Hrds
    specialize Hdef k1 Hin'.1
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
ks.Disjoint substs.unzip.2 →
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
    simp [List.Disjoint] at Hnin
    intros Hin
    have Hprod := List.mem_zip_2 (l₁:=substs.unzip.fst) (by simp) Hin
    rw [List.zip_unzip] at Hprod
    cases Hprod with
    | intro w Hprod =>
    have HH := Hnin.1 w
    contradiction
  have HH := substStoresUpdateInv (σ:=σ) Hnin Hsubst Hup
  apply ih HH
  simp [List.Disjoint] at *
  simp_all

theorem substStoresUpdatesInv' :
ks.Disjoint substs.unzip.1 →
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

theorem ReadValuesSubstStores :
  ReadValues σ ks vs →
  ReadValues σ' ks' vs →
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
    | read_some Hh Ht =>
    cases H2 with
    | read_some Hh' Ht' =>
    simp
    apply substStoresCons
    . simp [substStores]
      simp_all
    . exact ih Ht Ht'

theorem EvalStatementsContractApp' {φ : CoreEval → PureFunc Expression → CoreEval} {δ δ'' : CoreEval} :
  EvalStatementsContract π φ δ σ (ss₁ ++ ss₂) σ'' δ'' →
  ∃ σ' δ',
    EvalStatementsContract π φ δ σ ss₁ σ' δ' ∧
    EvalStatementsContract π φ δ' σ' ss₂ σ'' δ'' := by
  intros Heval
  induction ss₁ generalizing σ δ <;> simp_all
  case nil =>
    exists σ, δ <;> simp_all
    exact EvalBlock.stmts_none_sem
  case cons h t ih =>
    cases Heval with
    | stmts_some_sem Hh Ht =>
    next σ' δ' =>
    specialize ih Ht
    cases ih with
    | intro σ'' Heval =>
    cases Heval with
    | intro δ'' Heval =>
    exists σ'', δ''
    simp_all
    exact EvalBlock.stmts_some_sem Hh Heval.1

theorem EvalStatementsContractApp {φ : CoreEval → PureFunc Expression → CoreEval} {δ δ' δ'' : CoreEval} :
  EvalStatementsContract π φ δ σ ss₁ σ' δ' →
  EvalStatementsContract π φ δ' σ' ss₂ σ'' δ'' →
  EvalStatementsContract π φ δ σ (ss₁ ++ ss₂) σ'' δ'' := by
  intros Heval1 Heval2
  induction ss₁ generalizing σ σ' δ δ' <;> simp_all
  case nil =>
    have ⟨Hσ, Hδ⟩ := EvalBlockEmpty Heval1
    simp [Hσ, Hδ]
    assumption
  case cons h t ih =>
    cases Heval1 with
    | stmts_some_sem Heval Heval' =>
    next σ₁ δ₁ =>
    constructor
    . exact Heval
    . exact ih Heval' Heval2

theorem EvalStatementsApp {φ : CoreEval → PureFunc Expression → CoreEval} {δ δ' δ'' : CoreEval} :
  EvalStatements π φ δ σ ss₁ σ' δ' →
  EvalStatements π φ δ' σ' ss₂ σ'' δ'' →
  EvalStatements π φ δ σ (ss₁ ++ ss₂) σ'' δ'' := by
  intros Heval1 Heval2
  induction ss₁ generalizing σ σ' δ δ' with
  | nil =>
    have ⟨Hσ, Hδ⟩ := EvalBlockEmpty Heval1
    simp [Hσ, Hδ]
    assumption
  | cons h t ih =>
    cases Heval1 with
    | stmts_some_sem Heval Heval' =>
    next σ₁ δ₁ =>
    constructor
    . exact Heval
    . exact ih Heval' Heval2

theorem HavocVarsApp :
  HavocVars σ vs₁ σ' →
  HavocVars σ' vs₂ σ'' →
  HavocVars σ (vs₁ ++ vs₂) σ'' := by
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
    next exp σ1 Hup Hhavoc =>
    apply HavocVars.update_some <;> try assumption
    exact ih Hhavoc

theorem HavocVarsApp' :
  HavocVars σ (vs₁ ++ vs₂) σ'' →
  ∃ σ',
  HavocVars σ vs₁ σ' ∧
  HavocVars σ' vs₂ σ'' := by
  intros Hv
  induction vs₁ generalizing σ
  case nil =>
    exists σ
    simp_all
    constructor
  case cons h t ih =>
    cases Hv
    next exp σ1 Hup Hhavoc =>
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

theorem HavocVarsCons :
  HavocVars σ [v] σ' →
  HavocVars σ' vs σ'' →
  HavocVars σ (v :: vs) σ'' := by
  intros Hv1 Hv2
  have Heq : (v :: vs = [v] ++ vs) := by rfl
  rw [Heq]
  exact HavocVarsApp Hv1 Hv2

theorem HavocVarsId :
  isDefined σ vs →
  HavocVars σ vs σ := by
  intros Hdef
  induction vs
  constructor
  next P h t ih =>
  have Hh := Hdef h List.mem_cons_self
  simp [Option.isSome] at Hh
  split at Hh <;> simp_all
  next x v' heq =>
  apply @HavocVars.update_some (σ':=σ) (v:=v')
  exact UpdateState.update heq heq fun y => congrFun rfl
  apply ih
  simp [isDefined] at *
  intros v Hin
  apply Hdef.2 v Hin

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
  vs.Disjoint vs' →
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
    . apply List.Disjoint.mono_right _ Hdisj
      exact List.sublist_cons_self x xs'
    . assumption

theorem InitVarsDefMonotone' :
  vs.Disjoint vs' →
  isDefined σ' vs →
  InitVars σ vs' σ' →
  isDefined σ vs := by
  intros Hdisj Hdef Hinit
  have Hinit := InitVarsInitStates Hinit
  cases Hinit with
  | intro es Hinit =>
  exact InitStatesDefMonotone' Hdisj Hdef Hinit

-- theorem InitVarsNotDefMonotone' :
--   vs.Disjoint vs' →
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

theorem HavocVarsDefMonotone :
  isDefined σ vs →
  HavocVars σ vs' σ' →
  isDefined σ' vs := by
  intros Hdef Hhavoc
  induction Hhavoc with
  | update_some Hup Hhav ih =>
  apply ih
  apply UpdateStateDefMonotone <;> assumption
  | update_none => simp_all

theorem HavocVarsUpdateStates : HavocVars σ vars σ' →
  ∃ modvals, UpdateStates σ vars modvals σ' := by
  intros Hhav
  induction Hhav
  case update_none =>
    refine ⟨[], UpdateStates.update_none⟩
  case update_some σ x v σ₁ xs σ'' Hup Hhav Hex =>
    cases Hex with
    | intro vs Hups =>
    refine ⟨v::vs,?_⟩
    constructor <;> assumption

theorem HavocVarsDefMonotone' :
  isDefined σ' vs →
  HavocVars σ vs' σ' →
  isDefined σ vs := by
  intros Hdef Hhavoc
  have Hup := HavocVarsUpdateStates Hhavoc
  cases Hup with
  | intro es Hinit =>
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

theorem InitVarsReadValues :
  InitVars σ ks σ' →
  exists vs,
  ReadValues σ' ks vs := by
  intros Hinit
  induction Hinit
  case init_none =>
    exists []
    constructor
  case init_some x x' σ xs σ' Hinit Hinits ih =>
  cases Hinit with
  | init Hnone Hsome Hinv =>
  cases ih with
  | intro xs' Hrds =>
  exists x' :: xs'
  constructor <;> simp_all
  have Hrd : ReadValues σ [x] [x'] :=
    ReadValues.read_some Hsome ReadValues.read_none
  have Hrd' := InitVarsReadValuesMonotone Hrd Hinits
  cases Hrd'
  assumption

theorem HavocVarsDefined :
  HavocVars σ vs σ' →
  isDefined σ' vs := by
  intros Hhavoc
  induction vs generalizing σ σ'
  case nil => simp [isDefined]
  case cons h t ih =>
    cases Hhavoc with
    | @update_some _ _ v σ₁ _ _ Hup Hhav =>
    apply isDefinedCons
    apply HavocVarsDefMonotone (σ:=σ₁)
    apply UpdateStateDefined <;> assumption
    assumption
    apply ih <;> assumption

theorem EvalCmdDefMonotone' :
  isDefined σ v →
  EvalCmd Core.Expression δ σ c σ' →
  isDefined σ' v := by
  intros Hdef Heval
  cases Heval <;> try exact Hdef
  next _ Hup => exact InitStateDefMonotone Hdef Hup  -- eval_init
  next Hup => exact InitStateDefMonotone Hdef Hup    -- eval_init_unconstrained
  next _ Hup => exact UpdateStateDefMonotone Hdef Hup
  next Hup => exact UpdateStateDefMonotone Hdef Hup

theorem EvalCmdTouch
  [HasVal P] [HasFvar P] [HasBool P] [HasBoolVal P] [HasNot P] :
  EvalCmd P δ σ c σ' →
  TouchVars σ (HasVarsImp.touchedVars c) σ' := by
  intro Heval
  induction Heval <;> simp [HasVarsImp.touchedVars, Cmd.definedVars, Cmd.modifiedVars]
  case eval_init x' δ σ x v σ' σ₀ e Hsm Hup Hwf =>
    apply TouchVars.init_some Hup
    constructor
  case eval_init_unconstrained x' δ σ x v σ' σ₀ Hup Hwf =>
    apply TouchVars.init_some Hup
    constructor
  case eval_set δ σ x v σ' σ₀ e Hsm Hup Hwf =>
    exact TouchVars.update_some Hup TouchVars.none
  case eval_havoc x v σ' σ₀ e Hsm Hup Hwf =>
    exact TouchVars.update_some Hup TouchVars.none
  case eval_assert => exact TouchVars.none
  case eval_assume => exact TouchVars.none
  case eval_cover => exact TouchVars.none

theorem UpdateStatesHavocVars : UpdateStates σ vars modvals σ' → HavocVars σ vars σ' := by
  intros H
  induction vars generalizing σ modvals
  case nil =>
    cases modvals
    . have Heq := UpdateStatesEmpty H
      simp [Heq]
      apply HavocVars.update_none
    . cases H
  case cons h t ih =>
    have HH := H
    cases H
    next Hup2 =>
    constructor <;> try assumption
    apply ih
    apply Hup2

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
EvalCmd Expression δ σ c σ' →
EvalCommandContract π δ σ (CmdExt.cmd c) σ' := by
intros H; constructor; assumption

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
  ks.Disjoint ks' →
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
  ks.Disjoint ks' →
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
  exact List.DisjointAppRight' Hdisj

theorem InvStoresExceptUpdated :
  invStoresExcept σ σ' ks →
  ks'.length = vs'.length →
  invStoresExcept (updatedStates σ ks' vs') σ' (ks ++ ks') := by
  intros Hinv Hlen
  simp [invStoresExcept] at *
  intros vsInv Hdisj
  refine InvStoresUpdatedStatesDisjLeftMono ?_ ?_ Hlen
  exact List.DisjointAppLeft' Hdisj
  apply Hinv
  exact List.DisjointAppRight' Hdisj

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

theorem InvStoresExceptHavocVars :
  invStoresExcept σ σ' ks →
  HavocVars σ ks' σ'' →
  invStoresExcept σ'' σ' (ks ++ ks') := by
  intros Hinv Hup
  have Hup' := HavocVarsUpdateStates Hup
  cases Hup' with
  | intro vs' Hups =>
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
  List.Disjoint ks ks' →
  invStores σ σ' ks' := by
  intros Hinv Hdis k1 k2 Hin
  apply Hinv ks'
  exact List.Disjoint.symm Hdis
  assumption

/--
NOTE:
  In order to prove this refinement theorem, we need to reason about the
  assymmetry between the two semantics regarding the temporary variables
  created in the concrete semantics. That is, evaluating the procedure body may
  create new variables in the store, and since the temporary variables are
  discarded at the end of the call, it is possible to show that those created
  variables are irrelevant, and can be approximated by updating the relevant
  variables (that is, lhs ++ modifies)
-/
theorem EvalCallBodyRefinesContract :
  ∀ {π φ δ σ lhs n args σ' p},
  π n = .some p →
  p.spec.modifies = Imperative.HasVarsTrans.modifiedVarsTrans π p.body →
  EvalCommand π φ δ σ (CmdExt.call lhs n args) σ' →
  EvalCommandContract π δ σ (CmdExt.call lhs n args) σ' := by
  intros π φ δ σ lhs n args σ' p pFound modValid H
  cases H with
  | call_sem lkup Heval Hwfval Hwfvars Hwfb Hwf Hwf2 Hup Hhav Hpre Heval2 Hpost Hrd Hup2 =>
    sorry

theorem EvalCommandRefinesContract :
EvalCommand π φ δ σ c σ' →
EvalCommandContract π δ σ c σ' := by
  intros H
  cases H with
  | cmd_sem H => exact EvalCommandContract.cmd_sem H
  | call_sem _ =>
    apply EvalCallBodyRefinesContract <;> try assumption
    -- need to connect `modifies` with `modifiedVarsTrans`
    sorry
    constructor <;> assumption

mutual
/-- Proof that `EvalStmt` with concrete semantics refines contract semantics,
    by structural recursion on the derivation. -/
theorem EvalStmtRefinesContract
  (H : EvalStmt Expression Command (EvalCommand π φ) (EvalPureFunc φ) δ σ s σ' δ') :
  EvalStmt Expression Command (EvalCommandContract π) (EvalPureFunc φ) δ σ s σ' δ' :=
  match H with
  | .cmd_sem Heval Hdef => .cmd_sem (EvalCommandRefinesContract Heval) Hdef
  | .block_sem Heval => .block_sem (EvalBlockRefinesContract Heval)
  | .ite_true_sem Hcond Hwf Heval => .ite_true_sem Hcond Hwf (EvalBlockRefinesContract Heval)
  | .ite_false_sem Hcond Hwf Heval => .ite_false_sem Hcond Hwf (EvalBlockRefinesContract Heval)
  | .funcDecl_sem => .funcDecl_sem

/-- Proof that `EvalBlock` with concrete semantics refines contract semantics,
    by structural recursion on the derivation. -/
theorem EvalBlockRefinesContract
  (H : EvalBlock Expression Command (EvalCommand π φ) (EvalPureFunc φ) δ σ ss σ' δ') :
  EvalBlock Expression Command (EvalCommandContract π) (EvalPureFunc φ) δ σ ss σ' δ' :=
  match H with
  | .stmts_none_sem => .stmts_none_sem
  | .stmts_some_sem Hstmt Hrest =>
    .stmts_some_sem (EvalStmtRefinesContract Hstmt) (EvalBlockRefinesContract Hrest)
end

/-- If an expression is defined, all its free variables are defined in the store.
    Relies on the definedness propagation properties in `WellFormedCoreEvalCong`
    together with the variable-evaluation condition in `WellFormedSemanticEvalVar`. -/
theorem EvalExpressionIsDefined :
  WellFormedCoreEvalCong δ →
  WellFormedSemanticEvalVar δ →
  (δ σ e).isSome →
  isDefined σ (HasVarsPure.getVars e) := by
  intros Hwfc Hwfvr Hsome
  intros v Hin
  simp [WellFormedSemanticEvalVar] at Hwfvr
  induction e generalizing v <;>
    simp [HasVarsPure.getVars, Lambda.LExpr.LExpr.getVars] at *
  case fvar m v' ty' =>
    specialize Hwfvr (Lambda.LExpr.fvar m v' ty') v' σ
    simp [HasFvar.getFvar] at Hwfvr
    simp_all
  case abs m ty e ih =>
    exact ih (Hwfc.definedness.absdef σ m ty e Hsome) v Hin
  case quant m k ty tr e trih eih =>
    have ⟨htr, he⟩ := Hwfc.definedness.quantdef σ m k ty tr e Hsome
    grind
  case app m e₁ e₂ ih₁ ih₂ =>
    have ⟨h₁, h₂⟩ := Hwfc.definedness.appdef σ m e₁ e₂ Hsome
    grind
  case ite m c t e cih tih eih =>
    have ⟨hc, ht, he⟩ := Hwfc.definedness.itedef σ m c t e Hsome
    grind
  case eq m e₁ e₂ ih₁ ih₂ =>
    have ⟨h₁, h₂⟩ := Hwfc.definedness.eqdef σ m e₁ e₂ Hsome
    grind
