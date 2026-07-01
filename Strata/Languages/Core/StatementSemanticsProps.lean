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
public import Strata.DL.Util.ListUtils
import all Strata.DL.Util.ListUtils
import all Strata.Languages.Core.Statement
public import Strata.Languages.Core.StatementSemantics
import all Strata.Languages.Core.StatementSemantics
import all Strata.DL.Imperative.Cmd
import all Strata.DL.Imperative.Stmt
import Std.Tactic.BVDecide.Normalize.BitVec

public section

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
  EvalCmd Core.Expression fac σ c σ' f →
  isDefined σ' v := by
  intros Hdef Heval
  cases Heval with
  | eval_init Hsm Hup Hwf => exact InitStateDefMonotone Hdef Hup
  | eval_init_unconstrained Hup Hwf => exact InitStateDefMonotone Hdef Hup
  | eval_set Hsm Hup Hwf => exact UpdateStateDefMonotone Hdef Hup
  | eval_set_nondet Hup Hwf => exact UpdateStateDefMonotone Hdef Hup
  | _ => exact Hdef

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

/-

/-
NOTE:
  In order to prove this refinement theorem, we need to reason about the
  assymmetry between the two semantics regarding the temporary variables
  created in the concrete semantics. That is, evaluating the procedure body may
  create new variables in the store, and since the temporary variables are
  discarded at the end of the call, it is possible to show that those created
  variables are irrelevant.
-/
theorem EvalCallBodyRefinesContract :
  ∀ {π φ fac σ n callArgs σ' p md md'},
  π n = .some p →
  EvalCommand π φ fac σ (CmdExt.call n callArgs md) σ' false →
  EvalCommandContract π fac σ (CmdExt.call n callArgs md') σ' false := by
  intros π φ fac σ n callArgs σ' p md md' pFound H
  cases H with
  | call_sem hlkup _ _ heval hread hwfs hwfv hwfvar hwfb hwftwo hdef hinit_i hinit_o hpre hbody hpost hread_f hupd =>
    exact EvalCommandContract.call_sem hlkup rfl rfl heval hread hwfs hwfv hwfvar hwfb hwftwo hdef hinit_i hinit_o hpre sorry hpost hread_f hupd

theorem EvalCommandRefinesContract :
EvalCommand π φ fac σ c σ' f →
EvalCommandContract π fac σ c σ' f := by
  intros H
  cases H with
  | cmd_sem H => exact EvalCommandContract.cmd_sem H
  | call_sem _ =>
    apply EvalCallBodyRefinesContract <;> try assumption
    constructor <;> assumption

/-- A single `StepStmt` with `EvalCommand` can be simulated by a single
    `StepStmt` with `EvalCommandContract`. -/
private theorem StepStmt_refines_contract
    {c₁ c₂ : Imperative.Config Expression Command} :
    Imperative.StepStmt Expression (EvalCommand π φ) (EvalPureFunc φ) c₁ c₂ →
    Imperative.StepStmt Expression (EvalCommandContract π) (EvalPureFunc φ) c₁ c₂ := by
  intro H
  induction H with
  | step_cmd hcmd => exact .step_cmd (EvalCommandRefinesContract hcmd)
  | step_seq_inner _ ih => exact .step_seq_inner ih
  | step_block_body _ ih => exact .step_block_body ih
  | step_block => exact .step_block
  | step_ite_true h1 h2 => exact .step_ite_true h1 h2
  | step_ite_false h1 h2 => exact .step_ite_false h1 h2
  | step_ite_nondet_true => exact .step_ite_nondet_true
  | step_ite_nondet_false => exact .step_ite_nondet_false
  | step_loop_enter h1 h2 h3 h4 h5 h6 h7 => exact .step_loop_enter h1 h2 h3 h4 h5 h6 h7
  | step_loop_exit h1 h2 h3 h4 => exact .step_loop_exit h1 h2 h3 h4
  | step_loop_nondet_enter => exact .step_loop_nondet_enter
  | step_loop_nondet_exit => exact .step_loop_nondet_exit
  | step_exit => exact .step_exit
  | step_funcDecl => exact .step_funcDecl
  | step_typeDecl => exact .step_typeDecl
  | step_stmts_nil => exact .step_stmts_nil
  | step_stmts_cons => exact .step_stmts_cons
  | step_seq_done => exact .step_seq_done
  | step_seq_exit => exact .step_seq_exit
  | step_block_done => exact .step_block_done
  | step_block_exit_none => exact .step_block_exit_none
  | step_block_exit_match h => exact .step_block_exit_match h
  | step_block_exit_mismatch h => exact .step_block_exit_mismatch h

/-- Small-step execution with `EvalCommand` refines `EvalCommandContract`. -/
theorem StepStmtStar_refines_contract
    {c₁ c₂ : Imperative.Config Expression Command} :
    Imperative.StepStmtStar Expression (EvalCommand π φ) (EvalPureFunc φ) c₁ c₂ →
    Imperative.StepStmtStar Expression (EvalCommandContract π) (EvalPureFunc φ) c₁ c₂ := by
  intro H
  induction H with
  | refl => exact .refl _
  | step _ _ _ hstep _ ih =>
    exact .step _ _ _ (StepStmt_refines_contract hstep) ih

/-- `EvalStatements` with concrete semantics refines contract semantics. -/
theorem EvalStatementsRefinesContract :
    EvalStatements π φ ρ ss ρ' →
    EvalStatementsContract π φ ρ ss ρ' :=
  StepStmtStar_refines_contract

/-- `EvalStatement` with concrete semantics refines contract semantics. -/
theorem EvalStatementRefinesContract :
    EvalStatement π φ ρ s ρ' →
    EvalStatementContract π φ ρ s ρ' :=
  StepStmtStar_refines_contract

-/


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

/-! ### Config-level WF predicates for Core

`step_block_done`/`exit_match`/`exit_mismatch` restore `eval := e_parent`, so
preservation of WF along a trace requires WF of every captured `e_parent`
snapshot in addition to WF of the inner eval. -/

@[expose] def CoreConfig.wfBool : CoreConfig → Prop
  | .stmt _ ρ => WellFormedSemanticEvalBool (P := Expression) ρ.factory
  | .stmts _ ρ => WellFormedSemanticEvalBool (P := Expression) ρ.factory
  | .terminal ρ => WellFormedSemanticEvalBool (P := Expression) ρ.factory
  | .exiting _ ρ => WellFormedSemanticEvalBool (P := Expression) ρ.factory
  | .block _ _ f_parent inner =>
    WellFormedSemanticEvalBool (P := Expression) f_parent ∧ CoreConfig.wfBool inner
  | .seq inner _ => CoreConfig.wfBool inner

@[expose] def CoreConfig.wfVar : CoreConfig → Prop
  | .stmt _ ρ => WellFormedSemanticEvalVar (P := Expression) ρ.factory
  | .stmts _ ρ => WellFormedSemanticEvalVar (P := Expression) ρ.factory
  | .terminal ρ => WellFormedSemanticEvalVar (P := Expression) ρ.factory
  | .exiting _ ρ => WellFormedSemanticEvalVar (P := Expression) ρ.factory
  | .block _ _ f_parent inner =>
    WellFormedSemanticEvalVar (P := Expression) f_parent ∧ CoreConfig.wfVar inner
  | .seq inner _ => CoreConfig.wfVar inner

@[expose] def CoreConfig.wfCong : CoreConfig → Prop
  | .stmt _ ρ => WellFormedCoreEvalCong ρ.factory
  | .stmts _ ρ => WellFormedCoreEvalCong ρ.factory
  | .terminal ρ => WellFormedCoreEvalCong ρ.factory
  | .exiting _ ρ => WellFormedCoreEvalCong ρ.factory
  | .block _ _ f_parent inner =>
    WellFormedCoreEvalCong f_parent ∧
    CoreConfig.wfCong inner
  | .seq inner _ => CoreConfig.wfCong inner

@[expose] def CoreConfig.wfExprCongr : CoreConfig → Prop
  | .stmt _ ρ => @Imperative.WellFormedSemanticEvalExprCongr Expression _ ρ.factory
  | .stmts _ ρ => @Imperative.WellFormedSemanticEvalExprCongr Expression _ ρ.factory
  | .terminal ρ => @Imperative.WellFormedSemanticEvalExprCongr Expression _ ρ.factory
  | .exiting _ ρ => @Imperative.WellFormedSemanticEvalExprCongr Expression _ ρ.factory
  | .block _ _ f_parent inner =>
    @Imperative.WellFormedSemanticEvalExprCongr Expression _ f_parent ∧
    CoreConfig.wfExprCongr inner
  | .seq inner _ => CoreConfig.wfExprCongr inner

/-- If an expression evaluates successfully, all its free variables are defined
    in the store. This is proved from the (temporary, unsound) definedness
    propagation packaged in `WellFormedCoreEvalCong`; it MUST be re-proved
    directly against `Expression.eval` once that machinery disappears. -/
theorem EvalExpressionIsDefined :
  WellFormedStore σ f →
  WellFormedCoreEvalCong f →
  WellFormedSemanticEvalVar (P := Expression) f →
  (Expression.eval f σ e).isSome →
  isDefined σ (HasFvars.getFvars e) := by
  intros Hwfs Hwfc Hwfvr Hsome
  intros v Hin
  simp [WellFormedSemanticEvalVar] at Hwfvr
  induction e generalizing v <;>
    simp [HasFvars.getFvars, Lambda.LExpr.LExpr.getVars] at *
  case fvar m v' ty' =>
    specialize Hwfvr (Lambda.LExpr.fvar m v' ty') v' σ Hwfs
    simp [HasFvar.getFvar] at Hwfvr
    simp_all
  case abs m name ty e ih =>
    exact ih (Hwfc.definedness.absdef σ m name ty e Hsome) v Hin
  case quant m k name ty tr e trih eih =>
    have ⟨htr, he⟩ := Hwfc.definedness.quantdef σ m k name ty tr e Hsome
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


private theorem core_step_preserves_cfg_wfBool
    (h_wf_ext : WFFactoryExtension φ)
    (c₁ c₂ : CoreConfig)
    (hwf : c₁.wfBool)
    (hstep : CoreStep π φ c₁ c₂) :
    c₂.wfBool := by
  induction hstep with
  | step_cmd hcmd => cases hcmd with
    | cmd_sem _ | @call_sem _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
        exact hwf
  | step_block | step_ite_true | step_ite_false | step_ite_nondet_true
  | step_ite_nondet_false | step_loop_enter | step_loop_nondet_enter => exact ⟨hwf, hwf⟩
  | step_block_done | step_block_exit_match | step_block_exit_mismatch => exact hwf.1
  | step_seq_inner _ ih => exact ih hwf
  | step_block_body hstep_inner ih =>
    exact ⟨hwf.1, ih hwf.2⟩
  | step_funcDecl => exact h_wf_ext.preserves_wfBool _ _ _ hwf
  | _ => exact hwf

private theorem core_step_preserves_cfg_wfVar
    (h_wf_ext : WFFactoryExtension φ)
    (c₁ c₂ : CoreConfig)
    (hwf : c₁.wfVar)
    (hstep : CoreStep π φ c₁ c₂) :
    c₂.wfVar := by
  induction hstep with
  | step_cmd hcmd => cases hcmd with
    | cmd_sem _ | @call_sem _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
        exact hwf
  | step_block | step_ite_true | step_ite_false | step_ite_nondet_true
  | step_ite_nondet_false | step_loop_enter | step_loop_nondet_enter => exact ⟨hwf, hwf⟩
  | step_block_done | step_block_exit_match | step_block_exit_mismatch => exact hwf.1
  | step_seq_inner _ ih => exact ih hwf
  | step_block_body hstep_inner ih =>
    exact ⟨hwf.1, ih hwf.2⟩
  | step_funcDecl => exact h_wf_ext.preserves_wfVar _ _ _ hwf
  | _ => exact hwf

private theorem core_step_preserves_cfg_wfCong
    (h_wf_ext : WFFactoryExtension φ)
    (c₁ c₂ : CoreConfig)
    (hwf : c₁.wfCong)
    (hstep : CoreStep π φ c₁ c₂) :
    c₂.wfCong := by
  induction hstep with
  | step_cmd hcmd => cases hcmd with
    | cmd_sem _ | @call_sem _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
        exact hwf
  | step_block | step_ite_true | step_ite_false | step_ite_nondet_true
  | step_ite_nondet_false | step_loop_enter | step_loop_nondet_enter => exact ⟨hwf, hwf⟩
  | step_block_done | step_block_exit_match | step_block_exit_mismatch => exact hwf.1
  | step_seq_inner _ ih => exact ih hwf
  | step_block_body hstep_inner ih =>
    exact ⟨hwf.1, ih hwf.2⟩
  | step_funcDecl => exact h_wf_ext.preserves_wfCong _ _ _ hwf
  | _ => exact hwf

private theorem core_step_preserves_cfg_wfExprCongr
    (h_wf_ext : WFFactoryExtension φ)
    (c₁ c₂ : CoreConfig)
    (hwf : c₁.wfExprCongr)
    (hstep : CoreStep π φ c₁ c₂) :
    c₂.wfExprCongr := by
  induction hstep with
  | step_cmd hcmd => cases hcmd with
    | cmd_sem _ | @call_sem _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
        exact hwf
  | step_block | step_ite_true | step_ite_false | step_ite_nondet_true
  | step_ite_nondet_false | step_loop_enter | step_loop_nondet_enter => exact ⟨hwf, hwf⟩
  | step_block_done | step_block_exit_match | step_block_exit_mismatch => exact hwf.1
  | step_seq_inner _ ih => exact ih hwf
  | step_block_body hstep_inner ih =>
    exact ⟨hwf.1, ih hwf.2⟩
  | step_funcDecl => exact h_wf_ext.preserves_wfExprCongr _ _ _ hwf
  | _ => exact hwf

private theorem CoreConfig.wfBool_implies_wfEval (cfg : CoreConfig) :
    cfg.wfBool → WellFormedSemanticEvalBool (P := Expression) cfg.getEnv.factory := by
  induction cfg with
  | stmt | stmts | terminal | exiting => intro h; exact h
  | block _ _ _ inner ih => intro h; exact ih h.2
  | seq inner _ ih => intro h; exact ih h

private theorem CoreConfig.wfVar_implies_wfEval (cfg : CoreConfig) :
    cfg.wfVar → WellFormedSemanticEvalVar (P := Expression) cfg.getEnv.factory := by
  induction cfg with
  | stmt | stmts | terminal | exiting => intro h; exact h
  | block _ _ _ inner ih => intro h; exact ih h.2
  | seq inner _ ih => intro h; exact ih h

private theorem CoreConfig.wfExprCongr_implies_wfEval (cfg : CoreConfig) :
    cfg.wfExprCongr → @Imperative.WellFormedSemanticEvalExprCongr Expression _ cfg.getEnv.factory := by
  induction cfg with
  | stmt | stmts | terminal | exiting => intro h; exact h
  | block _ _ _ inner ih => intro h; exact ih h.2
  | seq inner _ ih => intro h; exact ih h

private theorem CoreConfig.wfCong_implies_wfEval (cfg : CoreConfig) :
    cfg.wfCong → WellFormedCoreEvalCong cfg.getEnv.factory := by
  induction cfg with
  | stmt | stmts | terminal | exiting => intro h; exact h
  | block _ _ _ inner ih => intro h; exact ih h.2
  | seq inner _ ih => intro h; exact ih h

private theorem core_star_preserves_cfg_wfBool
    (h_wf_ext : WFFactoryExtension φ)
    {c₁ c₂ : CoreConfig}
    (hstar : CoreStepStar π φ c₁ c₂)
    (hwf : c₁.wfBool) :
    c₂.wfBool := by
  suffices ∀ (c₁ c₂ : CoreConfig),
      Imperative.StepStmtStar Expression (EvalCommand π φ) (EvalPureFunc φ) c₁ c₂ →
      c₁.wfBool → c₂.wfBool from
    this c₁ c₂ (CoreStepStar_to_StepStmtStar hstar) hwf
  intro c₁ c₂ hstar
  induction hstar with
  | refl => intro h; exact h
  | step _ _ _ hstep _ ih =>
    intro h; exact ih (core_step_preserves_cfg_wfBool π φ h_wf_ext _ _ h hstep)

private theorem core_star_preserves_cfg_wfVar
    (h_wf_ext : WFFactoryExtension φ)
    {c₁ c₂ : CoreConfig}
    (hstar : CoreStepStar π φ c₁ c₂)
    (hwf : c₁.wfVar) :
    c₂.wfVar := by
  suffices ∀ (c₁ c₂ : CoreConfig),
      Imperative.StepStmtStar Expression (EvalCommand π φ) (EvalPureFunc φ) c₁ c₂ →
      c₁.wfVar → c₂.wfVar from
    this c₁ c₂ (CoreStepStar_to_StepStmtStar hstar) hwf
  intro c₁ c₂ hstar
  induction hstar with
  | refl => intro h; exact h
  | step _ _ _ hstep _ ih =>
    intro h; exact ih (core_step_preserves_cfg_wfVar π φ h_wf_ext _ _ h hstep)

private theorem core_star_preserves_cfg_wfCong
    (h_wf_ext : WFFactoryExtension φ)
    {c₁ c₂ : CoreConfig}
    (hstar : CoreStepStar π φ c₁ c₂)
    (hwf : c₁.wfCong) :
    c₂.wfCong := by
  suffices ∀ (c₁ c₂ : CoreConfig),
      Imperative.StepStmtStar Expression (EvalCommand π φ) (EvalPureFunc φ) c₁ c₂ →
      c₁.wfCong → c₂.wfCong from
    this c₁ c₂ (CoreStepStar_to_StepStmtStar hstar) hwf
  intro c₁ c₂ hstar
  induction hstar with
  | refl => intro h; exact h
  | step _ _ _ hstep _ ih =>
    intro h; exact ih (core_step_preserves_cfg_wfCong π φ h_wf_ext _ _ h hstep)

private theorem core_star_preserves_cfg_wfExprCongr
    (h_wf_ext : WFFactoryExtension φ)
    {c₁ c₂ : CoreConfig}
    (hstar : CoreStepStar π φ c₁ c₂)
    (hwf : c₁.wfExprCongr) :
    c₂.wfExprCongr := by
  suffices ∀ (c₁ c₂ : CoreConfig),
      Imperative.StepStmtStar Expression (EvalCommand π φ) (EvalPureFunc φ) c₁ c₂ →
      c₁.wfExprCongr → c₂.wfExprCongr from
    this c₁ c₂ (CoreStepStar_to_StepStmtStar hstar) hwf
  intro c₁ c₂ hstar
  induction hstar with
  | refl => intro h; exact h
  | step _ _ _ hstep _ ih =>
    intro h; exact ih (core_step_preserves_cfg_wfExprCongr π φ h_wf_ext _ _ h hstep)

theorem core_wfBool_preserved_stmt
    (h_wf_ext : WFFactoryExtension φ)
    {s : Statement} {ρ : Env Expression} {c₂ : CoreConfig}
    (hwf₀ : WellFormedSemanticEvalBool (P := Expression) ρ.factory)
    (hstar : CoreStepStar π φ (.stmt s ρ) c₂) :
    WellFormedSemanticEvalBool (P := Expression) c₂.getEnv.factory :=
  CoreConfig.wfBool_implies_wfEval _
    (core_star_preserves_cfg_wfBool π φ h_wf_ext hstar
      (show CoreConfig.wfBool (.stmt s ρ) from hwf₀))

theorem core_wfBool_preserved_stmts
    (h_wf_ext : WFFactoryExtension φ)
    {ss : List Statement} {ρ : Env Expression} {c₂ : CoreConfig}
    (hwf₀ : WellFormedSemanticEvalBool (P := Expression) ρ.factory)
    (hstar : CoreStepStar π φ (.stmts ss ρ) c₂) :
    WellFormedSemanticEvalBool (P := Expression) c₂.getEnv.factory :=
  CoreConfig.wfBool_implies_wfEval _
    (core_star_preserves_cfg_wfBool π φ h_wf_ext hstar
      (show CoreConfig.wfBool (.stmts ss ρ) from hwf₀))

theorem core_wfVar_preserved_stmt
    (h_wf_ext : WFFactoryExtension φ)
    {s : Statement} {ρ : Env Expression} {c₂ : CoreConfig}
    (hwf₀ : WellFormedSemanticEvalVar (P := Expression) ρ.factory)
    (hstar : CoreStepStar π φ (.stmt s ρ) c₂) :
    WellFormedSemanticEvalVar (P := Expression) c₂.getEnv.factory :=
  CoreConfig.wfVar_implies_wfEval _
    (core_star_preserves_cfg_wfVar π φ h_wf_ext hstar
      (show CoreConfig.wfVar (.stmt s ρ) from hwf₀))

theorem core_wfVar_preserved_stmts
    (h_wf_ext : WFFactoryExtension φ)
    {ss : List Statement} {ρ : Env Expression} {c₂ : CoreConfig}
    (hwf₀ : WellFormedSemanticEvalVar (P := Expression) ρ.factory)
    (hstar : CoreStepStar π φ (.stmts ss ρ) c₂) :
    WellFormedSemanticEvalVar (P := Expression) c₂.getEnv.factory :=
  CoreConfig.wfVar_implies_wfEval _
    (core_star_preserves_cfg_wfVar π φ h_wf_ext hstar
      (show CoreConfig.wfVar (.stmts ss ρ) from hwf₀))

theorem core_wfCong_preserved_stmt
    (h_wf_ext : WFFactoryExtension φ)
    {s : Statement} {ρ : Env Expression} {c₂ : CoreConfig}
    (hwf₀ : WellFormedCoreEvalCong ρ.factory)
    (hstar : CoreStepStar π φ (.stmt s ρ) c₂) :
    WellFormedCoreEvalCong c₂.getEnv.factory :=
  CoreConfig.wfCong_implies_wfEval _
    (core_star_preserves_cfg_wfCong π φ h_wf_ext hstar
      (show CoreConfig.wfCong (.stmt s ρ) from hwf₀))

theorem core_wfCong_preserved_stmts
    (h_wf_ext : WFFactoryExtension φ)
    {ss : List Statement} {ρ : Env Expression} {c₂ : CoreConfig}
    (hwf₀ : WellFormedCoreEvalCong ρ.factory)
    (hstar : CoreStepStar π φ (.stmts ss ρ) c₂) :
    WellFormedCoreEvalCong c₂.getEnv.factory :=
  CoreConfig.wfCong_implies_wfEval _
    (core_star_preserves_cfg_wfCong π φ h_wf_ext hstar
      (show CoreConfig.wfCong (.stmts ss ρ) from hwf₀))

theorem core_wfExprCongr_preserved_stmt
    (h_wf_ext : WFFactoryExtension φ)
    {s : Statement} {ρ : Env Expression} {c₂ : CoreConfig}
    (hwf₀ : @Imperative.WellFormedSemanticEvalExprCongr Expression _ ρ.factory)
    (hstar : CoreStepStar π φ (.stmt s ρ) c₂) :
    @Imperative.WellFormedSemanticEvalExprCongr Expression _ c₂.getEnv.factory :=
  CoreConfig.wfExprCongr_implies_wfEval _
    (core_star_preserves_cfg_wfExprCongr π φ h_wf_ext hstar
      (show CoreConfig.wfExprCongr (.stmt s ρ) from hwf₀))

theorem core_wfExprCongr_preserved_stmts
    (h_wf_ext : WFFactoryExtension φ)
    {ss : List Statement} {ρ : Env Expression} {c₂ : CoreConfig}
    (hwf₀ : @Imperative.WellFormedSemanticEvalExprCongr Expression _ ρ.factory)
    (hstar : CoreStepStar π φ (.stmts ss ρ) c₂) :
    @Imperative.WellFormedSemanticEvalExprCongr Expression _ c₂.getEnv.factory :=
  CoreConfig.wfExprCongr_implies_wfEval _
    (core_star_preserves_cfg_wfExprCongr π φ h_wf_ext hstar
      (show CoreConfig.wfExprCongr (.stmts ss ρ) from hwf₀))

/-! ## projectStore and expression evaluation -/

/-- If an expression evaluates in the projected store, it evaluates identically
    in the full store. The projected store only removes variables, and expression
    evaluation depends only on the variables it references.-/
theorem eval_projectStore_to_full
    {f : Expression.Factory} {σ₀ σ : SemanticStore Expression}
    {e : Expression.Expr} {v : Expression.Expr}
    (h_eval : Expression.eval f (projectStore σ₀ σ) e = some v)
    (h_wfStore : WellFormedStore σ f)
    (h_wfCong : WellFormedCoreEvalCong f)
    (h_wfVar : WellFormedSemanticEvalVar (P := Expression) f)
    (h_wfExprCongr : WellFormedSemanticEvalExprCongr (P := Expression) f) :
    Expression.eval f σ e = some v := by
  have h_wfStoreProj : WellFormedStore (projectStore σ₀ σ) f := by
    intro x w hx
    simp only [projectStore] at hx
    split at hx
    · exact h_wfStore x w hx
    · exact absurd hx (by simp)
  have h_def := EvalExpressionIsDefined h_wfStoreProj h_wfCong h_wfVar
    (show (Expression.eval f (projectStore σ₀ σ) e).isSome from by rw [h_eval]; simp)
  have h_agree : ∀ x ∈ HasFvars.getFvars e, (projectStore σ₀ σ) x = σ x := by
    intro x hx
    have h_x_def : (projectStore σ₀ σ x).isSome = true := h_def x hx
    simp only [projectStore] at h_x_def ⊢
    split
    · rfl
    · next h_neg => simp [h_neg] at h_x_def
  rw [← h_wfExprCongr e (projectStore σ₀ σ) σ h_agree]; exact h_eval

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

private theorem coreIsAtAssert_of_inv_mem
    {g m inv body md} {ρ : Env Expression} {lbl e}
    (hmem : (lbl, e) ∈ inv) :
    coreIsAtAssert (.stmt (.loop g m inv body md) ρ) ⟨lbl, e⟩ := hmem

private theorem coreIsAtAssert_seq_of_inner
    {inner : CoreConfig} {ss a}
    (h : coreIsAtAssert inner a) : coreIsAtAssert (.seq inner ss) a := h

private theorem coreIsAtAssert_block_of_inner
    {label} {σ_parent} {e_parent} {inner : CoreConfig} {a}
    (h : coreIsAtAssert inner a) : coreIsAtAssert (.block label σ_parent e_parent inner) a := h

private theorem evalCommand_failure_implies_assert_ff
    {π : String → Option Procedure} {φ : Expression.Factory → PureFunc Expression → Expression.Factory}
    {ρ : Env Expression} {c : Command} {σ'}
    (hcmd : EvalCommand π φ ρ.factory ρ.store c σ' true) :
    ∃ a : AssertId Expression,
      coreIsAtAssert (.stmt (.cmd c) ρ) a ∧
      Expression.eval ρ.factory ρ.store a.expr = some HasBool.ff := by
  cases hcmd with
  | cmd_sem heval =>
    cases heval with
    | eval_assert_fail hff _ => exact ⟨⟨_, _⟩, ⟨rfl, rfl⟩, hff⟩

theorem core_noFailure_preserved
    (c₁ c₂ : CoreConfig)
    (hvalid : ∀ (a : AssertId Expression) (cfg : CoreConfig),
      CoreStepStar π φ c₁ cfg →
      coreIsAtAssert cfg a →
      Expression.eval cfg.getEnv.factory cfg.getStore a.expr = some HasBool.tt)
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
        evalCommand_failure_implies_assert_ff
        coreIsAtAssert_of_inv_mem
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
