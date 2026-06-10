/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.DL.Imperative.CmdSemantics
import all Strata.DL.Imperative.CmdSemantics
import all Strata.DL.Imperative.Cmd
public import Strata.DL.Imperative.Stmt
import all Strata.DL.Util.ListUtils

---------------------------------------------------------------------

namespace Imperative

public section

section

variable (P : PureExpr)

theorem isDefinedCons :
  isDefined σ [v] →
  isDefined σ vs2 →
  isDefined σ (v :: vs2) := by
  intros Hd1 Hd2
  simp [isDefined] at *
  simp [Option.isSome] at *
  split <;> simp_all

theorem isDefinedApp :
  isDefined σ vs1 →
  isDefined σ vs2 →
  isDefined σ (vs1 ++ vs2) := by
  intros Hd1 Hd2
  simp [isDefined] at *
  intros id Hin
  simp [Option.isSome] at *
  cases Hin with
  | inl Hin =>
    split <;> simp
    specialize Hd1 id Hin; simp_all
  | inr Hin =>
    split <;> simp
    specialize Hd2 id Hin; simp_all

theorem isDefinedCons' :
  isDefined σ (h :: t) →
  isDefined σ [h] ∧ isDefined σ t := by simp [isDefined] at *

theorem isDefinedApp' :
  isDefined σ (t1 ++ t2) →
  isDefined σ t1 ∧ isDefined σ t2 := by
  intros Hd
  simp [isDefined] at *
  apply And.intro
  . intros x Hin
    apply Hd; left; assumption
  . intros x Hin
    apply Hd; right; assumption

theorem isNotDefinedCons :
  isNotDefined σ [v] →
  isNotDefined σ vs2 →
  isNotDefined σ (v :: vs2) := by
  intros Hd1 Hd2
  simp [isNotDefined] at *
  simp_all

theorem isNotDefinedApp :
  isNotDefined σ vs1 →
  isNotDefined σ vs2 →
  isNotDefined σ (vs1 ++ vs2) := by
  intros Hd1 Hd2
  simp [isNotDefined] at *
  intros id Hin
  cases Hin with
  | inl Hin =>
    specialize Hd1 id Hin; simp_all
  | inr Hin =>
    specialize Hd2 id Hin; simp_all

theorem isNotDefinedCons' :
  isNotDefined σ (h :: t) →
  isNotDefined σ [h] ∧ isNotDefined σ t := by simp [isNotDefined] at *

theorem isNotDefinedApp' :
  isNotDefined σ (t1 ++ t2) →
  isNotDefined σ t1 ∧ isNotDefined σ t2 := by
  intros Hd
  simp [isNotDefined] at *
  apply And.intro
  . intros x Hin
    apply Hd; left; assumption
  . intros x Hin
    apply Hd; right; assumption

/-! ### Store Substitution Properties -/

theorem substSwapId (substs : List (P.Ident × P.Ident)) :
  (substSwap (substSwap substs)) = substs := by
  simp [substSwap]

theorem substStoresFlip :
  substStores σ₁ σ₂ substs →
  substStores σ₂ σ₁ (substSwap substs) := by
  intros Hsub
  simp [substStores, substSwap] at *
  intros k1 k2 x2 x1 Hin Heq1 Heq2
  simp_all
  apply Eq.symm
  apply Hsub
  exact Hin

theorem substStoresFlip' :
  substStores σ₂ σ₁ (substSwap substs) →
  substStores σ₁ σ₂ substs := by
  intros Hsub
  have Hsub' := substStoresFlip Hsub
  simp [substSwapId] at Hsub'
  exact Hsub'

theorem substDefinedFlip :
  substDefined σ₁ σ₂ substs →
  substDefined σ₂ σ₁ (substSwap substs) := by
  intros Hsub
  simp [substDefined, substSwap] at *
  intros k1 k2 x2 x1 Hin Heq1 Heq2
  simp_all
  exact And.comm.mp (Hsub k2 k1 Hin)

theorem substDefinedFlip' :
  substDefined σ₂ σ₁ (substSwap substs) →
  substDefined σ₁ σ₂ substs := by
  intros Hsub
  have Hsub' := substDefinedFlip Hsub
  simp [substSwapId] at Hsub'
  exact Hsub'

theorem invStoresComm :
  invStores σ₁ σ₂ ks →
  invStores σ₂ σ₁ ks := by
  intros Hinv
  simp [invStores] at *
  apply substStoresFlip'
  simp [substSwap]
  assumption

theorem invStoresExceptComm :
  invStoresExcept σ₁ σ₂ ks →
  invStoresExcept σ₂ σ₁ ks := by
  intros Hinv ks' Hdisj
  simp [invStoresExcept] at *
  exact invStoresComm (Hinv ks' Hdisj)

end section

theorem InitStateDefCons
  {P : PureExpr} {σ σ' : SemanticStore P}
  {vs : List P.Ident} {e : P.Expr} {v : P.Ident} :
  isDefined σ vs →
  InitState P σ v e σ' →
  isDefined σ' (v::vs) := by
  intros Hdef Heval
  cases Heval with
  | init Hold HH Hsome =>
  simp [isDefined, HH] at *
  intros v' Hv'
  have Heq: ¬ v = v' :=by
    false_or_by_contra; rename_i Heq
    specialize Hdef v' Hv'
    simp_all
  specialize Hsome v' Heq
  specialize Hdef v'
  simp_all

theorem InitStateDefMonotone
  {P : PureExpr} {σ σ' : SemanticStore P}
  {vs : List P.Ident} {e : P.Expr} {v : P.Ident} :
  isDefined σ vs →
  InitState P σ v e σ' →
  isDefined σ' vs := by
  intros Hdef Heval
  exact (isDefinedCons' (InitStateDefCons Hdef Heval)).right

theorem UpdateStateDef
  {P : PureExpr} {σ σ' : SemanticStore P}
  {e : P.Expr} {v : P.Ident} :
  UpdateState P σ v e σ' →
  isDefined σ [v] ∧ isDefined σ' [v] := by
  intro Heval
  cases Heval with
  | update Hold HH Hsome =>
  simp_all [isDefined]

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

theorem UpdateStateUniqueResult
  {P : PureExpr} {σ σ' σ'': SemanticStore P}
  {e : P.Expr} {v : P.Ident} :
  UpdateState P σ v e σ' →
  UpdateState P σ v e σ'' →
  σ' = σ'' := by
  intro Hu1 Hu2
  cases Hu1; cases Hu2
  rename_i Hfa1 _ _ _ Hfa2 _
  ext v' e'
  by_cases h: v' = v
  simp_all
  rw[eq_comm] at h
  specialize Hfa1 v' h
  specialize Hfa2 v' h
  simp_all

theorem InitStateUniqueResult
  {P : PureExpr} {σ σ' σ'': SemanticStore P}
  {e : P.Expr} {v : P.Ident} :
  InitState P σ v e σ' →
  InitState P σ v e σ'' →
  σ' = σ'' := by
  intro Hu1 Hu2
  cases Hu1; cases Hu2
  rename_i Hfa1 _ _ Hfa2 _
  ext v' e'
  by_cases h: v' = v
  simp_all
  rw[eq_comm] at h
  specialize Hfa1 v' h
  specialize Hfa2 v' h
  simp_all

/-! ### Assert / set commutation -/

theorem eval_assert_store_cst
  [HasFvar P] [HasBool P] [HasBoolOps P] [HasOps P]:
  EvalCmd P δ σ (.assert l e md) σ' f → σ = σ' := by
  intros Heval; cases Heval with
  | eval_assert_pass _ => rfl
  | eval_assert_fail _ => rfl

theorem UpdateStateComm {P: PureExpr} {x1 x2: P.Ident} {σ σ' σ'' σ1 σ2: SemanticStore P} {v1 v2: P.Expr}
  [DecidableEq P.Ident]:
  ¬ x1 = x2 →
  UpdateState P σ x1 v1 σ1 →
  UpdateState P σ1 x2 v2 σ' →
  UpdateState P σ x2 v2 σ2 →
  UpdateState P σ2 x1 v1 σ'' →
  σ' = σ'' := by
  intro Hneq Hu1 Hu2 Hu3 Hu4
  cases Hu1; cases Hu2; cases Hu3; cases Hu4
  ext i e
  rename_i Hfa1 _ _ _ Hfa2 _ _ _ Hfa3 _ _ _ Hfa4 _
  simp at Hfa1 Hfa2 Hfa3 Hfa4
  rw[Eq.comm] at Hneq
  by_cases Heq1: x1 = i
  simp_all
  by_cases Heq2: x2 = i
  rw[Eq.comm] at Hneq
  specialize Hfa4 x2 Hneq
  simp_all
  specialize Hfa1 i Heq1
  specialize Hfa2 i Heq2
  specialize Hfa3 i Heq2
  specialize Hfa4 i Heq1
  simp_all

theorem UpdateState_InitStateComm {P: PureExpr} {x1 x2: P.Ident} {σ σ' σ'' σ1 σ2: SemanticStore P} {v1 v2: P.Expr}
  [DecidableEq P.Ident]:
  ¬ x1 = x2 →
  UpdateState P σ x1 v1 σ1 →
  InitState P σ1 x2 v2 σ' →
  InitState P σ x2 v2 σ2 →
  UpdateState P σ2 x1 v1 σ'' →
  σ' = σ'' := by
  intro Hneq Hu1 Hu2 Hu3 Hu4
  cases Hu1; cases Hu2; cases Hu3; cases Hu4
  ext i e
  rename_i Hfa1 _ _ Hfa2 _ _ Hfa3 _ _ _ Hfa4 _
  simp at Hfa1 Hfa2 Hfa3 Hfa4
  rw[Eq.comm] at Hneq
  by_cases Heq1: x1 = i
  simp_all
  by_cases Heq2: x2 = i
  rw[Eq.comm] at Hneq
  specialize Hfa4 x2 Hneq
  simp_all
  specialize Hfa1 i Heq1
  specialize Hfa2 i Heq2
  specialize Hfa3 i Heq2
  specialize Hfa4 i Heq1
  simp_all

theorem semantic_eval_eq_of_eval_cmd_set_unrelated_var
  [HasVarsImp P (Cmd P)] [HasFvar P] [HasBool P] [HasBoolOps P] [HasFvars P] [HasOps P]:
  WellFormedSemanticEvalExprCongr δ →
  ¬ v ∈ HasFvars.getFvars e →
  EvalCmd P δ σ (Cmd.set v (.det e') md) σ' f →
  δ σ e = δ σ' e := by
  intro Hwf Hnin Heval
  unfold WellFormedSemanticEvalExprCongr at Hwf
  specialize Hwf e σ σ'
  have: ∀ (v : P.Ident), v ∈ HasFvars.getFvars e → σ v = σ' v := by
    cases Heval
    rename_i Hu
    cases Hu
    rename_i Hfa _
    intro v' Hv'
    ext e'
    by_cases Hc: ¬ v = v'
    specialize Hfa v' Hc
    simp_all
    simp_all
  exact Hwf this

theorem eval_cmd_set_comm'
  [HasVarsImp P (List (Stmt P (Cmd P)))] [HasVarsImp P (Cmd P)]
  [HasFvar P] [HasBool P] [HasBoolOps P] [HasOps P] [DecidableEq P.Ident] :
  ¬ x1 = x2 →
  δ σ v1 = δ σ2 v1 →
  δ σ v2 = δ σ1 v2 →
  EvalCmd P δ σ (Cmd.set x1 (.det v1) md1) σ1 f1 →
  EvalCmd P δ σ1 (Cmd.set x2 (.det v2) md2) σ' f2 →
  EvalCmd P δ σ (Cmd.set x2 (.det v2) md2') σ2 f3 →
  EvalCmd P δ σ2 (Cmd.set x1 (.det v1) md1') σ'' f4 →
  σ' = σ'' := by
  intro Hneq Heq1 Heq2 Hs1 Hs2 Hs3 Hs4
  cases Hs1 with | eval_set _ Hu1 _ =>
  cases Hs2 with | eval_set _ Hu2 _ =>
  cases Hs3 with | eval_set _ Hu3 _ =>
  cases Hs4 with | eval_set _ Hu4 _ =>
  simp_all
  exact UpdateStateComm Hneq Hu1 Hu2 Hu3 Hu4

theorem eval_cmd_set_comm
  [HasVarsImp P (List (Stmt P (Cmd P)))] [HasVarsImp P (Cmd P)]
  [HasFvar P] [HasBool P] [HasBoolOps P] [HasFvars P] [HasOps P] [DecidableEq P.Ident]:
  WellFormedSemanticEvalExprCongr δ →
  ¬ x1 = x2 →
  ¬ x1 ∈ HasFvars.getFvars v2 →
  ¬ x2 ∈ HasFvars.getFvars v1 →
  EvalCmd P δ σ (Cmd.set x1 (.det v1) md1) σ1 f1 →
  EvalCmd P δ σ1 (Cmd.set x2 (.det v2) md2) σ' f2 →
  EvalCmd P δ σ (Cmd.set x2 (.det v2) md2') σ2 f3 →
  EvalCmd P δ σ2 (Cmd.set x1 (.det v1) md1') σ'' f4 →
  σ' = σ'' := by
  intro Hwf Hneq Hnin1 Hnin2 Hs1 Hs2 Hs3 Hs4
  have Heval2:= semantic_eval_eq_of_eval_cmd_set_unrelated_var Hwf Hnin1 Hs1
  have Heval1:= semantic_eval_eq_of_eval_cmd_set_unrelated_var Hwf Hnin2 Hs3
  exact eval_cmd_set_comm' Hneq Heval1 Heval2 Hs1 Hs2 Hs3 Hs4

end -- public section
