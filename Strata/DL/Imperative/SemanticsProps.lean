/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.DL.Imperative.CmdSemantics
import Strata.DL.Imperative.StmtSemantics

namespace Imperative

theorem eval_assert_store_cst
  [HasFvar P] [HasBool P] [HasBoolNeg P]:
  EvalCmd P δ σ₀ σ (.assert l e md) σ' → σ = σ' := by
  intros Heval; cases Heval with | eval_assert _ => rfl

theorem eval_stmt_assert_store_cst
  [HasVarsImp P (List (Stmt P (Cmd P)))] [HasVarsImp P (Cmd P)] [HasFvar P] [HasVal P] [HasBool P] [HasBoolNeg P] :
  EvalStmt P (Cmd P) (EvalCmd P) δ σ₀ σ (.cmd (Cmd.assert l e md)) σ' → σ = σ' := by
  intros Heval; cases Heval with | cmd_sem Hcmd => exact eval_assert_store_cst Hcmd

theorem eval_stmts_assert_store_cst
  [HasVarsImp P (List (Stmt P (Cmd P)))] [HasVarsImp P (Cmd P)] [HasFvar P] [HasVal P] [HasBool P] [HasBoolNeg P] :
  EvalStmts P (Cmd P) (EvalCmd P) δ σ₀ σ [(.cmd (Cmd.assert l e md))] σ' → σ = σ' := by
  intros Heval; cases Heval with
  | stmts_some_sem H1 H2 =>
    cases H1 with
    | cmd_sem H3 =>
      cases H2 with
      | stmts_none_sem => exact eval_assert_store_cst H3

theorem eval_stmt_assert_eq_of_pure_expr_eq
  [HasVarsImp P (List (Stmt P (Cmd P)))] [HasFvar P] [HasVal P] [HasBool P] [HasBoolNeg P] :
  WellFormedSemanticEvalBool δ →
  (EvalStmt P (Cmd P) (EvalCmd P) δ σ₀ σ (.cmd (Cmd.assert l1 e md1)) σ' ↔
  EvalStmt P (Cmd P) (EvalCmd P) δ σ₀ σ (.cmd (Cmd.assert l2 e md2)) σ') := by
  intro Hwf
  constructor <;>
  (
    intro Heval
    rw [← eval_stmt_assert_store_cst Heval]
    cases Heval
    apply EvalStmt.cmd_sem _ (by assumption)
    rename_i Heval
    cases Heval
    exact EvalCmd.eval_assert (by assumption) Hwf
  )

theorem eval_stmts_assert_elim
  [HasVarsImp P (List (Stmt P (Cmd P)))] [HasFvar P] [HasVal P] [HasBool P] [HasBoolNeg P] :
  WellFormedSemanticEvalBool δ →
  EvalStmts P (Cmd P) (EvalCmd P) δ σ₀ σ (.cmd (.assert l1 e md1) :: cmds) σ' →
  EvalStmts P (Cmd P) (EvalCmd P) δ σ₀ σ cmds σ' := by
  intros Hwf Heval
  cases Heval with
  | @stmts_some_sem _ _ _ _ σ1 _ _ Has1 Has2 =>
    rw [← eval_stmt_assert_store_cst Has1] at Has2
    assumption

theorem assert_elim
  [HasVarsImp P (List (Stmt P (Cmd P)))] [HasFvar P] [HasVal P] [HasBool P] [HasBoolNeg P] :
  WellFormedSemanticEvalBool δ →
  EvalStmts P (Cmd P) (EvalCmd P) δ σ₀ σ (.cmd (.assert l1 e md1) :: [.cmd (.assert l2 e md2)]) σ' →
  EvalStmts P (Cmd P) (EvalCmd P) δ σ₀ σ [.cmd (.assert l3 e md3)] σ' := by
  intro Hwf Heval
  have Heval := eval_stmts_assert_elim Hwf Heval
  rw [eval_stmts_singleton] at *
  exact (eval_stmt_assert_eq_of_pure_expr_eq Hwf).mp Heval

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
  [HasVarsImp P (Cmd P)] [HasVarsPure P P.Expr]
  [HasFvar P] [HasVal P] [HasBool P] [HasBoolNeg P]:
  WellFormedSemanticEvalExprCongr δ →
  ¬ v ∈ HasVarsPure.getVars e →
  EvalCmd P δ σ₀ σ (Cmd.set v e') σ' →
  δ σ₀ σ e = δ σ₀ σ' e := by
  intro Hwf Hnin Heval
  unfold WellFormedSemanticEvalExprCongr at Hwf
  specialize Hwf e σ₀ σ σ'
  have: ∀ (v : P.Ident), v ∈ HasVarsPure.getVars e → σ v = σ' v := by
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
  [HasFvar P] [HasVal P] [HasBool P] [HasBoolNeg P] [DecidableEq P.Ident] :
  ¬ x1 = x2 →
  δ σ₀ σ v1 = δ σ₀ σ2 v1 →
  δ σ₀ σ v2 = δ σ₀ σ1 v2 →
  EvalCmd P δ σ₀ σ (Cmd.set x1 v1) σ1 →
  EvalCmd P δ σ₀ σ1 (Cmd.set x2 v2) σ' →
  EvalCmd P δ σ₀ σ (Cmd.set x2 v2) σ2 →
  EvalCmd P δ σ₀ σ2 (Cmd.set x1 v1) σ'' →
  σ' = σ'' := by
  intro Hneq Heq1 Heq2 Hs1 Hs2 Hs3 Hs4
  cases Hs1; cases Hs2; cases Hs3; cases Hs4
  rename_i Hu1 _ _ _ Hu2 _ _ _ Hu3 _ _ _ Hu4
  simp_all
  exact UpdateStateComm Hneq Hu1 Hu2 Hu3 Hu4

theorem eval_cmd_set_comm
  [HasVarsImp P (List (Stmt P (Cmd P)))] [HasVarsImp P (Cmd P)] [HasVarsPure P P.Expr]
  [HasFvar P] [HasVal P] [HasBool P] [HasBoolNeg P] [DecidableEq P.Ident]:
  WellFormedSemanticEvalExprCongr δ →
  ¬ x1 = x2 →
  ¬ x1 ∈ HasVarsPure.getVars v2 →
  ¬ x2 ∈ HasVarsPure.getVars v1 →
  EvalCmd P δ σ₀ σ (Cmd.set x1 v1) σ1 →
  EvalCmd P δ σ₀ σ1 (Cmd.set x2 v2) σ' →
  EvalCmd P δ σ₀ σ (Cmd.set x2 v2) σ2 →
  EvalCmd P δ σ₀ σ2 (Cmd.set x1 v1) σ'' →
  σ' = σ'' := by
  intro Hwf Hneq Hnin1 Hnin2 Hs1 Hs2 Hs3 Hs4
  have Heval2:= semantic_eval_eq_of_eval_cmd_set_unrelated_var Hwf Hnin1 Hs1
  have Heval1:= semantic_eval_eq_of_eval_cmd_set_unrelated_var Hwf Hnin2 Hs3
  exact eval_cmd_set_comm' Hneq Heval1 Heval2 Hs1 Hs2 Hs3 Hs4

theorem eval_stmt_set_comm
  [HasVarsImp P (List (Stmt P (Cmd P)))] [HasVarsImp P (Cmd P)] [HasVarsPure P P.Expr]
  [HasFvar P] [HasVal P] [HasBool P] [HasBoolNeg P] [DecidableEq P.Ident]:
  WellFormedSemanticEvalExprCongr δ →
  ¬ x1 = x2 →
  ¬ x1 ∈ HasVarsPure.getVars v2 →
  ¬ x2 ∈ HasVarsPure.getVars v1 →
  EvalStmt P (Cmd P) (EvalCmd P) δ σ₀ σ (.cmd (Cmd.set x1 v1)) σ1 →
  EvalStmt P (Cmd P) (EvalCmd P) δ σ₀ σ1 (.cmd (Cmd.set x2 v2)) σ' →
  EvalStmt P (Cmd P) (EvalCmd P) δ σ₀ σ (.cmd (Cmd.set x2 v2)) σ2 →
  EvalStmt P (Cmd P) (EvalCmd P) δ σ₀ σ2 (.cmd (Cmd.set x1 v1)) σ'' →
  σ' = σ'' := by
  intro Hwf Hneq Hnin1 Hnin2 Hs1 Hs2 Hs3 Hs4
  cases Hs1; cases Hs2; cases Hs3; cases Hs4
  rename_i Hs1 _ Hs2 _ Hs3 _ Hs4
  exact eval_cmd_set_comm Hwf Hneq Hnin1 Hnin2 Hs1 Hs2 Hs3 Hs4

theorem eval_stmts_set_comm
  [HasVarsImp P (List (Stmt P (Cmd P)))] [HasVarsImp P (Cmd P)] [HasVarsPure P P.Expr]
  [HasFvar P] [HasVal P] [HasBool P] [HasBoolNeg P] [DecidableEq P.Ident] :
  WellFormedSemanticEvalExprCongr δ →
  ¬ x1 = x2 →
  ¬ x1 ∈ HasVarsPure.getVars v2 →
  ¬ x2 ∈ HasVarsPure.getVars v1 →
  EvalStmts P (Cmd P) (EvalCmd P) δ σ₀ σ [(.cmd (Cmd.set x1 v1)), (.cmd (Cmd.set x2 v2))] σ' →
  EvalStmts P (Cmd P) (EvalCmd P) δ σ₀ σ [(.cmd (Cmd.set x2 v2)), (.cmd (Cmd.set x1 v1))] σ'' →
  σ' = σ'' := by
  intro Hwf Hneq Hnin1 Hnin2 Hss1 Hss2
  cases Hss1; cases Hss2
  rw[eval_stmts_singleton] at *
  rename_i Hs1 Hs2 _ Hs3 Hs4
  exact eval_stmt_set_comm Hwf Hneq Hnin1 Hnin2 Hs1 Hs2 Hs3 Hs4
