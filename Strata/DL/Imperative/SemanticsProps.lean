/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.DL.Imperative.CmdSemantics
import Strata.DL.Imperative.StmtSemantics

namespace Imperative

theorem eval_assert_store_cst
  [HasFvar P] [HasBool P] [HasBoolNeg P]:
  EvalCmd P δ δP σ₀ σ (.assert l e md) σ' → σ = σ' := by
  intros Heval; cases Heval with | eval_assert _ => rfl

theorem eval_stmt_assert_store_cst
  [HasVarsImp P (List (Stmt P (Cmd P)))] [HasVarsImp P (Cmd P)] [HasFvar P] [HasVal P] [HasBool P] [HasBoolNeg P] :
  EvalStmt P (Cmd P) (EvalCmd P) δ δP σ₀ σ (.cmd (Cmd.assert l e md)) σ' → σ = σ' := by
  intros Heval; cases Heval with | cmd_sem Hcmd => exact eval_assert_store_cst Hcmd

theorem eval_stmts_assert_store_cst
  [HasVarsImp P (List (Stmt P (Cmd P)))] [HasVarsImp P (Cmd P)] [HasFvar P] [HasVal P] [HasBool P] [HasBoolNeg P] :
  EvalStmts P (Cmd P) (EvalCmd P) δ δP σ₀ σ [(.cmd (Cmd.assert l e md))] σ' → σ = σ' := by
  intros Heval; cases Heval with
  | stmts_some_sem H1 H2 =>
    cases H1 with
    | cmd_sem H3 =>
      cases H2 with
      | stmts_none_sem => exact eval_assert_store_cst H3

theorem eval_stmt_assert_eq_of_pure_expr_eq
  [HasVarsImp P (List (Stmt P (Cmd P)))] [HasFvar P] [HasVal P] [HasBool P] [HasBoolNeg P] :
  WellFormedSemanticEvalBool δ δP →
  (EvalStmt P (Cmd P) (EvalCmd P) δ δP σ₀ σ (.cmd (Cmd.assert l1 e md1)) σ' ↔
  EvalStmt P (Cmd P) (EvalCmd P) δ δP σ₀ σ (.cmd (Cmd.assert l2 e md2)) σ') := by
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
  WellFormedSemanticEvalBool δ δP →
  EvalStmts P (Cmd P) (EvalCmd P) δ δP σ₀ σ (.cmd (.assert l1 e md1) :: cmds) σ' →
  EvalStmts P (Cmd P) (EvalCmd P) δ δP σ₀ σ cmds σ' := by
  intros Hwf Heval
  cases Heval with
  | @stmts_some_sem _ _ _ _ _ σ1 _ _ Has1 Has2 =>
    rw [← eval_stmt_assert_store_cst Has1] at Has2
    assumption

theorem assert_elim
  [HasVarsImp P (List (Stmt P (Cmd P)))] [HasFvar P] [HasVal P] [HasBool P] [HasBoolNeg P] :
  WellFormedSemanticEvalBool δ δP →
  EvalStmts P (Cmd P) (EvalCmd P) δ δP σ₀ σ (.cmd (.assert l1 e md1) :: [.cmd (.assert l2 e md2)]) σ' →
  EvalStmts P (Cmd P) (EvalCmd P) δ δP σ₀ σ [.cmd (.assert l3 e md3)] σ' := by
  intro Hwf Heval
  have Heval := eval_stmts_assert_elim Hwf Heval
  rw [eval_stmts_singleton] at *
  exact (eval_stmt_assert_eq_of_pure_expr_eq Hwf).mp Heval

