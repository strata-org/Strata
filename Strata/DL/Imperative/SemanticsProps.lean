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

theorem assert_elim
  [HasVarsImp P (List (Stmt P (Cmd P)))] [HasFvar P] [HasVal P] [HasBool P] [HasBoolNeg P] :
  WellFormedSemanticEvalBool δ δP →
  EvalStmts P (Cmd P) (EvalCmd P) δ δP σ₀ σ (.cmd (.assert l1 e md1) :: [.cmd (.assert l2 e md2)]) σ' →
  EvalStmts P (Cmd P) (EvalCmd P) δ δP σ₀ σ [.cmd (.assert l3 e md3)] σ' := by
  intros Hwf Heval
  cases Heval with
  | @stmts_some_sem _ _ _ _ _ σ1 _ _ Has1 Has2 =>
    cases Has1 with
    | cmd_sem Hcmd =>
      have H : EvalStmts P (Cmd P) (EvalCmd P) δ δP σ₀ σ' [] σ' := .stmts_none_sem
      apply EvalStmts.stmts_some_sem _ H
      apply EvalStmt.cmd_sem
      . cases Has2 with
        | @stmts_some_sem _ _ _ _ _ σ2 _ _ H1 H2 =>
          have Heq2 : σ2 = σ' := by cases H2 <;> rfl
          have Heq1 : σ1 = σ2 := by exact eval_stmt_assert_store_cst H1
          have Heq0 : σ = σ1 := by exact eval_assert_store_cst Hcmd
          simp [Heq0, Heq1, Heq2] at *
          apply EvalCmd.eval_assert
          cases Hcmd; assumption
          assumption
      . next Hdef =>
        intros v Hin
        apply Hdef v
        simp [HasVarsImp.modifiedVars, Cmd.modifiedVars] at *
