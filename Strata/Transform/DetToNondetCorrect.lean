/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.DL.Imperative.Stmt
import Strata.DL.Imperative.StmtSemantics
import Strata.DL.Imperative.NondetStmt
import Strata.DL.Imperative.NondetStmtSemantics
import Strata.Transform.DetToNondet

open Imperative Boogie

theorem StmtToNondetCorrect [HasVal P] [HasFvar P] [HasBool P] [HasBoolVal P] [HasBoolNeg P] :
  WellFormedSemanticEvalBool δ δP →
  WellFormedSemanticEvalVal δ σ₀ σ →
  (∀ st,
    Stmt.sizeOf st ≤ m →
    EvalStmt P (Cmd P) (EvalCmd P) δ δP σ₀ σ st σ' →
    EvalNondetStmt P (Cmd P) (EvalCmd P) δ δP σ₀ σ (StmtToNondetStmt st) σ') ∧
  (∀ ss,
    Stmts.sizeOf ss ≤ m →
    EvalStmts P (Cmd P) (EvalCmd P) δ δP σ₀ σ ss σ' →
    EvalNondetStmt P (Cmd P) (EvalCmd P) δ δP σ₀ σ (StmtsToNondetStmt ss) σ') := by
  intros Hwfb Hwfvl
  apply Nat.strongRecOn (motive := λ m ↦
    ∀ σ₀ σ σ',
    (∀ st,
      Stmt.sizeOf st ≤ m →
      EvalStmt P (Cmd P) (EvalCmd P) δ δP σ₀ σ st σ' →
      EvalNondetStmt P (Cmd P) (EvalCmd P) δ δP σ₀ σ (StmtToNondetStmt st) σ') ∧
    (∀ ss,
      Stmts.sizeOf ss ≤ m →
      EvalStmts P (Cmd P) (EvalCmd P) δ δP σ₀ σ ss σ' →
      EvalNondetStmt P (Cmd P) (EvalCmd P) δ δP σ₀ σ (StmtsToNondetStmt ss) σ')
  )
  intros n ih σ₀ σ σ'
  refine ⟨?_, ?_⟩
  . intros st Hsz Heval
    cases st <;> simp [StmtToNondetStmt]
    case cmd c =>
      cases Heval
      constructor <;> simp_all
    case block =>
      cases Heval with
      | block_sem Heval =>
      next label b =>
      cases Heval with
      | block_sem Heval =>
      specialize ih (Stmts.sizeOf b.ss) (by simp_all; omega)
      apply (ih _ _ _).2
      omega
      assumption
    case ite =>
      cases Heval with
      | ite_true_sem Htrue Heval Hwf =>
        next c t e =>
        cases Heval with
        | block_sem Heval =>
        specialize ih (Stmts.sizeOf t.ss) (by simp_all; omega)
        refine EvalNondetStmt.choice_left_sem ?_ Hwfb
        apply EvalNondetStmt.seq_sem
        . apply EvalNondetStmt.cmd_sem
          exact EvalCmd.eval_assert Htrue Hwfb
          simp [isDefinedOver, HasVarsImp.modifiedVars, Cmd.modifiedVars, isDefined]
        . apply (ih _ _ _).2
          omega
          assumption
      | ite_false_sem Hfalse Heval Hwf =>
        next c t e =>
        cases Heval with
        | block_sem Heval =>
        specialize ih (Stmts.sizeOf e.ss) (by simp_all; omega)
        refine EvalNondetStmt.choice_right_sem ?_ Hwfb
        apply EvalNondetStmt.seq_sem
        . apply EvalNondetStmt.cmd_sem
          refine EvalCmd.eval_assert ?_ Hwfb
          simp [WellFormedSemanticEvalBool] at Hwfb
          have HH := (Hwfb σ₀ σ c).1.2.2.mp Hfalse
          assumption
          simp [isDefinedOver, HasVarsImp.modifiedVars, Cmd.modifiedVars, isDefined]
        . apply (ih _ _ _).2
          omega
          assumption
    case goto =>
      -- because goto has no semantics now, it also does not correspond to anything in the nondeterministic semantics
      cases Heval
  . intros ss Hsz Heval
    cases ss <;>
    cases Heval
    case stmts_none_sem =>
      simp [StmtsToNondetStmt]
      constructor
      constructor
      next wfvl wffv wfb wfbv wfn =>
        expose_names
        simp [WellFormedSemanticEvalBool] at Hwfb
        simp [WellFormedSemanticEvalVal] at Hwfvl
        have Hval := wfbv.bool_is_val.1
        have Hv := Hwfvl.2.2.2 HasBool.tt σ₀ σ Hval
        have Heq := (Hwfb σ₀ σ HasBool.tt).2.1
        exact Heq.mp Hv
      assumption
      intros id Hin
      simp [HasVarsImp.modifiedVars, Cmd.modifiedVars] at Hin
    case stmts_some_sem h t σ'' Heval Hevals =>
      simp [StmtsToNondetStmt]
      simp [Stmts.sizeOf] at Hsz
      specialize ih (h.sizeOf + Stmts.sizeOf t) (by omega)
      constructor
      . apply (ih _ _ _).1
        omega
        exact Heval
      . apply (ih _ _ _).2
        omega
        exact Hevals

theorem StmtToNondetStmtCorrect
  [HasVal P] [HasFvar P] [HasBool P] [HasBoolVal P] [HasBoolNeg P] :
  WellFormedSemanticEvalBool δ δP →
  WellFormedSemanticEvalVal δ σ₀ σ →
  EvalStmt P (Cmd P) (EvalCmd P) δ δP σ₀ σ st σ' →
  EvalNondetStmt P (Cmd P) (EvalCmd P) δ δP σ₀ σ (StmtToNondetStmt st) σ' := by
  intros Hwfb Hwfv Heval
  apply (StmtToNondetCorrect Hwfb Hwfv (m:=st.sizeOf)).1 <;> simp_all

theorem StmtsToNondetStmtCorrect
  [HasVal P] [HasFvar P] [HasBool P] [HasBoolVal P] [HasBoolNeg P] :
  WellFormedSemanticEvalBool δ δP →
  WellFormedSemanticEvalVal δ σ₀ σ →
  EvalStmts P (Cmd P) (EvalCmd P) δ δP σ₀ σ ss σ' →
  EvalNondetStmt P (Cmd P) (EvalCmd P) δ δP σ₀ σ (StmtsToNondetStmt ss) σ' := by
  intros Hwfb Hwfv Heval
  apply (StmtToNondetCorrect Hwfb Hwfv (m:=Stmts.sizeOf ss)).2 <;> simp_all
