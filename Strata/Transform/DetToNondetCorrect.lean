/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.DL.Imperative.Stmt
import Strata.DL.Imperative.StmtSemantics
import Strata.DL.Imperative.NondetStmt
import Strata.DL.Imperative.NondetStmtSemantics
import Strata.Transform.DetToNondet

/-! # Deterministic-to-Nondeterministic Transformation Correctness Proof
  This file contains the main proof that the deterministic-to-nondeterministic
  transformation is semantics preserving (see `StmtToNondetStmtCorrect` and
  `StmtToNondetStmtCorrect`)
  -/

open Imperative Boogie

/--
  The proof implementation for `StmtToNondetStmtCorrect` and
  `StmtToNondetStmtCorrect`.

  Since the definitions involve mutual recursion, `Nat.strongRecOn` is used to
  do induction on the size of the structure (see `StmtToNondetCorrect`). From
  experience, `mutual` theorems in Lean sometimes does not work well with
  implicit arguments, and it can be hard to find the cause from the generic
  error message similar to "(kernel) application type mismatch".
-/
theorem StmtToNondetCorrect [HasVal P] [HasFvar P] [HasBool P] [HasBoolVal P] [HasBoolNeg P] :
  WellFormedSemanticEvalBool δ →
  WellFormedSemanticEvalVal δ →
  (∀ st,
    Stmt.sizeOf st ≤ m →
    EvalStmt P (Cmd P) (EvalCmd P) δ σ₀ σ st σ' →
    EvalNondetStmt P (Cmd P) (EvalCmd P) δ σ₀ σ (StmtToNondetStmt st) σ') ∧
  (∀ ss,
    Stmts.sizeOf ss ≤ m →
    EvalStmts P (Cmd P) (EvalCmd P) δ σ₀ σ ss σ' →
    EvalNondetStmt P (Cmd P) (EvalCmd P) δ σ₀ σ (StmtsToNondetStmt ss) σ') := by
  intros Hwfb Hwfvl
  apply Nat.strongRecOn (motive := λ m ↦
    ∀ σ₀ σ σ',
    (∀ st,
      Stmt.sizeOf st ≤ m →
      EvalStmt P (Cmd P) (EvalCmd P) δ σ₀ σ st σ' →
      EvalNondetStmt P (Cmd P) (EvalCmd P) δ σ₀ σ (StmtToNondetStmt st) σ') ∧
    (∀ ss,
      Stmts.sizeOf ss ≤ m →
      EvalStmts P (Cmd P) (EvalCmd P) δ σ₀ σ ss σ' →
      EvalNondetStmt P (Cmd P) (EvalCmd P) δ σ₀ σ (StmtsToNondetStmt ss) σ')
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
      | ite_true_sem Htrue Hwfb Heval =>
        next c t e =>
        cases Heval with
        | block_sem Heval =>
        specialize ih (Stmts.sizeOf t.ss) (by simp_all; omega)
        refine EvalNondetStmt.choice_left_sem Hwfb ?_
        apply EvalNondetStmt.seq_sem
        . apply EvalNondetStmt.cmd_sem
          exact EvalCmd.eval_assume Htrue Hwfb
          simp [isDefinedOver, HasVarsImp.modifiedVars, Cmd.modifiedVars, isDefined]
        . apply (ih _ _ _).2
          omega
          assumption
      | ite_false_sem Hfalse Hwfb Heval =>
        next c t e =>
        cases Heval with
        | block_sem Heval =>
        specialize ih (Stmts.sizeOf e.ss) (by simp_all; omega)
        refine EvalNondetStmt.choice_right_sem Hwfb ?_
        apply EvalNondetStmt.seq_sem
        . apply EvalNondetStmt.cmd_sem
          refine EvalCmd.eval_assume ?_ Hwfb
          simp [WellFormedSemanticEvalBool] at Hwfb
          exact (Hwfb σ₀ σ c).2.mp Hfalse
          simp [isDefinedOver, HasVarsImp.modifiedVars, Cmd.modifiedVars, isDefined]
        . apply (ih _ _ _).2
          omega
          assumption
    case goto =>
      -- because goto has no semantics now, it also does not correspond to anything in the nondeterministic semantics
      cases Heval
    case loop =>
      -- because loop has no semantics now, it also does not correspond to anything in the nondeterministic semantics
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
        simp [WellFormedSemanticEvalVal] at Hwfvl
        have Hval := wfbv.bool_is_val.1
        have Hv := Hwfvl.2 HasBool.tt σ₀ σ Hval
        exact Hv
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

/-- Proof that the Deterministic-to-nondeterministic transformation is correct
for a single (deterministic) statement -/
theorem StmtToNondetStmtCorrect
  [HasVal P] [HasFvar P] [HasBool P] [HasBoolVal P] [HasBoolNeg P] :
  WellFormedSemanticEvalBool δ →
  WellFormedSemanticEvalVal δ →
  EvalStmt P (Cmd P) (EvalCmd P) δ σ₀ σ st σ' →
  EvalNondetStmt P (Cmd P) (EvalCmd P) δ σ₀ σ (StmtToNondetStmt st) σ' := by
  intros Hwfb Hwfv Heval
  apply (StmtToNondetCorrect Hwfb Hwfv (m:=st.sizeOf)).1 <;> simp_all

/-- Proof that the Deterministic-to-nondeterministic transformation is correct
for multiple (deterministic) statements -/
theorem StmtsToNondetStmtCorrect
  [HasVal P] [HasFvar P] [HasBool P] [HasBoolVal P] [HasBoolNeg P] :
  WellFormedSemanticEvalBool δ →
  WellFormedSemanticEvalVal δ →
  EvalStmts P (Cmd P) (EvalCmd P) δ σ₀ σ ss σ' →
  EvalNondetStmt P (Cmd P) (EvalCmd P) δ σ₀ σ (StmtsToNondetStmt ss) σ' := by
  intros Hwfb Hwfv Heval
  apply (StmtToNondetCorrect Hwfb Hwfv (m:=Stmts.sizeOf ss)).2 <;> simp_all
