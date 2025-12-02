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
theorem StmtToNondetCorrect
  [HasVal P] [HasFvar P] [HasBool P] [HasBoolVal P] [HasNot P] :
  WellFormedSemanticEvalBool δ →
  WellFormedSemanticEvalVal δ →
  (∀ st,
    Stmt.sizeOf st ≤ m →
    EvalStmt P (Cmd P) (EvalCmd P) δ σ st σ' →
    EvalNondetStmt P (Cmd P) (EvalCmd P) δ σ (StmtToNondetStmt st) σ') ∧
  (∀ ss,
    Block.sizeOf ss ≤ m →
    EvalBlock P (Cmd P) (EvalCmd P) δ σ ss σ' →
    EvalNondetStmt P (Cmd P) (EvalCmd P) δ σ (BlockToNondetStmt ss) σ') := by
  intros Hwfb Hwfvl
  apply Nat.strongRecOn (motive := λ m ↦
    ∀ σ σ',
    (∀ st,
      Stmt.sizeOf st ≤ m →
      EvalStmt P (Cmd P) (EvalCmd P) δ σ st σ' →
      EvalNondetStmt P (Cmd P) (EvalCmd P) δ σ (StmtToNondetStmt st) σ') ∧
    (∀ ss,
      Block.sizeOf ss ≤ m →
      EvalBlock P (Cmd P) (EvalCmd P) δ σ ss σ' →
      EvalNondetStmt P (Cmd P) (EvalCmd P) δ σ (BlockToNondetStmt ss) σ')
  )
  intros n ih σ σ'
  refine ⟨?_, ?_⟩
  . intros st Hsz Heval
    match st with
    | .cmd c =>
      cases Heval
      constructor <;> simp_all
    | .block _ bss =>
      cases Heval with
      | block_sem Heval =>
      next label b =>
      specialize ih (Block.sizeOf bss) (by simp_all; omega)
      apply (ih _ _).2
      omega
      assumption
    | .ite c tss ess =>
      cases Heval with
      | ite_true_sem Htrue Hwfb Heval =>
        specialize ih (Block.sizeOf tss) (by simp_all; omega)
        refine EvalNondetStmt.choice_left_sem Hwfb ?_
        apply EvalNondetStmt.seq_sem
        . apply EvalNondetStmt.cmd_sem
          exact EvalCmd.eval_assume Htrue Hwfb
          simp [isDefinedOver, HasVarsImp.modifiedVars, Cmd.modifiedVars, isDefined]
        . apply (ih _ _).2
          omega
          assumption
      | ite_false_sem Hfalse Hwfb Heval =>
        next c t e =>
        specialize ih (Block.sizeOf ess) (by simp_all; omega)
        refine EvalNondetStmt.choice_right_sem Hwfb ?_
        apply EvalNondetStmt.seq_sem
        . apply EvalNondetStmt.cmd_sem
          refine EvalCmd.eval_assume ?_ Hwfb
          simp [WellFormedSemanticEvalBool] at Hwfb
          exact (Hwfb σ c).2.mp Hfalse
          simp [isDefinedOver, HasVarsImp.modifiedVars, Cmd.modifiedVars, isDefined]
        . apply (ih _ _).2
          omega
          assumption
    | .goto _ =>
      -- because goto has no semantics now, it also does not correspond to anything in the nondeterministic semantics
      cases Heval
    | .loop _ _ _ _ =>
      -- because loop has no semantics now, it also does not correspond to anything in the nondeterministic semantics
      cases Heval
  . intros ss Hsz Heval
    cases ss <;>
    cases Heval
    case stmts_none_sem =>
      simp [BlockToNondetStmt]
      constructor
      constructor
      next wfvl wffv wfb wfbv wfn =>
        expose_names
        simp [WellFormedSemanticEvalVal] at Hwfvl
        have Hval := wfbv.bool_is_val.1
        have Hv := Hwfvl.2 HasBool.tt σ Hval
        exact Hv
      assumption
      intros id Hin
      simp [HasVarsImp.modifiedVars, Cmd.modifiedVars] at Hin
    case stmts_some_sem h t σ'' Heval Hevals =>
      simp [BlockToNondetStmt]
      simp [Block.sizeOf] at Hsz
      specialize ih (h.sizeOf + Block.sizeOf t) (by omega)
      constructor
      . apply (ih _ _).1
        omega
        exact Heval
      . apply (ih _ _).2
        omega
        exact Hevals

/-- Proof that the Deterministic-to-nondeterministic transformation is correct
for a single (deterministic) statement -/
theorem StmtToNondetStmtCorrect
  [HasVal P] [HasFvar P] [HasBool P] [HasBoolVal P] [HasNot P] :
  WellFormedSemanticEvalBool δ →
  WellFormedSemanticEvalVal δ →
  EvalStmt P (Cmd P) (EvalCmd P) δ σ st σ' →
  EvalNondetStmt P (Cmd P) (EvalCmd P) δ σ (StmtToNondetStmt st) σ' := by
  intros Hwfb Hwfv Heval
  apply (StmtToNondetCorrect Hwfb Hwfv (m:=st.sizeOf)).1 <;> simp_all

/-- Proof that the Deterministic-to-nondeterministic transformation is correct
for multiple (deterministic) statements -/
theorem BlockToNondetStmtCorrect
  [HasVal P] [HasFvar P] [HasBool P] [HasBoolVal P] [HasNot P] :
  WellFormedSemanticEvalBool δ →
  WellFormedSemanticEvalVal δ →
  EvalBlock P (Cmd P) (EvalCmd P) δ σ ss σ' →
  EvalNondetStmt P (Cmd P) (EvalCmd P) δ σ (BlockToNondetStmt ss) σ' := by
  intros Hwfb Hwfv Heval
  apply (StmtToNondetCorrect Hwfb Hwfv (m:=Block.sizeOf ss)).2 <;> simp_all
