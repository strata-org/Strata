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
  `BlockToNondetStmtCorrect`)

  Note: The proof requires that the program contains no function declarations
  (`noFuncDecl`). This is because `funcDecl` changes the evaluator `δ`, but the
  nondeterministic statements don't have function declarations.
  -/

open Imperative Core

/-- Helper for proving noFuncDecl preserves δ for blocks, given IH for statements. -/
private theorem noFuncDecl_preserves_δ_block_aux
  [HasVal P] [HasFvar P] [HasBool P] [HasNot P] [DecidableEq P.Ident]
  (extendEval : ExtendEval P)
  (ss : Block P (Cmd P)) (δ δ' : SemanticEval P) (σ σ' : SemanticStore P)
  (ih : ∀ s, s ∈ ss → ∀ (δ δ' : SemanticEval P) (σ σ' : SemanticStore P),
    Stmt.noFuncDecl s → EvalStmt P (Cmd P) (EvalCmd P) extendEval δ σ s σ' δ' → δ' = δ)
  (Hno : Block.noFuncDecl ss)
  (Heval : EvalBlock P (Cmd P) (EvalCmd P) extendEval δ σ ss σ' δ') :
  δ' = δ := by
  induction ss generalizing σ σ' δ δ' with
  | nil =>
    cases Heval with
    | stmts_none_sem => rfl
  | cons h t ih_list =>
    cases Heval with
    | stmts_some_sem Heval_h Heval_t =>
    next σ₁ δ₁ =>
    simp [Block.noFuncDecl] at Hno
    have h_mem : h ∈ h :: t := by simp
    have Hδ₁ : δ₁ = δ := ih h h_mem δ δ₁ σ σ₁ Hno.1 Heval_h
    have ih_t : ∀ s, s ∈ t → ∀ (δ δ' : SemanticEval P) (σ σ' : SemanticStore P),
      Stmt.noFuncDecl s → EvalStmt P (Cmd P) (EvalCmd P) extendEval δ σ s σ' δ' → δ' = δ :=
      fun s hs => ih s (by simp [hs])
    have Hδ' : δ' = δ₁ := ih_list δ₁ δ' σ₁ σ' ih_t Hno.2 Heval_t
    simp [Hδ₁, Hδ']

/-- When a statement has no function declarations, evaluating it preserves the evaluator. -/
theorem EvalStmt_noFuncDecl_preserves_δ
  [HasVal P] [HasFvar P] [HasBool P] [HasNot P] [DecidableEq P.Ident]
  (extendEval : ExtendEval P)
  (st : Stmt P (Cmd P)) (δ δ' : SemanticEval P) (σ σ' : SemanticStore P) :
  Stmt.noFuncDecl st →
  EvalStmt P (Cmd P) (EvalCmd P) extendEval δ σ st σ' δ' →
  δ' = δ := by
  induction st using Stmt.inductionOn generalizing δ δ' σ σ' with
  | cmd_case c =>
    intros Hno Heval
    cases Heval with
    | cmd_sem _ _ => rfl
  | block_case label bss md ih =>
    intros Hno Heval
    cases Heval with
    | block_sem Heval =>
    simp [Stmt.noFuncDecl] at Hno
    exact noFuncDecl_preserves_δ_block_aux extendEval bss _ _ _ _ ih Hno Heval
  | ite_case cond tss ess md ih_t ih_e =>
    intros Hno Heval
    cases Heval with
    | ite_true_sem _ _ Heval =>
      simp [Stmt.noFuncDecl] at Hno
      exact noFuncDecl_preserves_δ_block_aux extendEval tss _ _ _ _ ih_t Hno.1 Heval
    | ite_false_sem _ _ Heval =>
      simp [Stmt.noFuncDecl] at Hno
      exact noFuncDecl_preserves_δ_block_aux extendEval ess _ _ _ _ ih_e Hno.2 Heval
  | loop_case guard measure invariant body md ih =>
    intros Hno Heval
    cases Heval
  | goto_case label md =>
    intros Hno Heval
    cases Heval
  | funcDecl_case decl md =>
    intros Hno Heval
    simp [Stmt.noFuncDecl] at Hno

/-- When a block has no function declarations, evaluating it preserves the evaluator. -/
theorem EvalBlock_noFuncDecl_preserves_δ
  [HasVal P] [HasFvar P] [HasBool P] [HasNot P] [DecidableEq P.Ident]
  (extendEval : ExtendEval P)
  (ss : Block P (Cmd P)) (δ δ' : SemanticEval P) (σ σ' : SemanticStore P) :
  Block.noFuncDecl ss →
  EvalBlock P (Cmd P) (EvalCmd P) extendEval δ σ ss σ' δ' →
  δ' = δ := by
  induction ss generalizing δ δ' σ σ' with
  | nil =>
    intros Hno Heval
    cases Heval with
    | stmts_none_sem => rfl
  | cons h t ih =>
    intros Hno Heval
    cases Heval with
    | stmts_some_sem Heval_h Heval_t =>
    next σ₁ δ₁ =>
    simp [Block.noFuncDecl] at Hno
    have Hδ₁ : δ₁ = δ := EvalStmt_noFuncDecl_preserves_δ extendEval h δ δ₁ σ σ₁ Hno.1 Heval_h
    have Hδ' : δ' = δ₁ := ih δ₁ δ' σ₁ σ' Hno.2 Heval_t
    simp [Hδ₁, Hδ']

/--
  The proof implementation for `StmtToNondetStmtCorrect` and
  `BlockToNondetStmtCorrect`.

  Since the definitions involve mutual recursion, `Nat.strongRecOn` is used to
  do induction on the size of the structure (see `StmtToNondetCorrect`). From
  experience, `mutual` theorems in Lean sometimes does not work well with
  implicit arguments, and it can be hard to find the cause from the generic
  error message similar to "(kernel) application type mismatch".

  The proof requires that the program contains no function declarations.
  When `noFuncDecl` holds, the evaluator `δ` is preserved (δ' = δ).
-/
theorem StmtToNondetCorrect
  [HasVal P] [HasFvar P] [HasBool P] [HasBoolVal P] [HasNot P] [DecidableEq P.Ident]
  (extendEval : ExtendEval P) :
  WellFormedSemanticEvalBool δ →
  WellFormedSemanticEvalVal δ →
  (∀ st,
    Stmt.sizeOf st ≤ m →
    Stmt.noFuncDecl st →
    EvalStmt P (Cmd P) (EvalCmd P) extendEval δ σ st σ' δ →
    EvalNondetStmt P (Cmd P) (EvalCmd P) δ σ (StmtToNondetStmt st) σ') ∧
  (∀ ss,
    Block.sizeOf ss ≤ m →
    Block.noFuncDecl ss →
    EvalBlock P (Cmd P) (EvalCmd P) extendEval δ σ ss σ' δ →
    EvalNondetStmt P (Cmd P) (EvalCmd P) δ σ (BlockToNondetStmt ss) σ') := by
  intros Hwfb Hwfvl
  apply Nat.strongRecOn (motive := λ m ↦
    ∀ σ σ',
    (∀ st,
      Stmt.sizeOf st ≤ m →
      Stmt.noFuncDecl st →
      EvalStmt P (Cmd P) (EvalCmd P) extendEval δ σ st σ' δ →
      EvalNondetStmt P (Cmd P) (EvalCmd P) δ σ (StmtToNondetStmt st) σ') ∧
    (∀ ss,
      Block.sizeOf ss ≤ m →
      Block.noFuncDecl ss →
      EvalBlock P (Cmd P) (EvalCmd P) extendEval δ σ ss σ' δ →
      EvalNondetStmt P (Cmd P) (EvalCmd P) δ σ (BlockToNondetStmt ss) σ')
  )
  intros n ih σ σ'
  refine ⟨?_, ?_⟩
  . intros st Hsz Hno Heval
    match st with
    | .cmd c =>
      cases Heval with
      | cmd_sem Hcmd Hdef =>
        exact EvalNondetStmt.cmd_sem Hcmd Hdef
    | .block _ bss _ =>
      cases Heval with
      | block_sem Heval =>
      simp [Stmt.noFuncDecl] at Hno
      have Hδ : _ = δ := EvalBlock_noFuncDecl_preserves_δ extendEval bss δ _ σ σ' Hno Heval
      specialize ih (Block.sizeOf bss) (by simp_all; omega)
      apply (ih _ _).2
      omega
      exact Hno
      rw [← Hδ]; exact Heval
    | .ite c tss ess _ =>
      cases Heval with
      | ite_true_sem Htrue Hwfb' Heval =>
        simp [Stmt.noFuncDecl] at Hno
        have Hδ : _ = δ := EvalBlock_noFuncDecl_preserves_δ extendEval tss δ _ σ σ' Hno.1 Heval
        specialize ih (Block.sizeOf tss) (by simp_all; omega)
        refine EvalNondetStmt.choice_left_sem Hwfb ?_
        apply EvalNondetStmt.seq_sem
        . apply EvalNondetStmt.cmd_sem
          exact EvalCmd.eval_assume Htrue Hwfb
          simp [isDefinedOver, HasVarsImp.modifiedVars, Cmd.modifiedVars, isDefined]
        . apply (ih _ _).2
          omega
          exact Hno.1
          rw [← Hδ]; exact Heval
      | ite_false_sem Hfalse Hwfb' Heval =>
        simp [Stmt.noFuncDecl] at Hno
        have Hδ : _ = δ := EvalBlock_noFuncDecl_preserves_δ extendEval ess δ _ σ σ' Hno.2 Heval
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
          exact Hno.2
          rw [← Hδ]; exact Heval
    | .goto _ _ =>
      cases Heval
    | .loop _ _ _ _ _ =>
      cases Heval
    | .funcDecl _ _ =>
      simp [Stmt.noFuncDecl] at Hno
  . intros ss Hsz Hno Heval
    cases ss <;>
    cases Heval
    case stmts_none_sem =>
      simp [BlockToNondetStmt]
      constructor
      constructor
      · simp [WellFormedSemanticEvalVal] at Hwfvl
        have Hval : HasVal.value (HasBool.tt (P := P)) := HasBoolVal.bool_is_val.1
        exact Hwfvl.2 HasBool.tt σ Hval
      · assumption
      · intros id Hin
        simp [HasVarsImp.modifiedVars, Cmd.modifiedVars] at Hin
    case stmts_some_sem h t σ'' δ₁ Heval Hevals =>
      simp [BlockToNondetStmt]
      simp [Block.sizeOf] at Hsz
      simp [Block.noFuncDecl] at Hno
      have Hδ₁ : δ₁ = δ := EvalStmt_noFuncDecl_preserves_δ extendEval h δ δ₁ σ σ'' Hno.1 Heval
      subst Hδ₁
      -- Now δ₁ is replaced by δ everywhere
      specialize ih (h.sizeOf + Block.sizeOf t) (by omega)
      constructor
      . apply (ih _ _).1
        omega
        exact Hno.1
        exact Heval
      . apply (ih _ _).2
        omega
        exact Hno.2
        exact Hevals

/-- Proof that the Deterministic-to-nondeterministic transformation is correct
for a single (deterministic) statement that contains no function declarations. -/
theorem StmtToNondetStmtCorrect
  [HasVal P] [HasFvar P] [HasBool P] [HasBoolVal P] [HasNot P] [DecidableEq P.Ident]
  (extendEval : ExtendEval P) :
  WellFormedSemanticEvalBool δ →
  WellFormedSemanticEvalVal δ →
  Stmt.noFuncDecl st →
  EvalStmt P (Cmd P) (EvalCmd P) extendEval δ σ st σ' δ →
  EvalNondetStmt P (Cmd P) (EvalCmd P) δ σ (StmtToNondetStmt st) σ' := by
  intros Hwfb Hwfv Hno Heval
  exact (StmtToNondetCorrect extendEval Hwfb Hwfv (m:=st.sizeOf)).1 st (Nat.le_refl _) Hno Heval

/-- Proof that the Deterministic-to-nondeterministic transformation is correct
for multiple (deterministic) statements that contain no function declarations. -/
theorem BlockToNondetStmtCorrect
  [HasVal P] [HasFvar P] [HasBool P] [HasBoolVal P] [HasNot P] [DecidableEq P.Ident]
  (extendEval : ExtendEval P) :
  WellFormedSemanticEvalBool δ →
  WellFormedSemanticEvalVal δ →
  Block.noFuncDecl ss →
  EvalBlock P (Cmd P) (EvalCmd P) extendEval δ σ ss σ' δ →
  EvalNondetStmt P (Cmd P) (EvalCmd P) δ σ (BlockToNondetStmt ss) σ' := by
  intros Hwfb Hwfv Hno Heval
  exact (StmtToNondetCorrect extendEval Hwfb Hwfv (m:=Block.sizeOf ss)).2 ss (Nat.le_refl _) Hno Heval
