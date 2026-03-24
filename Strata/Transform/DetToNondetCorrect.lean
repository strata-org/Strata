/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.DL.Imperative.Stmt
public import Strata.DL.Imperative.StmtSemantics
public import Strata.DL.Imperative.NondetStmt
public import Strata.DL.Imperative.NondetStmtSemantics
public import Strata.Transform.DetToNondet
import all Strata.DL.Imperative.Stmt
import all Strata.DL.Imperative.NondetStmt
import all Strata.DL.Imperative.CmdSemantics
import all Strata.DL.Imperative.Cmd
import all Strata.DL.Imperative.HasVars
import all Strata.Transform.DetToNondet

/-! # Deterministic-to-Nondeterministic Transformation Correctness Proof
  This file contains the main proof that the deterministic-to-nondeterministic
  transformation is semantics preserving (see `StmtToNondetStmtCorrect` and
  `BlockToNondetStmtCorrect`)

  Note: The proof requires that the program contains no function declarations
  (`noFuncDecl`). This is because `funcDecl` changes the evaluator `δ`, but the
  nondeterministic statements don't have function declarations.
  -/

public section

open Imperative Core

/-- Helper for proving noFuncDecl preserves eval for blocks, given IH for statements. -/
private theorem noFuncDecl_preserves_eval_block_aux
  [HasVal P] [HasFvar P] [HasBool P] [HasNot P] [DecidableEq P.Ident]
  (extendEval : ExtendEval P)
  (ss : Block P (Cmd P)) (ρ ρ' : Env P)
  (ih : ∀ s, s ∈ ss → ∀ (ρ ρ' : Env P),
    Stmt.noFuncDecl s → EvalStmt P (Cmd P) (EvalCmd P) extendEval ρ s ρ' → ρ'.eval = ρ.eval)
  (Hno : Block.noFuncDecl ss)
  (Heval : EvalBlock P (Cmd P) (EvalCmd P) extendEval ρ ss ρ') :
  ρ'.eval = ρ.eval := by
  induction ss generalizing ρ ρ' with
  | nil =>
    cases Heval with
    | stmts_none_sem => rfl
  | cons h t ih_list =>
    cases Heval with
    | stmts_some_sem Heval_h Heval_t =>
    next ρ₁ =>
    simp [Block.noFuncDecl] at Hno
    have h_mem : h ∈ h :: t := by simp
    have Hδ₁ : ρ₁.eval = ρ.eval := ih h h_mem ρ ρ₁ Hno.1 Heval_h
    have ih_t : ∀ s, s ∈ t → ∀ (ρ ρ' : Env P),
      Stmt.noFuncDecl s → EvalStmt P (Cmd P) (EvalCmd P) extendEval ρ s ρ' → ρ'.eval = ρ.eval :=
      fun s hs => ih s (by simp [hs])
    have Hδ' : ρ'.eval = ρ₁.eval := ih_list ρ₁ ρ' ih_t Hno.2 Heval_t
    simp [Hδ₁, Hδ']

/-- When a statement has no function declarations, evaluating it preserves the evaluator. -/
theorem EvalStmt_noFuncDecl_preserves_eval
  [HasVal P] [HasFvar P] [HasBool P] [HasNot P] [DecidableEq P.Ident]
  (extendEval : ExtendEval P)
  (st : Stmt P (Cmd P)) (ρ ρ' : Env P) :
  Stmt.noFuncDecl st →
  EvalStmt P (Cmd P) (EvalCmd P) extendEval ρ st ρ' →
  ρ'.eval = ρ.eval := by
  induction st using Stmt.inductionOn generalizing ρ ρ' with
  | cmd_case c =>
    intros Hno Heval
    cases Heval with
    | cmd_sem _ _ => rfl
  | block_case label bss md ih =>
    intros Hno Heval
    cases Heval with
    | block_sem Heval =>
    simp [Stmt.noFuncDecl] at Hno
    exact noFuncDecl_preserves_eval_block_aux extendEval bss _ _ ih Hno Heval
  | ite_case cond tss ess md ih_t ih_e =>
    intros Hno Heval
    cases Heval with
    | ite_true_sem _ _ Heval =>
      simp [Stmt.noFuncDecl] at Hno
      exact noFuncDecl_preserves_eval_block_aux extendEval tss _ _ ih_t Hno.1 Heval
    | ite_false_sem _ _ Heval =>
      simp [Stmt.noFuncDecl] at Hno
      exact noFuncDecl_preserves_eval_block_aux extendEval ess _ _ ih_e Hno.2 Heval
  | loop_case guard measure invariant body md ih =>
    intros Hno Heval
    cases Heval
  | exit_case label md =>
    intros Hno Heval
    cases Heval
  | funcDecl_case decl md =>
    intros Hno Heval
    simp [Stmt.noFuncDecl] at Hno
  | typeDecl_case tc md =>
    intros Hno Heval
    cases Heval with
    | typeDecl_sem => rfl

/-- When a block has no function declarations, evaluating it preserves the evaluator. -/
theorem EvalBlock_noFuncDecl_preserves_eval
  [HasVal P] [HasFvar P] [HasBool P] [HasNot P] [DecidableEq P.Ident]
  (extendEval : ExtendEval P)
  (ss : Block P (Cmd P)) (ρ ρ' : Env P) :
  Block.noFuncDecl ss →
  EvalBlock P (Cmd P) (EvalCmd P) extendEval ρ ss ρ' →
  ρ'.eval = ρ.eval := by
  induction ss generalizing ρ ρ' with
  | nil =>
    intros Hno Heval
    cases Heval with
    | stmts_none_sem => rfl
  | cons h t ih =>
    intros Hno Heval
    cases Heval with
    | stmts_some_sem Heval_h Heval_t =>
    next ρ₁ =>
    simp [Block.noFuncDecl] at Hno
    have Hδ₁ : ρ₁.eval = ρ.eval := EvalStmt_noFuncDecl_preserves_eval extendEval h ρ ρ₁ Hno.1 Heval_h
    have Hδ' : ρ'.eval = ρ₁.eval := ih ρ₁ ρ' Hno.2 Heval_t
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
  When `noFuncDecl` holds, the evaluator is preserved (ρ'.eval = ρ.eval).
-/
theorem StmtToNondetCorrect
  [HasVal P] [HasFvar P] [HasBool P] [HasBoolVal P] [HasNot P] [DecidableEq P.Ident]
  (extendEval : ExtendEval P) :
  WellFormedSemanticEvalBool δ →
  WellFormedSemanticEvalVal δ →
  (∀ st,
    Stmt.sizeOf st ≤ m →
    Stmt.noFuncDecl st →
    ∀ (ρ ρ' : Env P), ρ.eval = δ → ρ'.eval = δ →
    EvalStmt P (Cmd P) (EvalCmd P) extendEval ρ st ρ' →
    EvalNondetStmt P (Cmd P) (EvalCmd P) δ ρ.store (StmtToNondetStmt st) ρ'.store) ∧
  (∀ ss,
    Block.sizeOf ss ≤ m →
    Block.noFuncDecl ss →
    ∀ (ρ ρ' : Env P), ρ.eval = δ → ρ'.eval = δ →
    EvalBlock P (Cmd P) (EvalCmd P) extendEval ρ ss ρ' →
    EvalNondetStmt P (Cmd P) (EvalCmd P) δ ρ.store (BlockToNondetStmt ss) ρ'.store) := by
  intros Hwfb Hwfvl
  apply Nat.strongRecOn (motive := λ m ↦
    (∀ st,
      Stmt.sizeOf st ≤ m →
      Stmt.noFuncDecl st →
      ∀ (ρ ρ' : Env P), ρ.eval = δ → ρ'.eval = δ →
      EvalStmt P (Cmd P) (EvalCmd P) extendEval ρ st ρ' →
      EvalNondetStmt P (Cmd P) (EvalCmd P) δ ρ.store (StmtToNondetStmt st) ρ'.store) ∧
    (∀ ss,
      Block.sizeOf ss ≤ m →
      Block.noFuncDecl ss →
      ∀ (ρ ρ' : Env P), ρ.eval = δ → ρ'.eval = δ →
      EvalBlock P (Cmd P) (EvalCmd P) extendEval ρ ss ρ' →
      EvalNondetStmt P (Cmd P) (EvalCmd P) δ ρ.store (BlockToNondetStmt ss) ρ'.store)
  )
  intros n ih
  refine ⟨?_, ?_⟩
  . intros st Hsz Hno ρ ρ' Hρδ Hρ'δ Heval
    match st with
    | .cmd c =>
      cases Heval with
      | cmd_sem Hcmd Hdef =>
        simp at *
        rw [Hρδ] at Hcmd
        exact EvalNondetStmt.cmd_sem Hcmd Hdef
    | .block _ bss _ =>
      cases Heval with
      | block_sem Heval =>
      simp [Stmt.noFuncDecl] at Hno
      specialize ih (Block.sizeOf bss) (by simp_all; omega)
      apply ih.2
      · omega
      · exact Hno
      · exact Hρδ
      · exact Hρ'δ
      · exact Heval
    | .ite c tss ess _ =>
      cases Heval with
      | ite_true_sem Htrue Hwfb' Heval =>
        simp [Stmt.noFuncDecl] at Hno
        specialize ih (Block.sizeOf tss) (by simp_all; omega)
        rw [Hρδ] at Htrue
        refine EvalNondetStmt.choice_left_sem Hwfb ?_
        apply EvalNondetStmt.seq_sem
        . apply EvalNondetStmt.cmd_sem
          exact EvalCmd.eval_assume Htrue Hwfb
          simp [isDefinedOver, HasVarsImp.modifiedVars, Cmd.modifiedVars, isDefined]
        . apply ih.2
          · omega
          · exact Hno.1
          · exact Hρδ
          · exact Hρ'δ
          · exact Heval
      | ite_false_sem Hfalse Hwfb' Heval =>
        simp [Stmt.noFuncDecl] at Hno
        specialize ih (Block.sizeOf ess) (by simp_all; omega)
        rw [Hρδ] at Hfalse
        refine EvalNondetStmt.choice_right_sem Hwfb ?_
        apply EvalNondetStmt.seq_sem
        . apply EvalNondetStmt.cmd_sem
          refine EvalCmd.eval_assume ?_ Hwfb
          exact (Hwfb ρ.store c).2.mp Hfalse
          simp [isDefinedOver, HasVarsImp.modifiedVars, Cmd.modifiedVars, isDefined]
        . apply ih.2
          · omega
          · exact Hno.2
          · exact Hρδ
          · exact Hρ'δ
          · exact Heval
    | .exit _ _ =>
      cases Heval
    | .loop _ _ _ _ _ =>
      cases Heval
    | .funcDecl _ _ =>
      simp [Stmt.noFuncDecl] at Hno
    | .typeDecl _ md =>
      cases Heval with
      | typeDecl_sem =>
        simp [StmtToNondetStmt]
        apply EvalNondetStmt.cmd_sem
        · exact EvalCmd.eval_assume
            (by have ⟨Htt, _⟩ := HasBoolVal.bool_is_val (P := P); exact Hwfvl.2 HasBool.tt ρ.store Htt)
            Hwfb
        · simp [isDefinedOver, HasVarsImp.modifiedVars, Cmd.modifiedVars, isDefined]
  . intros ss Hsz Hno ρ ρ' Hρδ Hρ'δ Heval
    cases ss <;>
    cases Heval
    case stmts_none_sem =>
      simp [BlockToNondetStmt]
      apply EvalNondetStmt.cmd_sem
      · exact EvalCmd.eval_assume
          (by simp [WellFormedSemanticEvalVal] at Hwfvl
              have Hval : HasVal.value (HasBool.tt (P := P)) := HasBoolVal.bool_is_val.1
              exact Hwfvl.2 HasBool.tt ρ.store Hval)
          Hwfb
      · intros id Hin
        simp [HasVarsImp.modifiedVars, Cmd.modifiedVars] at Hin
    case stmts_some_sem h t ρ₁ Heval Hevals =>
      simp [BlockToNondetStmt]
      simp [Block.sizeOf] at Hsz
      simp [Block.noFuncDecl] at Hno
      have Hδ₁ : ρ₁.eval = ρ.eval := EvalStmt_noFuncDecl_preserves_eval extendEval h ρ ρ₁ Hno.1 Heval
      -- Now ρ₁.eval = ρ.eval = δ
      have Hρ₁δ : ρ₁.eval = δ := by rw [Hδ₁, Hρδ]
      specialize ih (h.sizeOf + Block.sizeOf t) (by omega)
      constructor
      . apply ih.1
        · omega
        · exact Hno.1
        · exact Hρδ
        · exact Hρ₁δ
        · exact Heval
      . apply ih.2
        · omega
        · exact Hno.2
        · exact Hρ₁δ
        · exact Hρ'δ
        · exact Hevals

/-- Proof that the Deterministic-to-nondeterministic transformation is correct
for a single (deterministic) statement that contains no function declarations. -/
theorem StmtToNondetStmtCorrect
  [HasVal P] [HasFvar P] [HasBool P] [HasBoolVal P] [HasNot P] [DecidableEq P.Ident]
  (extendEval : ExtendEval P) :
  WellFormedSemanticEvalBool δ →
  WellFormedSemanticEvalVal δ →
  Stmt.noFuncDecl st →
  ∀ (ρ ρ' : Env P), ρ.eval = δ → ρ'.eval = δ →
  EvalStmt P (Cmd P) (EvalCmd P) extendEval ρ st ρ' →
  EvalNondetStmt P (Cmd P) (EvalCmd P) δ ρ.store (StmtToNondetStmt st) ρ'.store := by
  intros Hwfb Hwfv Hno ρ ρ' Hρδ Hρ'δ Heval
  exact (StmtToNondetCorrect extendEval Hwfb Hwfv (m:=st.sizeOf)).1 st (Nat.le_refl _) Hno ρ ρ' Hρδ Hρ'δ Heval

/-- Proof that the Deterministic-to-nondeterministic transformation is correct
for multiple (deterministic) statements that contain no function declarations. -/
theorem BlockToNondetStmtCorrect
  [HasVal P] [HasFvar P] [HasBool P] [HasBoolVal P] [HasNot P] [DecidableEq P.Ident]
  (extendEval : ExtendEval P) :
  WellFormedSemanticEvalBool δ →
  WellFormedSemanticEvalVal δ →
  Block.noFuncDecl ss →
  ∀ (ρ ρ' : Env P), ρ.eval = δ → ρ'.eval = δ →
  EvalBlock P (Cmd P) (EvalCmd P) extendEval ρ ss ρ' →
  EvalNondetStmt P (Cmd P) (EvalCmd P) δ ρ.store (BlockToNondetStmt ss) ρ'.store := by
  intros Hwfb Hwfv Hno ρ ρ' Hρδ Hρ'δ Heval
  exact (StmtToNondetCorrect extendEval Hwfb Hwfv (m:=Block.sizeOf ss)).2 ss (Nat.le_refl _) Hno ρ ρ' Hρδ Hρ'δ Heval

end
