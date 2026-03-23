/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.DL.Imperative.Stmt
public import Strata.DL.Imperative.StmtSemanticsSmallStep
public import Strata.DL.Imperative.NondetStmt
public import Strata.DL.Imperative.NondetStmtSemantics
public import Strata.Transform.DetToNondet
import all Strata.DL.Imperative.Stmt
import all Strata.DL.Imperative.NondetStmt
import all Strata.DL.Imperative.CmdSemantics
import all Strata.DL.Imperative.Cmd
import all Strata.DL.Imperative.HasVars
import all Strata.Transform.DetToNondet
import all Strata.DL.Util.Relations

/-! # Deterministic-to-Nondeterministic Transformation Correctness (Small-Step)

This file proves that the deterministic-to-nondeterministic transformation
is semantics preserving with respect to the small-step operational semantics
(`StmtSemanticsSmallStep`).

The analogous big-step proof lives in `DetToNondetCorrect.lean`.

## Preconditions

- `noFuncDecl` — ensures δ is preserved throughout execution.
- Loops and exits are left as `sorry`.

## Sorry inventory

- `step_preserves_noFuncDecl` / `step_loop_enter` — loops skipped
- `invert_cons_terminal` — multi-step decomposition for cons lists
- `invert_block_terminal` — multi-step decomposition for blocks
- `StmtToNondetCorrectSmallStep` / `.cmd` — `isDefinedOver` obligation
  (present in big-step `EvalStmt.cmd_sem` but absent from small-step `StepStmt.step_cmd`)
- `StmtToNondetCorrectSmallStep` / `.loop`, `.exit` — skipped
-/

public section

open Imperative Core

/-! ## Configuration predicates -/

@[simp] def Config.noFuncDecl : Config P (Cmd P) → Bool
  | .stmt s _ _ => Stmt.noFuncDecl s
  | .stmts ss _ _ => Block.noFuncDecl ss
  | .terminal _ _ => true
  | .exiting _ _ _ => true
  | .block _ ss _ _ => Block.noFuncDecl ss

@[simp] def Config.getδ : Config P (Cmd P) → SemanticEval P
  | .stmt _ _ δ => δ
  | .stmts _ _ δ => δ
  | .terminal _ δ => δ
  | .exiting _ _ δ => δ
  | .block _ _ _ δ => δ

/-! ## δ-preservation under noFuncDecl -/

private theorem step_preserves_noFuncDecl
    [HasVal P] [HasFvar P] [HasBool P] [HasNot P] [DecidableEq P.Ident]
    [HasVarsImp P (List (Stmt P (Cmd P)))] [HasVarsImp P (Cmd P)]
    (extendEval : ExtendEval P)
    {c₁ c₂ : Config P (Cmd P)}
    (Hno : Config.noFuncDecl c₁ = true)
    (Hstep : StepStmt P (EvalCmd P) extendEval c₁ c₂) :
    Config.noFuncDecl c₂ = true := by
  induction Hstep with
  | step_cmd => simp [Config.noFuncDecl]
  | step_block => simp [Config.noFuncDecl, Stmt.noFuncDecl] at Hno ⊢; exact Hno
  | step_ite_true => simp [Config.noFuncDecl, Stmt.noFuncDecl] at Hno ⊢; exact Hno.1
  | step_ite_false => simp [Config.noFuncDecl, Stmt.noFuncDecl] at Hno ⊢; exact Hno.2
  | step_loop_enter => sorry
  | step_loop_exit => simp [Config.noFuncDecl]
  | step_exit => simp [Config.noFuncDecl]
  | step_funcDecl => simp [Config.noFuncDecl, Stmt.noFuncDecl] at Hno
  | step_typeDecl => simp [Config.noFuncDecl]
  | step_stmts_nil => simp [Config.noFuncDecl]
  | step_stmt_cons _ _ => simp [Config.noFuncDecl, Block.noFuncDecl] at Hno ⊢; exact Hno.2
  | step_stmt_cons_exit _ _ => simp [Config.noFuncDecl]
  | step_block_body _ ih =>
    simp [Config.noFuncDecl] at Hno ⊢
    exact ih (by simp [Config.noFuncDecl]; exact Hno)
  | step_block_done _ _ => simp [Config.noFuncDecl]
  | step_block_exit_none _ _ => simp [Config.noFuncDecl]
  | step_block_exit_match _ _ _ => simp [Config.noFuncDecl]
  | step_block_exit_mismatch _ _ _ => simp [Config.noFuncDecl]

private theorem step_preserves_δ
    [HasVal P] [HasFvar P] [HasBool P] [HasNot P] [DecidableEq P.Ident]
    [HasVarsImp P (List (Stmt P (Cmd P)))] [HasVarsImp P (Cmd P)]
    (extendEval : ExtendEval P)
    {c₁ c₂ : Config P (Cmd P)}
    (Hno : Config.noFuncDecl c₁ = true)
    (Hstep : StepStmt P (EvalCmd P) extendEval c₁ c₂) :
    Config.getδ c₂ = Config.getδ c₁ := by
  induction Hstep with
  | step_cmd => simp [Config.getδ]
  | step_block => simp [Config.getδ]
  | step_ite_true => simp [Config.getδ]
  | step_ite_false => simp [Config.getδ]
  | step_loop_enter => simp [Config.getδ]
  | step_loop_exit => simp [Config.getδ]
  | step_exit => simp [Config.getδ]
  | step_funcDecl => simp [Config.noFuncDecl, Stmt.noFuncDecl] at Hno
  | step_typeDecl => simp [Config.getδ]
  | step_stmts_nil => simp [Config.getδ]
  | step_stmt_cons _ ih =>
    simp [Config.getδ, Config.noFuncDecl, Block.noFuncDecl] at Hno ⊢
    exact ih (by simp [Config.noFuncDecl]; exact Hno.1)
  | step_stmt_cons_exit _ ih =>
    simp [Config.getδ, Config.noFuncDecl, Block.noFuncDecl] at Hno ⊢
    exact ih (by simp [Config.noFuncDecl]; exact Hno.1)
  | step_block_body _ ih =>
    simp [Config.getδ]; exact ih (by simp [Config.noFuncDecl]; exact Hno)
  | step_block_done _ ih =>
    simp [Config.getδ]; exact ih (by simp [Config.noFuncDecl]; exact Hno)
  | step_block_exit_none _ ih =>
    simp [Config.getδ]; exact ih (by simp [Config.noFuncDecl]; exact Hno)
  | step_block_exit_match _ _ ih =>
    simp [Config.getδ]; exact ih (by simp [Config.noFuncDecl]; exact Hno)
  | step_block_exit_mismatch _ _ ih =>
    simp [Config.getδ]; exact ih (by simp [Config.noFuncDecl]; exact Hno)

private theorem stepStar_preserves_δ
    [HasVal P] [HasFvar P] [HasBool P] [HasNot P] [DecidableEq P.Ident]
    [HasVarsImp P (List (Stmt P (Cmd P)))] [HasVarsImp P (Cmd P)]
    (extendEval : ExtendEval P)
    {c₁ c₂ : Config P (Cmd P)}
    (Hno : Config.noFuncDecl c₁ = true)
    (Hstar : StepStmtStar P (EvalCmd P) extendEval c₁ c₂) :
    Config.getδ c₂ = Config.getδ c₁ := by
  unfold StepStmtStar at Hstar
  induction Hstar with
  | refl => rfl
  | step _ _ _ Hstep _ ih =>
    rw [ih (step_preserves_noFuncDecl extendEval Hno Hstep),
        step_preserves_δ extendEval Hno Hstep]

theorem EvalStmtSmall_noFuncDecl_preserves_δ
    [HasVal P] [HasFvar P] [HasBool P] [HasNot P] [DecidableEq P.Ident]
    [HasVarsImp P (List (Stmt P (Cmd P)))] [HasVarsImp P (Cmd P)]
    (extendEval : ExtendEval P)
    {δ : SemanticEval P} {σ σ' : SemanticStore P} {δ' : SemanticEval P}
    {s : Stmt P (Cmd P)}
    (Hno : Stmt.noFuncDecl s = true)
    (Heval : EvalStmtSmall P (EvalCmd P) extendEval δ σ s σ' δ') :
    δ' = δ := by
  unfold EvalStmtSmall at Heval
  have h := stepStar_preserves_δ extendEval
    (show Config.noFuncDecl (.stmt s σ δ) = true by simp [Config.noFuncDecl]; exact Hno)
    Heval
  simp [Config.getδ] at h; exact h

theorem EvalStmtsSmall_noFuncDecl_preserves_δ
    [HasVal P] [HasFvar P] [HasBool P] [HasNot P] [DecidableEq P.Ident]
    [HasVarsImp P (List (Stmt P (Cmd P)))] [HasVarsImp P (Cmd P)]
    (extendEval : ExtendEval P)
    {δ : SemanticEval P} {σ σ' : SemanticStore P} {δ' : SemanticEval P}
    {ss : Block P (Cmd P)}
    (Hno : Block.noFuncDecl ss = true)
    (Heval : EvalStmtsSmall P (EvalCmd P) extendEval δ σ ss σ' δ') :
    δ' = δ := by
  unfold EvalStmtsSmall at Heval
  have h := stepStar_preserves_δ extendEval
    (show Config.noFuncDecl (.stmts ss σ δ) = true by simp [Config.noFuncDecl]; exact Hno)
    Heval
  simp [Config.getδ] at h; exact h

/-! ## Inversion lemmas -/

private theorem terminal_no_step
    [HasVal P] [HasFvar P] [HasBool P] [HasNot P] [DecidableEq P.Ident]
    [HasVarsImp P (List (Stmt P (Cmd P)))] [HasVarsImp P (Cmd P)]
    {extendEval : ExtendEval P}
    {σ : SemanticStore P} {δ : SemanticEval P}
    {c : Config P (Cmd P)} :
    StepStmt P (EvalCmd P) extendEval (.terminal σ δ) c → False := by
  intro h; cases h

private theorem terminal_reflTrans_eq
    [HasVal P] [HasFvar P] [HasBool P] [HasNot P] [DecidableEq P.Ident]
    [HasVarsImp P (List (Stmt P (Cmd P)))] [HasVarsImp P (Cmd P)]
    {extendEval : ExtendEval P}
    {σ σ' : SemanticStore P} {δ δ' : SemanticEval P}
    (H : ReflTrans (StepStmt P (EvalCmd P) extendEval)
      (.terminal σ δ) (.terminal σ' δ')) :
    σ' = σ ∧ δ' = δ := by
  cases H with
  | refl => exact ⟨rfl, rfl⟩
  | step _ _ _ Hstep _ => exact absurd Hstep terminal_no_step

private theorem invert_cmd_terminal
    [HasVal P] [HasFvar P] [HasBool P] [HasNot P] [DecidableEq P.Ident]
    [HasVarsImp P (List (Stmt P (Cmd P)))] [HasVarsImp P (Cmd P)]
    {extendEval : ExtendEval P}
    {c : Cmd P} {σ σ' : SemanticStore P} {δ δ' : SemanticEval P}
    (Heval : EvalStmtSmall P (EvalCmd P) extendEval δ σ (.cmd c) σ' δ') :
    EvalCmd P δ σ c σ' ∧ δ' = δ := by
  unfold EvalStmtSmall StepStmtStar at Heval
  cases Heval with
  | step _ mid _ Hstep Hrest =>
    cases Hstep with
    | step_cmd Hcmd =>
      have ⟨h1, h2⟩ := terminal_reflTrans_eq Hrest
      subst h1; subst h2; exact ⟨Hcmd, rfl⟩

private theorem invert_ite_terminal
    [HasVal P] [HasFvar P] [HasBool P] [HasNot P] [DecidableEq P.Ident]
    [HasVarsImp P (List (Stmt P (Cmd P)))] [HasVarsImp P (Cmd P)]
    {extendEval : ExtendEval P}
    {cond : P.Expr} {tss ess : Block P (Cmd P)} {md : MetaData P}
    {σ σ' : SemanticStore P} {δ δ' : SemanticEval P}
    (Heval : EvalStmtSmall P (EvalCmd P) extendEval δ σ (.ite cond tss ess md) σ' δ') :
    (δ σ cond = .some HasBool.tt ∧ WellFormedSemanticEvalBool δ ∧
      EvalStmtsSmall P (EvalCmd P) extendEval δ σ tss σ' δ') ∨
    (δ σ cond = .some HasBool.ff ∧ WellFormedSemanticEvalBool δ ∧
      EvalStmtsSmall P (EvalCmd P) extendEval δ σ ess σ' δ') := by
  unfold EvalStmtSmall StepStmtStar at Heval
  cases Heval with
  | step _ _ _ Hstep Hrest =>
    cases Hstep with
    | step_ite_true Htrue Hwfb => left; exact ⟨Htrue, Hwfb, Hrest⟩
    | step_ite_false Hfalse Hwfb => right; exact ⟨Hfalse, Hwfb, Hrest⟩

private theorem invert_typeDecl_terminal
    [HasVal P] [HasFvar P] [HasBool P] [HasNot P] [DecidableEq P.Ident]
    [HasVarsImp P (List (Stmt P (Cmd P)))] [HasVarsImp P (Cmd P)]
    {extendEval : ExtendEval P}
    {tc : TypeConstructor} {md : MetaData P}
    {σ σ' : SemanticStore P} {δ δ' : SemanticEval P}
    (Heval : EvalStmtSmall P (EvalCmd P) extendEval δ σ (.typeDecl tc md) σ' δ') :
    σ' = σ ∧ δ' = δ := by
  unfold EvalStmtSmall StepStmtStar at Heval
  cases Heval with
  | step _ _ _ Hstep Hrest =>
    cases Hstep with
    | step_typeDecl => exact terminal_reflTrans_eq Hrest

private theorem invert_stmts_nil_terminal
    [HasVal P] [HasFvar P] [HasBool P] [HasNot P] [DecidableEq P.Ident]
    [HasVarsImp P (List (Stmt P (Cmd P)))] [HasVarsImp P (Cmd P)]
    {extendEval : ExtendEval P}
    {σ σ' : SemanticStore P} {δ δ' : SemanticEval P}
    (Heval : EvalStmtsSmall P (EvalCmd P) extendEval δ σ [] σ' δ') :
    σ' = σ ∧ δ' = δ := by
  unfold EvalStmtsSmall StepStmtStar at Heval
  cases Heval with
  | step _ _ _ Hstep Hrest =>
    cases Hstep with
    | step_stmts_nil => exact terminal_reflTrans_eq Hrest

private theorem invert_cons_terminal
    [HasVal P] [HasFvar P] [HasBool P] [HasNot P] [DecidableEq P.Ident]
    [HasVarsImp P (List (Stmt P (Cmd P)))] [HasVarsImp P (Cmd P)]
    {extendEval : ExtendEval P}
    {s : Stmt P (Cmd P)} {ss : Block P (Cmd P)}
    {σ σ' : SemanticStore P} {δ δ' : SemanticEval P}
    (Heval : EvalStmtsSmall P (EvalCmd P) extendEval δ σ (s :: ss) σ' δ') :
    ∃ σ_mid δ_mid,
      EvalStmtSmall P (EvalCmd P) extendEval δ σ s σ_mid δ_mid ∧
      EvalStmtsSmall P (EvalCmd P) extendEval δ_mid σ_mid ss σ' δ' := by
  sorry

private theorem invert_block_terminal
    [HasVal P] [HasFvar P] [HasBool P] [HasNot P] [DecidableEq P.Ident]
    [HasVarsImp P (List (Stmt P (Cmd P)))] [HasVarsImp P (Cmd P)]
    {extendEval : ExtendEval P}
    {label : String} {ss : Block P (Cmd P)} {md : MetaData P}
    {σ σ' : SemanticStore P} {δ δ' : SemanticEval P}
    (Heval : EvalStmtSmall P (EvalCmd P) extendEval δ σ (.block label ss md) σ' δ') :
    EvalStmtsSmall P (EvalCmd P) extendEval δ σ ss σ' δ' := by
  sorry

/-! ## Main Correctness Theorem -/

theorem StmtToNondetCorrectSmallStep
    [HasVal P] [HasFvar P] [HasBool P] [HasBoolVal P] [HasNot P] [DecidableEq P.Ident]
    (extendEval : ExtendEval P) :
    WellFormedSemanticEvalBool δ →
    WellFormedSemanticEvalVal δ →
    (∀ st,
      Stmt.sizeOf st ≤ m →
      Stmt.noFuncDecl st →
      EvalStmtSmall P (EvalCmd P) extendEval δ σ st σ' δ →
      EvalNondetStmt P (Cmd P) (EvalCmd P) δ σ (StmtToNondetStmt st) σ') ∧
    (∀ ss,
      Block.sizeOf ss ≤ m →
      Block.noFuncDecl ss →
      EvalStmtsSmall P (EvalCmd P) extendEval δ σ ss σ' δ →
      EvalNondetStmt P (Cmd P) (EvalCmd P) δ σ (BlockToNondetStmt ss) σ') := by
  intros Hwfb Hwfvl
  apply Nat.strongRecOn (motive := fun m =>
    ∀ σ σ',
    (∀ st,
      Stmt.sizeOf st ≤ m →
      Stmt.noFuncDecl st →
      EvalStmtSmall P (EvalCmd P) extendEval δ σ st σ' δ →
      EvalNondetStmt P (Cmd P) (EvalCmd P) δ σ (StmtToNondetStmt st) σ') ∧
    (∀ ss,
      Block.sizeOf ss ≤ m →
      Block.noFuncDecl ss →
      EvalStmtsSmall P (EvalCmd P) extendEval δ σ ss σ' δ →
      EvalNondetStmt P (Cmd P) (EvalCmd P) δ σ (BlockToNondetStmt ss) σ'))
  intros n ih σ₀ σ₀'
  refine ⟨?_, ?_⟩
  -- ── Statement case ──
  · intros st Hsz Hno Heval
    match st with
    | .cmd c =>
      have ⟨Hcmd, _⟩ := invert_cmd_terminal Heval
      apply EvalNondetStmt.cmd_sem Hcmd
      sorry -- isDefinedOver not available from small-step
    | .ite cond tss ess md =>
      simp [Stmt.noFuncDecl] at Hno
      cases invert_ite_terminal Heval with
      | inl Htrue =>
        obtain ⟨Hguard, _, Hbranch⟩ := Htrue
        have Hδ := EvalStmtsSmall_noFuncDecl_preserves_δ extendEval Hno.1 Hbranch
        refine EvalNondetStmt.choice_left_sem Hwfb ?_
        apply EvalNondetStmt.seq_sem
        · apply EvalNondetStmt.cmd_sem
          exact EvalCmd.eval_assume Hguard Hwfb
          simp [isDefinedOver, HasVarsImp.modifiedVars, Cmd.modifiedVars, isDefined]
        · exact (ih (Block.sizeOf tss) (by simp [Stmt.sizeOf] at Hsz; omega) σ₀ σ₀').2
            tss (by omega) Hno.1 (Hδ ▸ Hbranch)
      | inr Hfalse =>
        obtain ⟨Hguard, _, Hbranch⟩ := Hfalse
        have Hδ := EvalStmtsSmall_noFuncDecl_preserves_δ extendEval Hno.2 Hbranch
        refine EvalNondetStmt.choice_right_sem Hwfb ?_
        apply EvalNondetStmt.seq_sem
        · apply EvalNondetStmt.cmd_sem
          refine EvalCmd.eval_assume ?_ Hwfb
          exact (Hwfb σ₀ cond).2.mp Hguard
          simp [isDefinedOver, HasVarsImp.modifiedVars, Cmd.modifiedVars, isDefined]
        · exact (ih (Block.sizeOf ess) (by simp [Stmt.sizeOf] at Hsz; omega) σ₀ σ₀').2
            ess (by omega) Hno.2 (Hδ ▸ Hbranch)
    | .block label bss md =>
      simp [Stmt.noFuncDecl] at Hno
      have Hbody := invert_block_terminal Heval
      have Hδ := EvalStmtsSmall_noFuncDecl_preserves_δ extendEval Hno Hbody
      simp [StmtToNondetStmt]
      exact (ih (Block.sizeOf bss) (by simp [Stmt.sizeOf] at Hsz; omega) σ₀ σ₀').2
        bss (by omega) Hno (Hδ ▸ Hbody)
    | .loop _ _ _ _ _ => sorry
    | .exit _ _ => sorry
    | .funcDecl _ _ => simp [Stmt.noFuncDecl] at Hno
    | .typeDecl tc md =>
      have ⟨Hσ, _⟩ := invert_typeDecl_terminal Heval
      subst Hσ
      simp [StmtToNondetStmt]
      apply EvalNondetStmt.cmd_sem
      · apply EvalCmd.eval_assume
        · exact Hwfvl.2 HasBool.tt σ₀' HasBoolVal.bool_is_val.1
        · exact Hwfb
      · simp [isDefinedOver, HasVarsImp.modifiedVars, Cmd.modifiedVars, isDefined]
  -- ── Block case ──
  · intros ss Hsz Hno Heval
    cases ss with
    | nil =>
      have ⟨Hσ, _⟩ := invert_stmts_nil_terminal Heval
      subst Hσ
      simp [BlockToNondetStmt]
      apply EvalNondetStmt.cmd_sem
      · apply EvalCmd.eval_assume
        · exact Hwfvl.2 HasBool.tt σ₀' HasBoolVal.bool_is_val.1
        · exact Hwfb
      · simp [isDefinedOver, HasVarsImp.modifiedVars, Cmd.modifiedVars, isDefined]
    | cons h t =>
      simp [BlockToNondetStmt, Block.sizeOf] at Hsz ⊢
      simp [Block.noFuncDecl] at Hno
      obtain ⟨σ_mid, δ_mid, Hh, Ht⟩ := invert_cons_terminal Heval
      have Hδ₁ : δ_mid = δ := EvalStmtSmall_noFuncDecl_preserves_δ extendEval Hno.1 Hh
      subst Hδ₁
      have ih_both := ih (h.sizeOf + Block.sizeOf t) (by omega)
      exact EvalNondetStmt.seq_sem
        ((ih_both σ₀ σ_mid).1 h (by omega) Hno.1 Hh)
        ((ih_both σ_mid σ₀').2 t (by omega) Hno.2 Ht)

/-! ## Public API -/

theorem StmtToNondetStmtCorrectSmallStep
    [HasVal P] [HasFvar P] [HasBool P] [HasBoolVal P] [HasNot P] [DecidableEq P.Ident]
    (extendEval : ExtendEval P) :
    WellFormedSemanticEvalBool δ →
    WellFormedSemanticEvalVal δ →
    Stmt.noFuncDecl st →
    EvalStmtSmall P (EvalCmd P) extendEval δ σ st σ' δ →
    EvalNondetStmt P (Cmd P) (EvalCmd P) δ σ (StmtToNondetStmt st) σ' := by
  intros Hwfb Hwfv Hno Heval
  exact (StmtToNondetCorrectSmallStep extendEval Hwfb Hwfv (m := st.sizeOf)).1
    st (Nat.le_refl _) Hno Heval

theorem BlockToNondetStmtCorrectSmallStep
    [HasVal P] [HasFvar P] [HasBool P] [HasBoolVal P] [HasNot P] [DecidableEq P.Ident]
    (extendEval : ExtendEval P) :
    WellFormedSemanticEvalBool δ →
    WellFormedSemanticEvalVal δ →
    Block.noFuncDecl ss →
    EvalStmtsSmall P (EvalCmd P) extendEval δ σ ss σ' δ →
    EvalNondetStmt P (Cmd P) (EvalCmd P) δ σ (BlockToNondetStmt ss) σ' := by
  intros Hwfb Hwfv Hno Heval
  exact (StmtToNondetCorrectSmallStep extendEval Hwfb Hwfv (m := Block.sizeOf ss)).2
    ss (Nat.le_refl _) Hno Heval

end -- public section
