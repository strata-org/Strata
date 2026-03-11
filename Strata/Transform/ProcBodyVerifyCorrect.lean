/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Transform.ProcBodyVerify
import Strata.Transform.SoundnessFramework

/-! # Procedure Body Verification Correctness Proof -/

namespace ProcBodyVerifyCorrect

open Core Core.ProcBodyVerify Imperative Lambda Transform Strata.Soundness

/-! ## Structural Characterization -/


theorem procToVerifyStmt_structure
    (proc : Procedure) (p : Program) (st : CoreTransformState)
    (stmt : Statement) (st' : CoreTransformState)
    (h : (procToVerifyStmt proc p).run st = (Except.ok stmt, st')) :
    ∃ (label : String) (pre_body : List Statement) (bodyLabel : String) (md : MetaData Expression),
      stmt = Stmt.block label
        (pre_body ++ [Stmt.block bodyLabel proc.body #[]] ++ ensuresToAsserts proc.spec.postconditions) md := by
  unfold procToVerifyStmt at h
  simp only [bind, ExceptT.bind, ExceptT.mk, pure, ExceptT.pure, ExceptT.run, StateT.bind] at h
  simp only [ExceptT.bindCont] at h
  split at h
  · rename_i a s h_mapM
    split at h
    · rename_i modifiesInits
      simp only [StateT.pure, pure, Prod.mk.injEq] at h
      obtain ⟨rfl, _⟩ := h
      exact ⟨_, _, _, _, rfl⟩
    · rename_i e; exact absurd h nofun
/-! ## Helper Lemmas -/

theorem block_lift_steps
    (π : String → Option Procedure) (φ : CoreEval → PureFunc Expression → CoreEval)
    (label : String) (c₁ c₂ : CoreConfig) :
    CoreStepStar π φ c₁ c₂ →
    CoreStepStar π φ (.block label c₁) (.block label c₂) := by
  intro h; induction h with
  | refl => exact ReflTrans.refl _
  | step _ y _ h_step _ ih => exact ReflTrans.step _ _ _ (StepStmt.step_block_body h_step) ih

theorem seq_lift_steps
    (π : String → Option Procedure) (φ : CoreEval → PureFunc Expression → CoreEval)
    (ss : List Statement) (c₁ c₂ : CoreConfig) :
    CoreStepStar π φ c₁ c₂ →
    CoreStepStar π φ (.seq c₁ ss) (.seq c₂ ss) := by
  intro h; induction h with
  | refl => exact ReflTrans.refl _
  | step _ y _ h_step _ ih => exact ReflTrans.step _ _ _ (StepStmt.step_seq_inner h_step) ih

theorem seq_process_stmt
    (π : String → Option Procedure) (φ : CoreEval → PureFunc Expression → CoreEval)
    (s : Statement) (ss : List Statement) (σ σ' : CoreStore) (δ δ' : CoreEval) :
    CoreStepStar π φ (.stmt s σ δ) (.terminal σ' δ') →
    CoreStepStar π φ (.stmts (s :: ss) σ δ) (.stmts ss σ' δ') := by
  intro h
  apply ReflTrans.step _ (.seq (.stmt s σ δ) ss)
  · exact StepStmt.step_stmts_cons
  exact ReflTrans_Transitive _ _ _ _
    (seq_lift_steps π φ ss _ _ h)
    (ReflTrans.step _ _ _ StepStmt.step_seq_done (ReflTrans.refl _))

theorem block_stmt_to_terminal
    (π : String → Option Procedure) (φ : CoreEval → PureFunc Expression → CoreEval)
    (label : String) (body : List Statement) (md : MetaData Expression)
    (σ σ' : CoreStore) (δ δ' : CoreEval) :
    CoreStepStar π φ (.stmts body σ δ) (.terminal σ' δ') →
    CoreStepStar π φ (.stmt (Stmt.block label body md) σ δ) (.terminal σ' δ') := by
  intro h_body
  apply ReflTrans.step _ (.block label (.stmts body σ δ))
  · exact StepStmt.step_block
  exact ReflTrans_Transitive _ _ _ _
    (block_lift_steps π φ label _ _ h_body)
    (ReflTrans.step _ _ _ StepStmt.step_block_done (ReflTrans.refl _))

private theorem stmts_nil_step_terminal
    (π : String → Option Procedure) (φ : CoreEval → PureFunc Expression → CoreEval)
    (σ : CoreStore) (δ : CoreEval) (c : CoreConfig) :
    CoreStep π φ (.stmts [] σ δ) c → c = .terminal σ δ := by
  intro h; cases h; rfl

private theorem stmts_cons_step_seq
    (π : String → Option Procedure) (φ : CoreEval → PureFunc Expression → CoreEval)
    (s : Statement) (ss : List Statement) (σ : CoreStore) (δ : CoreEval) (c : CoreConfig) :
    CoreStep π φ (.stmts (s :: ss) σ δ) c → c = .seq (.stmt s σ δ) ss := by
  intro h; cases h; rfl

private theorem seq_reaches_stmts
    (π : String → Option Procedure) (φ : CoreEval → PureFunc Expression → CoreEval)
    (inner : CoreConfig) (ss : List Statement) (c : CoreConfig) :
    CoreStepStar π φ (.seq inner ss) c →
    (∃ c', c = .seq c' ss) ∨
    (∃ σ_mid δ_mid,
      CoreStepStar π φ inner (.terminal σ_mid δ_mid) ∧
      CoreStepStar π φ (.stmts ss σ_mid δ_mid) c) ∨
    (∃ label σ_mid δ_mid,
      CoreStepStar π φ inner (.exiting label σ_mid δ_mid) ∧
      c = .exiting label σ_mid δ_mid) := by
  intro h
  generalize h_c1 : Config.seq inner ss = c₁ at h
  induction h generalizing inner with
  | refl => left; exact ⟨inner, h_c1 ▸ rfl⟩
  | step _ y _ h_step h_rest ih =>
    subst h_c1
    cases h_step with
    | step_seq_inner h_inner =>
      rename_i inner'
      rcases ih inner' rfl with ⟨c', rfl⟩ | ⟨σ_mid, δ_mid, h_t, h_r⟩ | ⟨l, σ_mid, δ_mid, h_e, h_eq⟩
      · left; exact ⟨c', rfl⟩
      · right; left; exact ⟨σ_mid, δ_mid, ReflTrans.step _ _ _ h_inner h_t, h_r⟩
      · right; right; exact ⟨l, σ_mid, δ_mid, ReflTrans.step _ _ _ h_inner h_e, h_eq⟩
    | step_seq_done =>
      right; left; exact ⟨_, _, ReflTrans.refl _, h_rest⟩
    | step_seq_exit =>
      right; right
      cases h_rest with
      | refl => exact ⟨_, _, _, ReflTrans.refl _, rfl⟩
      | step _ _ _ h_next => exact absurd h_next nofun

theorem stmts_cons_decompose
    (π : String → Option Procedure) (φ : CoreEval → PureFunc Expression → CoreEval)
    (s : Statement) (rest : List Statement) (σ σ' : CoreStore) (δ δ' : CoreEval) :
    CoreStepStar π φ (.stmts (s :: rest) σ δ) (.terminal σ' δ') →
    ∃ (σ_mid : CoreStore) (δ_mid : CoreEval),
      CoreStepStar π φ (.stmt s σ δ) (.terminal σ_mid δ_mid) ∧
      CoreStepStar π φ (.stmts rest σ_mid δ_mid) (.terminal σ' δ') := by
  intro h
  cases h with
  | step _ y _ h_step h_rest =>
    cases h_step with
    | step_stmts_cons =>
      rcases seq_reaches_stmts π φ (.stmt s σ δ) rest (.terminal σ' δ') h_rest with
        ⟨_, h_eq⟩ | ⟨σ_mid, δ_mid, h_s, h_r⟩ | ⟨_, _, _, _, h_eq⟩
      · exact absurd h_eq nofun
      · exact ⟨σ_mid, δ_mid, h_s, h_r⟩
      · exact absurd h_eq nofun

theorem stmts_process_to_suffix
    (π : String → Option Procedure) (φ : CoreEval → PureFunc Expression → CoreEval)
    (prefix_ suffix_ : List Statement) (σ σ' : CoreStore) (δ δ' : CoreEval) :
    CoreStepStar π φ (.stmts prefix_ σ δ) (.terminal σ' δ') →
    CoreStepStar π φ (.stmts (prefix_ ++ suffix_) σ δ) (.stmts suffix_ σ' δ') := by
  intro h
  induction prefix_ generalizing σ δ with
  | nil =>
    cases h with
    | step _ _ _ h_step h_rest =>
      have := stmts_nil_step_terminal π φ σ δ _ h_step
      subst this
      cases h_rest with
      | refl => exact ReflTrans.refl _
      | step _ _ _ h_next => exact absurd h_next nofun
  | cons s rest ih =>
    obtain ⟨σ_mid, δ_mid, h_s, h_rest⟩ := stmts_cons_decompose π φ s rest σ σ' δ δ' h
    simp only [List.cons_append]
    exact ReflTrans_Transitive _ _ _ _
      (seq_process_stmt π φ s (rest ++ suffix_) σ σ_mid δ δ_mid h_s)
      (ih σ_mid δ_mid h_rest)

/-- Assert skips execute to terminal without changing state. -/
theorem assert_skips_to_terminal
    (π : String → Option Procedure) (φ : CoreEval → PureFunc Expression → CoreEval)
    (stmts : List Statement) (σ : CoreStore) (δ : CoreEval) :
    (∀ s, s ∈ stmts → ∃ l e m, s = Statement.assert l e m) →
    CoreStepStar π φ (.stmts stmts σ δ) (.terminal σ δ) := by
  intro h_all
  induction stmts with
  | nil => exact ReflTrans.step _ _ _ StepStmt.step_stmts_nil (ReflTrans.refl _)
  | cons s rest ih =>
    obtain ⟨l, e, m, rfl⟩ := h_all s (List.mem_cons.mpr (Or.inl rfl))
    exact ReflTrans_Transitive _ _ _ _
      (seq_process_stmt π φ _ _ σ σ δ δ
        (ReflTrans.step _ _ _ (StepStmt.step_cmd (EvalCommand.cmd_sem EvalCmd.eval_assert)) (ReflTrans.refl _)))
      (ih (fun s h => h_all s (List.mem_cons.mpr (Or.inr h))))

/-! ## Soundness Theorem -/

/-- Soundness of ProcBodyVerify: if the verification block is correct,
    then the procedure obeys its contract. -/
theorem procBodyVerify_sound
    -- Given a procedure environment and function extension mechanism
    (π : String → Option Procedure) (φ : CoreEval → PureFunc Expression → CoreEval)
    -- Given a procedure and a program context
    (proc : Procedure) (p : Program) (st : CoreTransformState)
    -- If procToVerifyStmt produces a verification statement `stmt`
    (stmt : Statement) (st' : CoreTransformState)
    (h_transform : (procToVerifyStmt proc p).run st = (Except.ok stmt, st'))
    -- And every assertion in `stmt` is valid (holds at all reachable states)
    (h_correct : stmt_correct π φ stmt) :
    -- Then the procedure obeys its contract:
    -- for all initial states where preconditions hold,
    -- if the body executes to completion,
    -- then all postconditions hold at exit.
    procedure_obeys_contract π φ proc := by
  obtain ⟨blk_label, pre_body, bodyLabel, blk_md, h_stmt_eq⟩ :=
    procToVerifyStmt_structure proc p st stmt st' h_transform
  intro δ σ₀ σ_final δ_final h_pre h_body label check h_post_in h_default
  have h_assert_in : Statement.assert label check.expr check.md ∈
      ensuresToAsserts proc.spec.postconditions := by
    unfold ensuresToAsserts; simp only [List.mem_filterMap]
    exact ⟨(label, check), h_post_in, by simp [h_default]⟩
  rw [h_stmt_eq] at h_correct
  obtain ⟨before_a, after_a, h_split⟩ := List.append_of_mem h_assert_in
  -- The postcondition assert is reachable in the verification block
  -- with store σ_final and evaluator δ_final.
  -- This requires showing the prefix (inits + assumes + body) can execute.
  -- We construct the path: block → prefix → body → assert skips → target assert
  apply h_correct ⟨label, check.expr, check.md⟩
    ⟨σ_final, δ_final, some ⟨label, check.expr, check.md⟩⟩
  · -- reachable: the postcondition assert is reachable in the verification block
    -- This requires:
    -- 1. The prefix (inits + assumes) executes from some σ₀' to σ₀
    --    (inits create variables with arbitrary values, assumes check preconditions)
    -- 2. The body block executes from σ₀ to σ_final (by h_body)
    -- 3. The assert skips before the target assert execute (no-op)
    -- Step 1 requires constructing InitState derivations and showing
    -- assume conditions hold. This is the remaining proof obligation.
    sorry
  · rfl

end ProcBodyVerifyCorrect
