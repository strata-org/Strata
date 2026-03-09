/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Transform.ProcBodyVerify
import StrataTest.Transform.SoundnessFramework

/-! # Procedure Body Verification Correctness Proof -/

namespace ProcBodyVerifyCorrect

open Core Core.ProcBodyVerify Imperative Lambda Transform Soundness

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

/-- Process one statement in a stmts list via seq. -/
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

/-- A block statement reaches terminal via its body. -/
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

/-- Process a prefix of statements, each reaching terminal, advancing to the suffix. -/
theorem stmts_process_to_suffix
    (π : String → Option Procedure) (φ : CoreEval → PureFunc Expression → CoreEval)
    (prefix_ suffix_ : List Statement) (σ σ' : CoreStore) (δ δ' : CoreEval) :
    CoreStepStar π φ (.stmts prefix_ σ δ) (.terminal σ' δ') →
    CoreStepStar π φ (.stmts (prefix_ ++ suffix_) σ δ) (.stmts suffix_ σ' δ') := by
  intro h
  -- By induction on the step sequence, but we need to know prefix_ structure.
  -- Alternative: use the fact that .stmts prefix_ →* .terminal means
  -- each statement in prefix_ processes to terminal sequentially.
  sorry

/-! ## Soundness Theorem -/

theorem procBodyVerify_sound
    (π : String → Option Procedure) (φ : CoreEval → PureFunc Expression → CoreEval)
    (proc : Procedure) (p : Program) (st : CoreTransformState)
    (stmt : Statement) (st' : CoreTransformState)
    (h_transform : (procToVerifyStmt proc p).run st = (Except.ok stmt, st'))
    (h_correct : stmt_correct π φ stmt)
    -- The prefix (inits + assumes) can execute to produce any state where pre holds
    (h_prefix_exec : ∀ (δ : CoreEval) (σ₀ : CoreStore),
      (∀ (label : CoreLabel) (check : Procedure.Check),
        (label, check) ∈ proc.spec.preconditions.toList →
        δ σ₀ check.expr = some HasBool.tt) →
      ∃ (δ₀ : CoreEval) (σ₀' : CoreStore),
        ∀ (pre_body : List Statement) (bodyLabel : String),
          (∃ blk_label md, stmt = Stmt.block blk_label
            (pre_body ++ [Stmt.block bodyLabel proc.body #[]] ++ ensuresToAsserts proc.spec.postconditions) md) →
          CoreStepStar π φ (.stmts pre_body σ₀' δ₀) (.terminal σ₀ δ)) :
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
  -- Get prefix execution
  obtain ⟨δ₀, σ₀', h_pre_exec⟩ := h_prefix_exec δ σ₀ h_pre
  have h_prefix := h_pre_exec pre_body bodyLabel ⟨blk_label, blk_md, h_stmt_eq⟩
  -- Build the full path
  -- .stmt (block ...) σ₀' δ₀ → .block blk_label (.stmts allStmts σ₀' δ₀)
  -- →* .block blk_label (.stmts (assert :: after_a) σ_final δ_final)
  -- ProgramState.ofConfig detects the assert
  apply h_correct ⟨label, check.expr, check.md⟩
    ⟨σ_final, δ_final, some ⟨label, check.expr, check.md⟩⟩
  · -- reachable
    unfold reachable
    refine ⟨δ₀, σ₀', .block blk_label (.stmts (Statement.assert label check.expr check.md :: after_a) σ_final δ_final), ?_, rfl⟩
    -- Path: .stmt block → .block (.stmts allStmts) →* .block (.stmts (assert :: after_a))
    apply ReflTrans.step _ (.block blk_label (.stmts _ σ₀' δ₀))
    · exact StepStmt.step_block
    apply block_lift_steps
    -- Need: .stmts allStmts σ₀' δ₀ →* .stmts (assert :: after_a) σ_final δ_final
    -- allStmts = pre_body ++ [body_block] ++ asserts
    -- = pre_body ++ [body_block] ++ before_a ++ [assert] ++ after_a
    rw [h_split, show pre_body ++ [Stmt.block bodyLabel proc.body #[]] ++
      (before_a ++ Statement.assert label check.expr check.md :: after_a) =
      pre_body ++ ([Stmt.block bodyLabel proc.body #[]] ++
      before_a ++ [Statement.assert label check.expr check.md] ++ after_a)
      from by simp [List.append_assoc]]
    -- Process pre_body: →* .stmts rest σ₀ δ
    apply ReflTrans_Transitive
    · exact stmts_process_to_suffix π φ pre_body _ σ₀' σ₀ δ₀ δ h_prefix
    -- Process body_block via seq: →* .stmts (before_a ++ [assert] ++ after_a) σ_final δ_final
    apply ReflTrans_Transitive
    · exact seq_process_stmt π φ _ _ σ₀ σ_final δ δ_final
        (block_stmt_to_terminal π φ bodyLabel proc.body #[] σ₀ σ_final δ δ_final h_body)
    -- Process before_a (assert skips): →* .stmts ([assert] ++ after_a) σ_final δ_final
    sorry
  · rfl

end ProcBodyVerifyCorrect
