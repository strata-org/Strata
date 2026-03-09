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

/-- .stmts [] can only step to .terminal -/
private theorem stmts_nil_step_terminal
    (π : String → Option Procedure) (φ : CoreEval → PureFunc Expression → CoreEval)
    (σ : CoreStore) (δ : CoreEval) (c : CoreConfig) :
    CoreStep π φ (.stmts [] σ δ) c → c = .terminal σ δ := by
  intro h; cases h; rfl

/-- .stmts (s :: ss) can only step to .seq (.stmt s σ δ) ss -/
private theorem stmts_cons_step_seq
    (π : String → Option Procedure) (φ : CoreEval → PureFunc Expression → CoreEval)
    (s : Statement) (ss : List Statement) (σ : CoreStore) (δ : CoreEval) (c : CoreConfig) :
    CoreStep π φ (.stmts (s :: ss) σ δ) c → c = .seq (.stmt s σ δ) ss := by
  intro h; cases h; rfl

/-- If .seq inner ss reaches a non-seq config, then inner must have reached
    .terminal or .exiting. -/
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
  -- Generalize to avoid ReflTrans index issues
  generalize h_c1 : Config.seq inner ss = c₁ at h
  induction h generalizing inner with
  | refl => left; exact ⟨inner, h_c1 ▸ rfl⟩
  | step _ y _ h_step h_rest ih =>
    subst h_c1
    cases h_step with
    | step_seq_inner h_inner =>
      -- y = .seq inner' ss where inner stepped to inner'
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
      have h_seq := seq_reaches_stmts π φ (.stmt s σ δ) rest (.terminal σ' δ') h_rest
      rcases h_seq with ⟨_, h_eq⟩ | ⟨σ_mid, δ_mid, h_s, h_r⟩ | ⟨_, _, _, _, h_eq⟩
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
      | step _ _ _ h_next => exact absurd h_next (fun h => by cases h)
  | cons s rest ih =>
    -- prefix_ = s :: rest
    obtain ⟨σ_mid, δ_mid, h_s, h_rest⟩ := stmts_cons_decompose π φ s rest σ σ' δ δ' h
    -- .stmts ((s :: rest) ++ suffix_) σ δ
    -- = .stmts (s :: (rest ++ suffix_)) σ δ
    -- →* .stmts (rest ++ suffix_) σ_mid δ_mid  (by seq_process_stmt using h_s)
    -- →* .stmts suffix_ σ' δ'                  (by IH using h_rest)
    simp only [List.cons_append]
    exact ReflTrans_Transitive _ _ _ _
      (seq_process_stmt π φ s (rest ++ suffix_) σ σ_mid δ δ_mid h_s)
      (ih σ_mid δ_mid h_rest)

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
      (before_a ++ (Statement.assert label check.expr check.md :: after_a)))
      from by simp [List.append_assoc]]
    -- Process pre_body: →* .stmts rest σ₀ δ
    apply ReflTrans_Transitive
    · exact stmts_process_to_suffix π φ pre_body _ σ₀' σ₀ δ₀ δ h_prefix
    -- Process body_block via seq: →* .stmts (before_a ++ [assert] ++ after_a) σ_final δ_final
    apply ReflTrans_Transitive
    · exact seq_process_stmt π φ _ _ σ₀ σ_final δ δ_final
        (block_stmt_to_terminal π φ bodyLabel proc.body #[] σ₀ σ_final δ δ_final h_body)
    -- Process before_a (assert skips)
    -- The goal should be: .stmts (before_a ++ assert :: after_a) σ_final δ_final
    --   →* .stmts (assert :: after_a) σ_final δ_final
    -- This is stmts_process_to_suffix with prefix_ = before_a, suffix_ = assert :: after_a
    -- We need: .stmts before_a σ_final δ_final →* .terminal σ_final δ_final
    have h_before_asserts : ∀ s, s ∈ before_a → ∃ l e m, s = Statement.assert l e m := by
      intro s h_s
      have : s ∈ ensuresToAsserts proc.spec.postconditions := by
        rw [h_split]; exact List.mem_append.mpr (Or.inl h_s)
      unfold ensuresToAsserts at this
      simp only [List.mem_filterMap] at this
      obtain ⟨⟨l, c⟩, _, h_eq⟩ := this
      cases h_attr : c.attr <;> simp [h_attr] at h_eq
      subst h_eq; exact ⟨l, c.expr, c.md, rfl⟩
    have h_before_exec : CoreStepStar π φ (.stmts before_a σ_final δ_final) (.terminal σ_final δ_final) := by
      suffices ∀ (stmts : List Statement),
          (∀ s, s ∈ stmts → ∃ l e m, s = Statement.assert l e m) →
          CoreStepStar π φ (.stmts stmts σ_final δ_final) (.terminal σ_final δ_final) by
        exact this before_a h_before_asserts
      intro stmts h_all
      induction stmts with
      | nil => exact ReflTrans.step _ _ _ StepStmt.step_stmts_nil (ReflTrans.refl _)
      | cons s rest ih =>
        obtain ⟨l, e, m, rfl⟩ := h_all s (List.mem_cons.mpr (Or.inl rfl))
        exact ReflTrans_Transitive _ _ _ _
          (seq_process_stmt π φ _ _ σ_final σ_final δ_final δ_final
            (ReflTrans.step _ _ _ (StepStmt.step_cmd (EvalCommand.cmd_sem EvalCmd.eval_assert)) (ReflTrans.refl _)))
          (ih (fun s h => h_all s (List.mem_cons.mpr (Or.inr h))))
    exact stmts_process_to_suffix π φ before_a
      (Statement.assert label check.expr check.md :: after_a)
      σ_final σ_final δ_final δ_final h_before_exec
  · rfl

end ProcBodyVerifyCorrect
