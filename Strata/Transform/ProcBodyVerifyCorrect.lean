/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Transform.ProcBodyVerify
import Strata.Transform.SoundnessFramework
import Strata.Languages.Core.WF

/-! # Procedure Body Verification Correctness Proof -/

namespace ProcBodyVerifyCorrect

open Core Core.ProcBodyVerify Imperative Lambda Transform Strata.Soundness Core.WF

/-! ## Structural Characterization -/


theorem procToVerifyStmt_structure
    (proc : Procedure) (p : Program) (st : CoreTransformState)
    (stmt : Statement) (st' : CoreTransformState)
    (h : (procToVerifyStmt proc p).run st = (Except.ok stmt, st')) :
    ∃ (label : String) (pre_body : List Statement) (md : MetaData Expression),
      stmt = Stmt.block label
        (pre_body ++ [Stmt.block s!"body_{proc.header.name.name}" proc.body #[]] ++
          ensuresToAsserts proc.spec.postconditions) md := by
  unfold procToVerifyStmt at h
  simp only [bind, ExceptT.bind, ExceptT.mk, pure, ExceptT.pure, ExceptT.run, StateT.bind] at h
  simp only [ExceptT.bindCont] at h
  split at h
  · rename_i a s h_mapM
    split at h
    · rename_i modifiesInits
      simp only [StateT.pure, pure] at h
      obtain ⟨rfl, _⟩ := h
      exact ⟨_, _, _, rfl⟩
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

/-- A single unconstrained init can step from a store without x to a store with x. -/
theorem init_unconstrained_step
    (π : String → Option Procedure) (φ : CoreEval → PureFunc Expression → CoreEval)
    (x : CoreIdent) (ty : LMonoTy) (σ_prev σ : CoreStore) (δ : CoreEval) (v : Expression.Expr)
    (h_none : σ_prev x = none)
    (h_some : σ x = some v)
    (h_rest : ∀ y, x ≠ y → σ y = σ_prev y)
    (h_wfv : WellFormedSemanticEvalVar δ) :
    CoreStepStar π φ
      (.stmt (Statement.init x (Lambda.LTy.forAll [] ty) none #[]) σ_prev δ)
      (.terminal σ δ) :=
  ReflTrans.step _ _ _
    (StepStmt.step_cmd (EvalCommand.cmd_sem
      (EvalCmd.eval_init_unconstrained (InitState.init h_none h_some h_rest) h_wfv)))
    (ReflTrans.refl _)

/-- A constrained init (init x ty (some e)) steps when e evaluates to a value. -/
theorem init_constrained_step
    (π : String → Option Procedure) (φ : CoreEval → PureFunc Expression → CoreEval)
    (x : CoreIdent) (ty : LMonoTy) (e : Expression.Expr)
    (σ_prev σ : CoreStore) (δ : CoreEval) (v : Expression.Expr)
    (h_eval : δ σ_prev e = some v)
    (h_none : σ_prev x = none)
    (h_some : σ x = some v)
    (h_rest : ∀ y, x ≠ y → σ y = σ_prev y)
    (h_wfv : WellFormedSemanticEvalVar δ) :
    CoreStepStar π φ
      (.stmt (Statement.init x (Lambda.LTy.forAll [] ty) (some e) #[]) σ_prev δ)
      (.terminal σ δ) :=
  ReflTrans.step _ _ _
    (StepStmt.step_cmd (EvalCommand.cmd_sem
      (EvalCmd.eval_init h_eval (InitState.init h_none h_some h_rest) h_wfv)))
    (ReflTrans.refl _)

/-- A list of unconstrained inits can reach any target store from a store
    where all the initialized variables are undefined. -/
theorem unconstrained_inits_reach
    (π : String → Option Procedure) (φ : CoreEval → PureFunc Expression → CoreEval)
    (vars : List (CoreIdent × LMonoTy)) (σ_target : CoreStore) (δ : CoreEval)
    (h_wfv : WellFormedSemanticEvalVar δ)
    -- All variables being initialized are defined in the target store
    (h_defined : ∀ p, p ∈ vars → ∃ v, σ_target p.1 = some v)
    -- All variables being initialized are distinct
    (h_nodup : (vars.map Prod.fst).Nodup) :
    ∃ (σ_init : CoreStore),
      -- The initial store agrees with target on non-initialized variables
      (∀ x, x ∉ vars.map Prod.fst → σ_init x = σ_target x) ∧
      -- The initial store has none for initialized variables
      (∀ x, x ∈ vars.map Prod.fst → σ_init x = none) ∧
      CoreStepStar π φ
        (.stmts (vars.map fun (id, ty) => Statement.init id (Lambda.LTy.forAll [] ty) none #[])
          σ_init δ)
        (.terminal σ_target δ) := by
  induction vars with
  | nil =>
    exact ⟨σ_target, fun _ _ => rfl, fun _ h => by simp at h,
      ReflTrans.step _ _ _ StepStmt.step_stmts_nil (ReflTrans.refl _)⟩
  | cons p rest ih =>
    obtain ⟨x, ty⟩ := p
    simp only [List.map_cons, List.nodup_cons] at h_nodup
    obtain ⟨h_x_notin, h_rest_nodup⟩ := h_nodup
    have h_rest_defined : ∀ p, p ∈ rest → ∃ v, σ_target p.1 = some v :=
      fun p hp => h_defined p (List.mem_cons_of_mem _ hp)
    obtain ⟨σ_mid, h_mid_agree, h_mid_none, h_rest_exec⟩ := ih h_rest_defined h_rest_nodup
    -- σ_mid has: rest vars = none, other vars = σ_target
    -- We need σ_init that also has x = none
    obtain ⟨v, h_v⟩ := h_defined ⟨x, ty⟩ List.mem_cons_self
    -- σ_init is σ_mid with x set to none
    let σ_init : CoreStore := fun y => if y = x then none else σ_mid y
    refine ⟨σ_init, ?_, ?_, ?_⟩
    · -- σ_init agrees with σ_target on non-initialized variables
      intro y hy
      simp only [List.map_cons, List.mem_cons, not_or] at hy
      simp only [σ_init, if_neg hy.1]
      exact h_mid_agree y (fun h => hy.2 h)
    · -- σ_init has none for all initialized variables
      intro y hy
      simp only [List.map_cons, List.mem_cons] at hy
      cases hy with
      | inl h => simp only [σ_init, h, if_pos rfl]
      | inr h =>
        simp only [σ_init]
        have : y ≠ x := fun heq => h_x_notin (heq ▸ h)
        simp only [if_neg this]
        exact h_mid_none y h
    · -- Execution: init x then rest
      simp only [List.map_cons]
      apply ReflTrans_Transitive
      · apply seq_process_stmt
        -- Execute init x from σ_init to σ_mid
        -- σ_init x = none, σ_mid x = σ_target x = some v
        have h_init_none : σ_init x = none := by simp [σ_init]
        have h_mid_x : σ_mid x = some v := by
          rw [h_mid_agree x h_x_notin]; exact h_v
        have h_mid_rest : ∀ y, x ≠ y → σ_mid y = σ_init y := by
          intro y hne; simp [σ_init, if_neg (Ne.symm hne)]
        exact init_unconstrained_step π φ x ty σ_init σ_mid δ v
          h_init_none h_mid_x h_mid_rest h_wfv
      · exact h_rest_exec

/-- An assume executes successfully when the condition holds. -/
theorem assume_reaches
    (π : String → Option Procedure) (φ : CoreEval → PureFunc Expression → CoreEval)
    (label : CoreLabel) (expr : Expression.Expr) (md : MetaData Expression)
    (σ : CoreStore) (δ : CoreEval)
    (h_true : δ σ expr = some HasBool.tt)
    (h_wf : WellFormedSemanticEvalBool δ) :
    CoreStepStar π φ
      (.stmt (Statement.assume label expr md) σ δ)
      (.terminal σ δ) :=
  ReflTrans.step _ _ _
    (StepStmt.step_cmd (EvalCommand.cmd_sem (EvalCmd.eval_assume h_true h_wf)))
    (ReflTrans.refl _)

/-- A list of assumes executes when all conditions hold. -/
theorem assumes_reach
    (π : String → Option Procedure) (φ : CoreEval → PureFunc Expression → CoreEval)
    (assumes : List Statement)
    (σ : CoreStore) (δ : CoreEval)
    (h_all_assume : ∀ s, s ∈ assumes → ∃ l e m,
      s = Statement.assume l e m ∧ δ σ e = some HasBool.tt)
    (h_wf : WellFormedSemanticEvalBool δ) :
    CoreStepStar π φ (.stmts assumes σ δ) (.terminal σ δ) := by
  induction assumes with
  | nil => exact ReflTrans.step _ _ _ StepStmt.step_stmts_nil (ReflTrans.refl _)
  | cons s rest ih =>
    obtain ⟨l, e, m, rfl, h_true⟩ := h_all_assume s List.mem_cons_self
    apply ReflTrans_Transitive
    · apply seq_process_stmt
      exact assume_reaches π φ l e m σ δ h_true h_wf
    · exact ih (fun s h => h_all_assume s (List.mem_cons_of_mem _ h))

/-- The postcondition assert is reachable in the verification block when the body executes. -/
theorem postcond_reachable_in_verifyBlock
    (π : String → Option Procedure) (φ : CoreEval → PureFunc Expression → CoreEval)
    (proc : Procedure) (blk_label : String) (pre_body : List Statement)
    (bodyLabel : String) (blk_md : MetaData Expression)
    (σ_init : CoreStore) (δ_init : CoreEval)
    (δ₀ : CoreEval) (σ₀ σ_final : CoreStore) (δ_final : CoreEval)
    (label : CoreLabel) (check : Procedure.Check)
    (h_pre_exec : CoreStepStar π φ (.stmts pre_body σ_init δ_init) (.terminal σ₀ δ₀))
    (h_body : CoreStepStar π φ (.stmts proc.body σ₀ δ₀) (.terminal σ_final δ_final))
    (h_post_in : (label, check) ∈ proc.spec.postconditions.toList)
    (h_default : check.attr = Procedure.CheckAttr.Default) :
    reachable π φ
      (Stmt.block blk_label (pre_body ++ [Stmt.block bodyLabel proc.body #[]] ++
        ensuresToAsserts proc.spec.postconditions) blk_md)
      ⟨σ_final, δ_final, ⟨label, check.expr, check.md⟩⟩ := by
  -- The assert statement for this postcondition
  have h_assert_in : Statement.assert label check.expr check.md ∈
      ensuresToAsserts proc.spec.postconditions := by
    unfold ensuresToAsserts; simp only [List.mem_filterMap]
    exact ⟨(label, check), h_post_in, by simp [h_default]⟩
  -- Find the position of this assert in the list
  obtain ⟨asserts_before, asserts_after, h_split⟩ :=
    List.mem_iff_append.mp h_assert_in
  -- Construct the execution path
  unfold reachable
  refine ⟨δ_init, σ_init, ?cfg, ?path, ?state⟩
  case cfg =>
    exact .block blk_label
      (.stmts (Statement.assert label check.expr check.md :: asserts_after) σ_final δ_final)
  case state =>
    simp only [ProgramState.ofConfig]
  case path =>
    -- Enter the block
    apply ReflTrans.step _ (.block blk_label (.stmts _ σ_init δ_init))
    · exact StepStmt.step_block
    -- Reassociate: (pre_body ++ [body_block]) ++ asserts = pre_body ++ ([body_block] ++ asserts)
    rw [List.append_assoc] at *
    apply ReflTrans_Transitive
    · -- Execute pre_body
      apply block_lift_steps
      exact stmts_process_to_suffix _ _ pre_body _ _ _ _ _ h_pre_exec
    -- Now at: block(stmts([body_block] ++ asserts))
    apply ReflTrans_Transitive
    · apply block_lift_steps
      -- Step into body_block :: asserts
      apply seq_process_stmt
      exact block_stmt_to_terminal _ _ bodyLabel proc.body #[] _ _ _ _ h_body
    -- Now at: block(stmts(asserts))
    -- Split asserts at our target
    rw [h_split]
    apply ReflTrans_Transitive
    · apply block_lift_steps
      apply stmts_process_to_suffix _ _ asserts_before
      apply assert_skips_to_terminal
      intro s hs
      have : s ∈ ensuresToAsserts proc.spec.postconditions := by
        rw [h_split]; exact List.mem_append_left _ hs
      unfold ensuresToAsserts at this
      simp only [List.mem_filterMap] at this
      obtain ⟨⟨l, c⟩, _, h_eq⟩ := this
      split at h_eq
      · exact absurd h_eq nofun
      · simp only [Option.some.injEq] at h_eq; exact ⟨_, _, _, h_eq.symm⟩
    -- Now at: block(stmts(assert :: asserts_after))
    exact ReflTrans.refl _

/-- Soundness of ProcBodyVerify: if the verification block is correct,
    then the procedure obeys its contract. -/
theorem procBodyVerify_sound
    (π : String → Option Procedure) (φ : CoreEval → PureFunc Expression → CoreEval)
    (proc : Procedure) (p : Program) (st : CoreTransformState)
    (stmt : Statement) (st' : CoreTransformState)
    (h_transform : (procToVerifyStmt proc p).run st = (Except.ok stmt, st'))
    (h_correct : stmt_correct π φ stmt)
    -- The verification block's pre_body (inits + assumes) does not get stuck:
    -- for any state where preconditions hold, there exists an initial state
    -- from which the pre_body executes to that state.
    -- This is guaranteed by the type checker (inits create variables with
    -- arbitrary values, assumes pass when preconditions hold).
    (h_pre_body_exec : ∀ (δ : CoreEval) (σ : CoreStore),
      (∀ (label : CoreLabel) (check : Procedure.Check),
        (label, check) ∈ proc.spec.preconditions.toList →
        δ σ check.expr = some HasBool.tt) →
      ∀ (pre_body : List Statement),
        (∃ (blk_label : String) (blk_md : MetaData Expression),
          stmt = Stmt.block blk_label
            (pre_body ++ [Stmt.block s!"body_{proc.header.name.name}" proc.body #[]] ++
              ensuresToAsserts proc.spec.postconditions) blk_md) →
        ∃ (σ_init : CoreStore) (δ_init : CoreEval),
          CoreStepStar π φ (.stmts pre_body σ_init δ_init) (.terminal σ δ)) :
    procedure_obeys_contract π φ proc := by
  obtain ⟨blk_label, pre_body, blk_md, h_stmt_eq⟩ :=
    procToVerifyStmt_structure proc p st stmt st' h_transform
  intro δ σ₀ σ_final δ_final h_pre h_body label check h_post_in h_default
  obtain ⟨σ_init, δ_init, h_pre_exec⟩ :=
    h_pre_body_exec δ σ₀ h_pre pre_body
      ⟨blk_label, blk_md, h_stmt_eq⟩
  have h_reach := postcond_reachable_in_verifyBlock π φ proc
    blk_label pre_body s!"body_{proc.header.name.name}" blk_md
    σ_init δ_init δ σ₀ σ_final δ_final
    label check h_pre_exec h_body h_post_in h_default
  rw [h_stmt_eq] at h_correct
  exact h_correct ⟨label, check.expr, check.md⟩
    ⟨σ_final, δ_final, ⟨label, check.expr, check.md⟩⟩ h_reach rfl

end ProcBodyVerifyCorrect
