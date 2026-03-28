/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Transform.ProcBodyVerify
import Strata.Transform.CoreSpecification
import Strata.Languages.Core.WF

/-! # Procedure Body Verification Correctness Proof -/

namespace ProcBodyVerifyCorrect

open Core Core.ProcBodyVerify Imperative Lambda Transform Core.WF

/-! ## Verification Statement Structure -/

/-- Structure: the output of `procToVerifyStmt` is a block
    `prefix ++ [bodyBlock] ++ postAsserts`, and all prefix statements
    are `.cmd` (init/assume commands). -/
theorem procToVerifyStmt_structure
    (proc : Procedure) (p : Program) (st st' : CoreTransformState)
    (verifyStmt : Statement)
    (h : (procToVerifyStmt proc p).run st = (Except.ok verifyStmt, st')) :
    ∃ (prefixStmts : List Statement),
      verifyStmt = Stmt.block s!"verify_{proc.header.name.name}"
        (prefixStmts ++ [Stmt.block s!"body_{proc.header.name.name}" proc.body #[]] ++
          ensuresToAsserts proc.spec.postconditions) #[] ∧
      (∀ s ∈ prefixStmts, ∃ c, s = Stmt.cmd c) := by
  unfold procToVerifyStmt at h
  simp only [bind, ExceptT.bind, ExceptT.mk, ExceptT.run, ExceptT.bindCont,
    pure, ExceptT.pure, StateT.bind] at h
  split at h
  · rename_i a st_mid heq
    cases a with
    | ok modifiesInits =>
      dsimp at h
      refine ⟨_, ((Prod.mk.inj h).1 |> Except.ok.inj).symm, ?_⟩
      intro s hs
      simp only [List.mem_append] at hs
      rcases hs with ((hs | hs) | hs) | hs
      · -- inputInits: each is Statement.init
        simp only [List.mem_map] at hs
        obtain ⟨⟨id, ty⟩, _, rfl⟩ := hs
        exact ⟨_, rfl⟩
      · -- outputInits: each is Statement.init
        simp only [List.mem_map] at hs
        obtain ⟨⟨id, ty⟩, _, rfl⟩ := hs
        exact ⟨_, rfl⟩
      · -- modifiesInits.flatten: each is Statement.init
        rw [List.mem_flatten] at hs
        obtain ⟨sublist, h_sub_mem, h_s_mem⟩ := hs
        -- Each element of modifiesInits is [Statement.init ..., Statement.init ...]
        -- Extract this from heq
        have h_form : ∀ sub ∈ modifiesInits, ∀ s' ∈ sub, ∃ c, s' = Stmt.cmd c := by
          clear h h_sub_mem h_s_mem sublist
          revert heq
          generalize proc.spec.modifies = gs
          induction gs generalizing st st_mid modifiesInits with
          | nil =>
            intro heq
            simp only [List.mapM_nil, pure, ExceptT.pure] at heq
            have := (Prod.mk.inj heq).1 |> Except.ok.inj; subst this
            intro _ h; simp at h
          | cons g rest ih =>
            intro heq
            simp only [List.mapM_cons, bind, ExceptT.bind, ExceptT.mk,
              ExceptT.bindCont, pure, ExceptT.pure, StateT.bind] at heq
            split at heq
            · rename_i res₁ st₁ heq₁
              cases res₁ with
              | ok gTy =>
                simp only [bind, StateT.bind, ExceptT.bindCont] at heq
                split at heq
                · rename_i rest_res st₂ heq₂
                  cases rest_res with
                  | ok restInits =>
                    dsimp at heq
                    have heq_mi := (Prod.mk.inj heq).1 |> Except.ok.inj
                    subst heq_mi
                    intro sub h_sub_mem s' h_s'_mem
                    cases h_sub_mem with
                    | head =>
                      split at heq₁
                      · rename_i ty_res ty_st heq_ty
                        cases ty_res with
                        | ok actualTy =>
                          simp only [StateT.pure] at heq₁
                          have := (Prod.mk.inj heq₁).1 |> Except.ok.inj
                          subst this
                          simp only [List.mem_cons, List.mem_nil_iff, or_false] at h_s'_mem
                          rcases h_s'_mem with rfl | rfl <;> exact ⟨_, rfl⟩
                        | error e =>
                          simp only [StateT.pure] at heq₁
                          exact absurd (Prod.mk.inj heq₁).1 (by intro h; cases h)
                    | tail _ h_in_rest =>
                      exact ih (st := st₁) (st_mid := st₂) (modifiesInits := restInits) heq₂ sub h_in_rest s' h_s'_mem
                  | error e =>
                    simp only [pure, StateT.pure] at heq
                    exact absurd (Prod.mk.inj heq).1 (by intro h; cases h)
              | error e =>
                dsimp at heq; exact absurd (Prod.mk.inj heq).1 (by intro h; cases h)
        exact h_form sublist h_sub_mem s h_s_mem
      · -- assumes: each is Statement.assume = Stmt.cmd
        simp only [requiresToAssumes, List.mem_map] at hs
        obtain ⟨⟨label, check⟩, _, rfl⟩ := hs
        exact ⟨_, rfl⟩
    | error e => dsimp at h; exact absurd (Prod.mk.inj h).1 (by intro h; cases h)

/-! ## Postcondition Assert Helpers -/

private theorem ensuresToAsserts_mem_is_assert
    {s : Statement} {pcs : ListMap CoreLabel Procedure.Check}
    (h : s ∈ ensuresToAsserts pcs) :
    ∃ l e md, s = Statement.assert l e md := by
  simp only [ensuresToAsserts, List.mem_filterMap] at h
  obtain ⟨⟨label, check⟩, _, h_eq⟩ := h
  split at h_eq
  · simp at h_eq
  · simp at h_eq; exact ⟨label, check.expr, check.md, h_eq.symm⟩

private theorem ensuresToAsserts_ecb (labels : List String)
    (pcs : ListMap CoreLabel Procedure.Check) :
    Stmt.exitsCoveredByBlocks.Block.exitsCoveredByBlocks labels (ensuresToAsserts pcs) := by
  apply all_cmd_exitsCoveredByBlocks
  intro s hs
  have ⟨l, e, md, heq⟩ := ensuresToAsserts_mem_is_assert hs
  exact ⟨CmdExt.cmd (Cmd.assert l e md), heq⟩

/-! ## Main Theorem -/

/-- If all asserts are valid in the verification statement produced by
    `procToVerifyStmt` (for initial environments satisfying `ProcEnvWF`),
    then `ProcedureCorrect` holds for the procedure. -/
theorem procBodyVerify_procedureCorrect
    (π : String → Option Procedure) (φ : CoreEval → PureFunc Expression → CoreEval)
    (proc : Procedure) (p : Program) (st : CoreTransformState)
    (verifyStmt : Statement) (st' : CoreTransformState)
    -- `h_transform`: procToVerifyStmt returned successfully.
    (h_transform : (procToVerifyStmt proc p).run st = (Except.ok verifyStmt, st'))
    -- `h_correct`: all asserts in `verifyStmt` are valid, given the
    -- well-formed initial states (e.g., all input arguments appear in the registerd file)
    (h_correct : Specification.AllAssertsValidWhen
      (Core.Specification.Lang.core π φ) (Core.Specification.ProcEnvWF proc) verifyStmt)
    -- `h_wf_ext`: the evaluator extension `φ` is well-formed
    (h_wf_ext : Core.WFEvalExtension φ) :
    -- Conclusion: ProcedureCorrect holds.
    Core.Specification.ProcedureCorrect π φ proc p verifyStmt := by

  obtain ⟨prefixStmts, h_eq, h_prefix_cmd⟩ :=
    procToVerifyStmt_structure proc p st st' verifyStmt h_transform
  let verifyLabel := s!"verify_{proc.header.name.name}"
  let bodyLabel := s!"body_{proc.header.name.name}"
  let postAsserts := ensuresToAsserts proc.spec.postconditions
  constructor
  · ----- Part 1: All asserts valid -----
    exact h_correct
  · ----- Part 2: Postconditions + hasFailure on termination -----
    intro h_wf_proc ρ₀ ρ' h_wf h_nf h_term
    have h_valid : ∀ (a : AssertId Expression) (cfg : CoreConfig),
        CoreStepStar π φ (.stmt verifyStmt ρ₀) cfg →
        Core.coreIsAtAssert cfg a →
        cfg.getEval cfg.getStore a.expr = some HasBool.tt :=
      fun a cfg h hat => h_correct a ρ₀ cfg h_wf h hat
    -- hasFailure = false (needed early for postconditions proof)
    have h_nf' : ρ'.hasFailure = Bool.false :=
      Core.core_noFailure_preserved π φ _ _ h_valid h_nf h_term
    -- Save wfBool preservation for later (before h_term is consumed)
    have h_wfb_term : WellFormedSemanticEvalBool ρ'.eval :=
      Core.core_wfBool_preserved π φ h_wf_ext
        (.stmt verifyStmt ρ₀) (.terminal ρ') h_wf.wfBool h_term
    -- From verifyStmt termination, get inner stmts termination
    -- (exits ruled out by exitsCoveredByBlocks + block_exitsCoveredByBlocks_noEscape)
    rw [h_eq] at h_term
    cases h_term with
    | step _ _ _ hstep hrest => cases hstep with
      | step_block =>
        -- Derive exit coverage from WFProcedureProp.bodyExitsCovered
        have h_body_ecb := h_wf_proc.bodyExitsCovered
        -- Block.ecb [] proc.body → Block.ecb [bodyLabel] proc.body (weakening)
        have h_body_ecb' : Stmt.exitsCoveredByBlocks.Block.exitsCoveredByBlocks
            [bodyLabel] proc.body :=
          (exitsCoveredByBlocks_weaken (labels₁ := []) (labels₂ := [bodyLabel]) (fun _ h => nomatch h)).2 proc.body h_body_ecb
        -- Build Block.ecb [] allStmts from parts
        have h_prefix_ecb : Stmt.exitsCoveredByBlocks.Block.exitsCoveredByBlocks [] prefixStmts :=
          all_cmd_exitsCoveredByBlocks [] prefixStmts h_prefix_cmd
        have h_ecb : Stmt.exitsCoveredByBlocks.Block.exitsCoveredByBlocks []
            (prefixStmts ++ [Stmt.block bodyLabel proc.body #[]] ++ postAsserts) :=
          block_exitsCoveredByBlocks_append [] _ _ (block_exitsCoveredByBlocks_append [] _ _ h_prefix_ecb
            ⟨h_body_ecb', True.intro⟩) (ensuresToAsserts_ecb [] proc.spec.postconditions)
        match block_reaches_terminal Expression (EvalCommand π φ) (EvalPureFunc φ) hrest with
        | .inl h_stmts_term =>
          -- Decompose: prefix | [bodyBlock] ++ postAsserts
          have h_stmts_term' : CoreStepStar π φ
              (.stmts (prefixStmts ++ ([Stmt.block bodyLabel proc.body #[]] ++ postAsserts)) ρ₀)
              (.terminal ρ') := by
            rw [List.append_assoc] at h_stmts_term; exact h_stmts_term
          have ⟨ρ₁, h_prefix_trace, h_rest_term⟩ :=
            stmts_append_terminates Expression (EvalCommand π φ) (EvalPureFunc φ) prefixStmts
              ([Stmt.block bodyLabel proc.body #[]] ++ postAsserts) ρ₀ ρ' h_stmts_term'
          -- Decompose: bodyBlock | postAsserts
          cases h_rest_term with
          | step _ _ _ hstep2 hrest2 => cases hstep2 with
            | step_stmts_cons =>
              have ⟨ρ₂, h_body_trace, h_post_trace⟩ :=
                seq_reaches_terminal Expression (EvalCommand π φ) (EvalPureFunc φ) hrest2
              -- Build trace: (.stmt verifyStmt ρ₀) →* (.block verifyLabel (.stmts postAsserts ρ₂))
              have h_to_post : CoreStepStar π φ (.stmt verifyStmt ρ₀)
                  (.block verifyLabel (.stmts postAsserts ρ₂)) := by
                rw [h_eq]
                exact ReflTrans_Transitive _ _ _ _
                  (step_block_enter Expression (EvalCommand π φ) (EvalPureFunc φ) verifyLabel _ #[] ρ₀)
                  (block_inner_star Expression (EvalCommand π φ) (EvalPureFunc φ) _ _ verifyLabel
                    (ReflTrans_Transitive _ _ _ _
                      (by rw [List.append_assoc]
                          exact stmts_prefix_terminal_append Expression (EvalCommand π φ) (EvalPureFunc φ) prefixStmts _ ρ₀ ρ₁ h_prefix_trace)
                      (ReflTrans_Transitive _ _ _ _
                        (.step _ _ _ .step_stmts_cons (.refl _))
                        (ReflTrans_Transitive _ _ _ _
                          (seq_inner_star Expression (EvalCommand π φ) (EvalPureFunc φ)
                            _ _ postAsserts h_body_trace)
                          (.step _ _ _ .step_seq_done (.refl _))))))
              -- postAsserts noFuncDecl
              have h_nofd_post : Block.noFuncDecl postAsserts = true := by
                suffices h_all_nofd : ∀ s ∈ postAsserts, Stmt.noFuncDecl s = true by
                  have h_block : ∀ (xs : List Statement),
                      (∀ s ∈ xs, Stmt.noFuncDecl s = true) → Block.noFuncDecl xs = true := by
                    intro xs; induction xs with
                    | nil => intro _; simp [Block.noFuncDecl]
                    | cons hd tl ih =>
                      intro h
                      simp only [Block.noFuncDecl, Bool.and_eq_true]
                      exact ⟨h hd (.head _), ih (fun s hs => h s (.tail _ hs))⟩
                  exact h_block postAsserts h_all_nofd
                intro s hs
                have ⟨l, e, md, heq⟩ := ensuresToAsserts_mem_is_assert hs
                subst heq; simp [Stmt.noFuncDecl]
              -- Extract stmts trace for postAsserts
              have h_post_stmts : CoreStepStar π φ (.stmts postAsserts ρ₂) (.terminal ρ') := by
                simp only [List.append] at h_post_trace; exact h_post_trace
              -- Derive eval and store preservation through postAsserts
              have h_eval_post : ρ'.eval = ρ₂.eval :=
                block_noFuncDecl_preserves_eval Expression (EvalCommand π φ) (EvalPureFunc φ) postAsserts ρ₂ ρ' h_nofd_post h_post_stmts
              have h_store_post : ρ'.store = ρ₂.store :=
                Core.stmts_allAssert_preserves_store π φ postAsserts ρ₂ ρ'
                  (fun s hs => ensuresToAsserts_mem_is_assert hs) h_post_stmts
              -- Derive WellFormedSemanticEvalBool at ρ₂ using wfBool preservation
              have h_wfb₂ : WellFormedSemanticEvalBool ρ₂.eval := by
                rw [← h_eval_post]; exact h_wfb_term
              -- Show every postcondition assert evaluates to true at ρ₂
              -- by induction on the suffix of postAsserts
              have h_all_post_valid : ∀ s ∈ postAsserts, ∀ l e md,
                  s = Statement.assert l e md → ρ₂.eval ρ₂.store e = some HasBool.tt := by
                suffices h_sfx :
                    ∀ (sfx : List Statement),
                      (∀ s ∈ sfx, ∃ l e md, s = Statement.assert l e md) →
                      CoreStepStar π φ (.stmt verifyStmt ρ₀)
                        (.block verifyLabel (.stmts sfx ρ₂)) →
                      ∀ s ∈ sfx, ∀ l e md,
                        s = Statement.assert l e md →
                        ρ₂.eval ρ₂.store e = some HasBool.tt by
                  exact h_sfx postAsserts
                    (fun s hs => ensuresToAsserts_mem_is_assert hs) h_to_post
                intro sfx h_all_assert h_trace
                induction sfx with
                | nil => intro _ h_mem; contradiction
                | cons hd tl ih =>
                  intro s h_mem l e md h_s_eq
                  have ⟨lh, eh, mdh, h_hd_eq⟩ := h_all_assert hd (.head _)
                  subst h_hd_eq
                  have h_at_head : Core.coreIsAtAssert
                      (.block verifyLabel (.stmts (Statement.assert lh eh mdh :: tl) ρ₂))
                      ⟨lh, eh⟩ := by
                    simp only [Core.coreIsAtAssert]; exact ⟨trivial, trivial⟩
                  have h_head_eval := h_valid ⟨lh, eh⟩ _ h_trace h_at_head
                  simp only [Config.getEval, Config.getStore] at h_head_eval
                  cases h_mem with
                  | head _ =>
                    injection h_s_eq with h1; injection h1 with h2
                    injection h2 with _ h3; subst h3; exact h_head_eval
                  | tail _ h_in_tl =>
                    have h_assert_step : CoreStepStar π φ
                        (.stmt (Statement.assert lh eh mdh) ρ₂) (.terminal ρ₂) := by
                      have h1 : CoreStepStar π φ
                          (.stmt (Statement.assert lh eh mdh) ρ₂)
                          (.terminal ⟨ρ₂.store, ρ₂.eval, ρ₂.hasFailure || false⟩) :=
                        .step _ _ _
                          (.step_cmd (@EvalCommand.cmd_sem π φ ρ₂.eval ρ₂.store
                            (Cmd.assert lh eh mdh) ρ₂.store false
                            (EvalCmd.eval_assert_pass h_head_eval h_wfb₂)))
                          (.refl _)
                      have h2 : (⟨ρ₂.store, ρ₂.eval, ρ₂.hasFailure || false⟩ : Env Expression) = ρ₂ := by
                        cases ρ₂; simp [Bool.or_false]
                      rw [h2] at h1; exact h1
                    have h_trace_tl := ReflTrans_Transitive _ _ _ _ h_trace
                      (block_inner_star Expression (EvalCommand π φ) (EvalPureFunc φ) _ _ verifyLabel
                        (stmts_cons_step Expression (EvalCommand π φ) (EvalPureFunc φ)
                          (Statement.assert lh eh mdh) tl ρ₂ ρ₂ h_assert_step))
                    exact ih (fun s' hs' => h_all_assert s' (.tail _ hs'))
                      h_trace_tl s h_in_tl l e md h_s_eq
              -- Prove postconditions hold and hasFailure is false
              constructor
              · -- Each non-free postcondition evaluates to true
                intro label check h_mem h_attr
                have h_in : Statement.assert label check.expr check.md ∈ postAsserts := by
                  simp only [postAsserts, ensuresToAsserts, List.mem_filterMap]
                  exact ⟨(label, check), h_mem, by simp [h_attr]⟩
                have h_at_ρ₂ := h_all_post_valid _ h_in label check.expr check.md rfl
                -- Transfer from ρ₂ to ρ' using store and eval preservation
                rw [h_eval_post, h_store_post]
                exact h_at_ρ₂
              · exact h_nf'
        | .inr ⟨lbl, h_stmts_exit⟩ =>
          -- Inner stmts exit — contradicts exitsCoveredByBlocks
          exact absurd h_stmts_exit
            (block_exitsCoveredByBlocks_noEscape Expression
              (EvalCommand π φ) (EvalPureFunc φ) _ h_ecb ρ₀ lbl ρ')

end ProcBodyVerifyCorrect
