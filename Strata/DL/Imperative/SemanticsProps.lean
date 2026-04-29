/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.DL.Imperative.CmdSemantics
import all Strata.DL.Imperative.CmdSemantics
public import Strata.DL.Imperative.StmtSemantics
import all Strata.DL.Imperative.StmtSemantics
import all Strata.DL.Imperative.Cmd
import all Strata.DL.Util.Relations

namespace Imperative

public section

theorem eval_assert_store_cst
  [HasFvar P] [HasBool P] [HasNot P]:
  EvalCmd P δ σ (.assert l e md) σ' f → σ = σ' := by
  intros Heval; cases Heval with
  | eval_assert_pass _ => rfl
  | eval_assert_fail _ => rfl

theorem eval_stmt_assert_store_cst
  [HasFvar P] [HasBool P] [HasNot P] :
  EvalStmtSmall P (EvalCmd P) extendEval ρ (.cmd (Cmd.assert l e md)) ρ' → ρ.store = ρ'.store := by
  intro Heval
  unfold EvalStmtSmall at Heval
  -- step_cmd produces .terminal, so the trace is one step then done
  match Heval with
  | .step _ _ _ (.step_cmd hcmd) hrest =>
    -- hrest : StepStmtStar ... (.terminal ...) (.terminal ρ')
    -- .terminal is terminal (no further steps), so hrest must be refl
    cases hrest with
    | refl => simp; exact eval_assert_store_cst hcmd
    | step _ _ _ hstep _ => exact absurd hstep (by intro h; cases h)

theorem eval_stmt_assert_eval_cst
  [HasFvar P] [HasBool P] [HasNot P] :
  EvalStmtSmall P (EvalCmd P) extendEval ρ (.cmd (Cmd.assert l e md)) ρ' → ρ.eval = ρ'.eval := by
  intro Heval
  unfold EvalStmtSmall at Heval
  match Heval with
  | .step _ _ _ (.step_cmd _) hrest =>
    cases hrest with
    | refl => simp
    | step _ _ _ hstep _ => exact absurd hstep (by intro h; cases h)

theorem eval_stmts_assert_store_cst
  [HasFvar P] [HasBool P] [HasNot P] :
  EvalStmtsSmall P (EvalCmd P) extendEval ρ [(.cmd (Cmd.assert l e md))] ρ' → ρ.store = ρ'.store := by
  intro Heval
  -- Use stmts_cons_step inversion: the singleton list steps through
  -- .stmts [assert] ρ →* .stmts [] ρ'' →* .terminal ρ'
  -- where the head statement preserves the store.
  have hstmt : EvalStmtSmall P (EvalCmd P) extendEval ρ (.cmd (Cmd.assert l e md)) ρ' := by
    unfold EvalStmtsSmall at Heval
    unfold EvalStmtSmall
    -- .stmts [s] ρ → .seq (.stmt s ρ) [] → ... → .seq (.terminal ρ'') [] → .stmts [] ρ'' → .terminal ρ''
    have hcons := stmts_cons_step P (EvalCmd P) extendEval
      (.cmd (Cmd.assert l e md)) [] ρ
    -- We need to extract the stmt execution from the stmts execution
    -- Use seq_reaches_terminal to invert
    match Heval with
    | .step _ _ _ .step_stmts_cons hrest =>
      have ⟨ρ₁, hterm, htail⟩ := seq_reaches_terminal P (EvalCmd P) extendEval hrest
      -- htail : StepStmtStar (.stmts [] ρ₁) (.terminal ρ')
      -- From htail, .stmts [] → .terminal in one step, so ρ₁ = ρ'
      match htail with
      | .step _ _ _ .step_stmts_nil hrest' =>
        cases hrest' with
        | refl => exact hterm
        | step _ _ _ h _ => exact absurd h (by intro h; cases h)
  exact eval_stmt_assert_store_cst hstmt

theorem eval_stmt_assert_eq_of_pure_expr_eq
  [HasFvar P] [HasBool P] [HasNot P] :
  WellFormedSemanticEvalBool ρ.eval →
  (EvalStmtSmall P (EvalCmd P) extendEval ρ (.cmd (Cmd.assert l1 e md1)) ρ' ↔
  EvalStmtSmall P (EvalCmd P) extendEval ρ (.cmd (Cmd.assert l2 e md2)) ρ') := by
  intro Hwf
  constructor <;>
  (
    intro Heval
    unfold EvalStmtSmall at Heval ⊢
    match Heval with
    | .step _ _ _ (.step_cmd hcmd) hrest =>
      cases hrest with
      | refl =>
        cases hcmd with
        | eval_assert_pass htt _ =>
          exact .step _ _ _ (.step_cmd (EvalCmd.eval_assert_pass htt Hwf)) (.refl _)
        | eval_assert_fail hne _ =>
          exact .step _ _ _ (.step_cmd (EvalCmd.eval_assert_fail hne Hwf)) (.refl _)
      | step _ _ _ hstep _ => exact absurd hstep (by intro h; cases h)
  )

/-! ### hasFailure monotonicity and irrelevance

`hasFailure` is never consulted by any `StepStmt` premise,
so it is both *monotone* (once `true`, stays `true`) and *irrelevant*
(changing only `hasFailure` in the input env yields an execution with the
same `store` and `eval` in the output).
-/

private theorem step_hasFailure_monotone
  {P : PureExpr} {CmdT : Type} {EvalCmd : EvalCmdParam P CmdT}
  {extendEval : ExtendEval P}
  [HasBool P] [HasNot P]
  {c c' : Config P CmdT}
  (hstep : StepStmt P EvalCmd extendEval c c')
  (hf : c.getEnv.hasFailure = true) :
  c'.getEnv.hasFailure = true := by
  induction hstep with
  | step_cmd _ => simp [Config.getEnv]; left; exact hf
  | step_block => simp [Config.getEnv]; exact hf
  | step_ite_true _ _ => exact hf
  | step_ite_false _ _ => exact hf
  | step_ite_nondet_true => exact hf
  | step_ite_nondet_false => exact hf
  | step_loop_enter _ _ _ _ =>
    simp [Config.getEnv]; left; exact hf
  | step_loop_exit _ _ _ _ =>
    simp [Config.getEnv]; left; exact hf
  | step_loop_nondet_enter _ _ =>
    simp [Config.getEnv]; left; exact hf
  | step_loop_nondet_exit _ _ =>
    simp [Config.getEnv]; left; exact hf
  | step_exit => exact hf
  | step_funcDecl => simp [Config.getEnv]; exact hf
  | step_typeDecl => exact hf
  | step_stmts_nil => exact hf
  | step_stmts_cons => exact hf
  | step_seq_inner _ ih => exact ih hf
  | step_seq_done => exact hf
  | step_seq_exit => exact hf
  | step_block_body _ ih => exact ih hf
  | step_block_done => exact hf
  | step_block_exit_none => exact hf
  | step_block_exit_match _ => exact hf
  | step_block_exit_mismatch _ => exact hf

theorem EvalStmtSmall_hasFailure_monotone
  {P : PureExpr} {CmdT : Type} {EvalCmd : EvalCmdParam P CmdT}
  {extendEval : ExtendEval P}
  {ρ ρ' : Env P} {s : Stmt P CmdT}
  [HasBool P] [HasNot P] :
  EvalStmtSmall P EvalCmd extendEval ρ s ρ' →
  ρ.hasFailure = true → ρ'.hasFailure = true := by
  intro Heval Hf
  suffices ∀ c c', StepStmtStar P EvalCmd extendEval c c' →
      c.getEnv.hasFailure = true → c'.getEnv.hasFailure = true by
    exact this _ _ Heval Hf
  intro c c' hstar hf
  induction hstar with
  | refl => exact hf
  | step _ _ _ hstep _ ih => exact ih (step_hasFailure_monotone hstep hf)

theorem EvalStmtsSmall_hasFailure_monotone
  {P : PureExpr} {CmdT : Type} {EvalCmd : EvalCmdParam P CmdT}
  {extendEval : ExtendEval P}
  {ρ ρ' : Env P} {ss : List (Stmt P CmdT)}
  [HasBool P] [HasNot P] :
  EvalStmtsSmall P EvalCmd extendEval ρ ss ρ' →
  ρ.hasFailure = true → ρ'.hasFailure = true := by
  intro Heval Hf
  suffices ∀ c c', StepStmtStar P EvalCmd extendEval c c' →
      c.getEnv.hasFailure = true → c'.getEnv.hasFailure = true by
    exact this _ _ Heval Hf
  intro c c' hstar hf
  induction hstar with
  | refl => exact hf
  | step _ _ _ hstep _ ih => exact ih (step_hasFailure_monotone hstep hf)

theorem StepStmtStar_hasFailure_monotone
  {P : PureExpr} {CmdT : Type} {EvalCmd : EvalCmdParam P CmdT}
  {extendEval : ExtendEval P}
  [HasBool P] [HasNot P]
  {c c' : Config P CmdT}
  (hstar : StepStmtStar P EvalCmd extendEval c c')
  (hf : c.getEnv.hasFailure = true) :
  c'.getEnv.hasFailure = true := by
  induction hstar with
  | refl => exact hf
  | step _ _ _ hstep _ ih => exact ih (step_hasFailure_monotone hstep hf)

theorem EvalStmtSmall_hasFailure_irrel
  {P : PureExpr} {CmdT : Type} {EvalCmd : EvalCmdParam P CmdT}
  {extendEval : ExtendEval P}
  {ρ ρ' : Env P} {s : Stmt P CmdT}
  [HasBool P] [HasNot P] :
  EvalStmtSmall P EvalCmd extendEval ρ s ρ' →
  ∀ (ρ₂ : Env P), ρ₂.store = ρ.store → ρ₂.eval = ρ.eval →
  ∃ ρ₂', EvalStmtSmall P EvalCmd extendEval ρ₂ s ρ₂' ∧
    ρ₂'.store = ρ'.store ∧ ρ₂'.eval = ρ'.eval :=
  smallStep_hasFailure_irrel P EvalCmd extendEval s ρ ρ'

theorem EvalStmtsSmall_hasFailure_irrel
  {P : PureExpr} {CmdT : Type} {EvalCmd : EvalCmdParam P CmdT}
  {extendEval : ExtendEval P}
  {ρ ρ' : Env P} {ss : List (Stmt P CmdT)}
  [HasBool P] [HasNot P] :
  EvalStmtsSmall P EvalCmd extendEval ρ ss ρ' →
  ∀ (ρ₂ : Env P), ρ₂.store = ρ.store → ρ₂.eval = ρ.eval →
  ∃ ρ₂', EvalStmtsSmall P EvalCmd extendEval ρ₂ ss ρ₂' ∧
    ρ₂'.store = ρ'.store ∧ ρ₂'.eval = ρ'.eval := by
  intro Heval ρ₂ Hstore Heval_eq
  -- Reuse the simulation-based proof from StmtSemantics
  -- smallStep_hasFailure_irrel works on .stmt configs; we need .stmts
  -- Use the same simulation technique directly
  suffices ∀ (c₁ c₂ : Config P CmdT),
      ConfigSE P c₁ c₂ →
      ∀ c₁', StepStmtStar P EvalCmd extendEval c₁ c₁' →
      ∃ c₂', StepStmtStar P EvalCmd extendEval c₂ c₂' ∧ ConfigSE P c₁' c₂' by
    have heq_init : ConfigSE P (.stmts ss ρ) (.stmts ss ρ₂) := ⟨rfl, Hstore.symm, Heval_eq.symm⟩
    have ⟨c₂', hstar₂, heq₂⟩ := this _ _ heq_init _ Heval
    match c₂', heq₂ with
    | .terminal ρ₂', heq_t => exact ⟨ρ₂', hstar₂, heq_t.1.symm, heq_t.2.symm⟩
  intro c₁ c₂ heq c₁' hstar
  induction hstar generalizing c₂ with
  | refl => exact ⟨c₂, .refl _, heq⟩
  | step _ mid _ hstep _ ih =>
    have ⟨mid₂, hstep₂, heq_mid⟩ := step_simulation P EvalCmd extendEval _ _ _ hstep heq
    have ⟨c₂', hstar₂, heq_final⟩ := ih _ heq_mid
    exact ⟨c₂', .step _ _ _ hstep₂ hstar₂, heq_final⟩

/-! ### Assert elimination -/

theorem eval_stmts_assert_elim
  [HasFvar P] [HasBool P] [HasNot P] :
  WellFormedSemanticEvalBool ρ.eval →
  EvalStmtsSmall P (EvalCmd P) extendEval ρ (.cmd (.assert l1 e md1) :: cmds) ρ' →
  ∃ ρ'', EvalStmtsSmall P (EvalCmd P) extendEval ρ cmds ρ'' ∧
    ρ''.store = ρ'.store ∧ ρ''.eval = ρ'.eval ∧
    (ρ'.hasFailure = false → ρ''.hasFailure = false) := by
  intro Hwf Heval
  unfold EvalStmtsSmall at Heval
  match Heval with
  | .step _ _ _ .step_stmts_cons hrest =>
    have ⟨ρ₁, hterm_assert, htail⟩ := seq_reaches_terminal P (EvalCmd P) extendEval hrest
    -- The assert takes exactly one step_cmd to terminal
    have ⟨hcmd, hσ, hδ⟩ : (∃ σ' f, EvalCmd P ρ.eval ρ.store (.assert l1 e md1) σ' f) ∧
        ρ.store = ρ₁.store ∧ ρ.eval = ρ₁.eval := by
      match hterm_assert with
      | .step _ _ _ (.step_cmd hcmd) (.refl _) =>
        exact ⟨⟨_, _, hcmd⟩, eval_assert_store_cst hcmd, rfl⟩
    -- Use hasFailure_irrel to re-run cmds from ρ
    have ⟨ρ'', Hblock, Hstore, Heval_eq⟩ := EvalStmtsSmall_hasFailure_irrel htail ρ hσ hδ
    -- Determine whether the assert passed or failed
    match hterm_assert with
    | .step _ _ _ (.step_cmd hcmd) (.refl _) =>
      cases hcmd with
      | eval_assert_pass =>
        -- ρ₁ = { ρ with hasFailure := ρ.hasFailure || false } = ρ
        exists ρ'
        refine ⟨?_, rfl, rfl, id⟩
        show StepStmtStar P (EvalCmd P) extendEval (.stmts cmds ρ) (.terminal ρ')
        have : ρ = { store := ρ.store, eval := ρ.eval, hasFailure := ρ.hasFailure || false } := by
          cases ρ; simp
        rw [this]; exact htail
      | eval_assert_fail =>
        exists ρ''
        refine ⟨Hblock, Hstore, Heval_eq, ?_⟩
        intro Hf
        -- ρ₁.hasFailure = ρ.hasFailure || true = true
        -- By monotonicity, ρ'.hasFailure = true, contradicting Hf
        have hf1 : (Env.mk ρ.store ρ.eval (ρ.hasFailure || true)).hasFailure = true := by simp
        exact absurd (EvalStmtsSmall_hasFailure_monotone htail hf1) (by simp [Hf])

theorem assert_elim
  [HasFvar P] [HasBool P] [HasNot P] :
  WellFormedSemanticEvalBool ρ.eval →
  EvalStmtsSmall P (EvalCmd P) extendEval ρ (.cmd (.assert l1 e md1) :: [.cmd (.assert l2 e md2)]) ρ' →
  EvalStmtsSmall P (EvalCmd P) extendEval ρ [.cmd (.assert l3 e md3)] ρ' := by
  intro Hwf Heval
  unfold EvalStmtsSmall at Heval ⊢
  -- Invert: first assert
  match Heval with
  | .step _ _ _ .step_stmts_cons hrest =>
    have ⟨ρ₁, hterm1, htail1⟩ := seq_reaches_terminal P (EvalCmd P) extendEval hrest
    match hterm1 with
    | .step _ _ _ (.step_cmd hcmd1) (.refl _) =>
      -- Invert: second assert (from htail1 which is .stmts [assert2] ρ₁ →* .terminal ρ')
      match htail1 with
      | .step _ _ _ .step_stmts_cons hrest2 =>
        have ⟨ρ₂, hterm2, htail2⟩ := seq_reaches_terminal P (EvalCmd P) extendEval hrest2
        match hterm2 with
        | .step _ _ _ (.step_cmd hcmd2) (.refl _) =>
          match htail2 with
          | .step _ _ _ .step_stmts_nil (.refl _) =>
            -- Both asserts preserve store, so ρ₂ has same store/eval as ρ
            -- hcmd1 and hcmd2 both evaluate e in the same store/eval
            -- They must agree on pass/fail
            cases hcmd1 with
            | eval_assert_pass h1 _ =>
              -- e evaluates to tt; hcmd2 also sees tt (same store/eval)
              -- Build single assert3 that passes, producing same ρ'
              -- ρ' = { store := ρ.store, eval := ρ.eval, hasFailure := (ρ.hasFailure || false) || f₂ }
              -- We need to produce the same env with a single assert
              -- Since h1 : ρ.eval ρ.store e = some tt, hcmd2 must also pass
              cases hcmd2 with
              | eval_assert_pass _ _ =>
                apply ReflTrans.step _ _ _ .step_stmts_cons
                apply ReflTrans.step _ _ _ (.step_seq_inner (.step_cmd (EvalCmd.eval_assert_pass h1 Hwf)))
                apply ReflTrans.step _ _ _ .step_seq_done
                apply ReflTrans.step _ _ _ .step_stmts_nil
                simp_all [Bool.or_false]; exact .refl _
              | eval_assert_fail h2 _ =>
                simp at h2
                exact absurd (h1.symm.trans h2)
                  (by exact fun h => HasBool.tt_is_not_ff (Option.some.inj h))
            | eval_assert_fail h1 _ =>
              cases hcmd2 with
              | eval_assert_pass h2 _ =>
                simp at h2
                exact absurd (h2.symm.trans h1)
                  (by exact fun h => HasBool.tt_is_not_ff (Option.some.inj h))
              | eval_assert_fail _ _ =>
                apply ReflTrans.step _ _ _ .step_stmts_cons
                apply ReflTrans.step _ _ _ (.step_seq_inner (.step_cmd (EvalCmd.eval_assert_fail h1 Hwf)))
                apply ReflTrans.step _ _ _ .step_seq_done
                apply ReflTrans.step _ _ _ .step_stmts_nil
                simp_all [Bool.or_true]; exact .refl _

theorem UpdateStateComm {P: PureExpr} {x1 x2: P.Ident} {σ σ' σ'' σ1 σ2: SemanticStore P} {v1 v2: P.Expr}
  [DecidableEq P.Ident]:
  ¬ x1 = x2 →
  UpdateState P σ x1 v1 σ1 →
  UpdateState P σ1 x2 v2 σ' →
  UpdateState P σ x2 v2 σ2 →
  UpdateState P σ2 x1 v1 σ'' →
  σ' = σ'' := by
  intro Hneq Hu1 Hu2 Hu3 Hu4
  cases Hu1; cases Hu2; cases Hu3; cases Hu4
  ext i e
  rename_i Hfa1 _ _ _ Hfa2 _ _ _ Hfa3 _ _ _ Hfa4 _
  simp at Hfa1 Hfa2 Hfa3 Hfa4
  rw[Eq.comm] at Hneq
  by_cases Heq1: x1 = i
  simp_all
  by_cases Heq2: x2 = i
  rw[Eq.comm] at Hneq
  specialize Hfa4 x2 Hneq
  simp_all
  specialize Hfa1 i Heq1
  specialize Hfa2 i Heq2
  specialize Hfa3 i Heq2
  specialize Hfa4 i Heq1
  simp_all

theorem UpdateState_InitStateComm {P: PureExpr} {x1 x2: P.Ident} {σ σ' σ'' σ1 σ2: SemanticStore P} {v1 v2: P.Expr}
  [DecidableEq P.Ident]:
  ¬ x1 = x2 →
  UpdateState P σ x1 v1 σ1 →
  InitState P σ1 x2 v2 σ' →
  InitState P σ x2 v2 σ2 →
  UpdateState P σ2 x1 v1 σ'' →
  σ' = σ'' := by
  intro Hneq Hu1 Hu2 Hu3 Hu4
  cases Hu1; cases Hu2; cases Hu3; cases Hu4
  ext i e
  rename_i Hfa1 _ _ Hfa2 _ _ Hfa3 _ _ _ Hfa4 _
  simp at Hfa1 Hfa2 Hfa3 Hfa4
  rw[Eq.comm] at Hneq
  by_cases Heq1: x1 = i
  simp_all
  by_cases Heq2: x2 = i
  rw[Eq.comm] at Hneq
  specialize Hfa4 x2 Hneq
  simp_all
  specialize Hfa1 i Heq1
  specialize Hfa2 i Heq2
  specialize Hfa3 i Heq2
  specialize Hfa4 i Heq1
  simp_all

theorem semantic_eval_eq_of_eval_cmd_set_unrelated_var
  [HasVarsImp P (Cmd P)] [HasVarsPure P P.Expr]
  [HasFvar P] [HasVal P] [HasBool P] [HasNot P]:
  WellFormedSemanticEvalExprCongr δ →
  ¬ v ∈ HasVarsPure.getVars e →
  EvalCmd P δ σ (Cmd.set v (.det e') md) σ' f →
  δ σ e = δ σ' e := by
  intro Hwf Hnin Heval
  unfold WellFormedSemanticEvalExprCongr at Hwf
  specialize Hwf e σ σ'
  have: ∀ (v : P.Ident), v ∈ HasVarsPure.getVars e → σ v = σ' v := by
    cases Heval
    rename_i Hu
    cases Hu
    rename_i Hfa _
    intro v' Hv'
    ext e'
    by_cases Hc: ¬ v = v'
    specialize Hfa v' Hc
    simp_all
    simp_all
  exact Hwf this

theorem eval_cmd_set_comm'
  [HasVarsImp P (List (Stmt P (Cmd P)))] [HasVarsImp P (Cmd P)]
  [HasFvar P] [HasVal P] [HasBool P] [HasNot P] [DecidableEq P.Ident] :
  ¬ x1 = x2 →
  δ σ v1 = δ σ2 v1 →
  δ σ v2 = δ σ1 v2 →
  EvalCmd P δ σ (Cmd.set x1 (.det v1) md1) σ1 f1 →
  EvalCmd P δ σ1 (Cmd.set x2 (.det v2) md2) σ' f2 →
  EvalCmd P δ σ (Cmd.set x2 (.det v2) md2') σ2 f3 →
  EvalCmd P δ σ2 (Cmd.set x1 (.det v1) md1') σ'' f4 →
  σ' = σ'' := by
  intro Hneq Heq1 Heq2 Hs1 Hs2 Hs3 Hs4
  cases Hs1 with | eval_set _ Hu1 _ =>
  cases Hs2 with | eval_set _ Hu2 _ =>
  cases Hs3 with | eval_set _ Hu3 _ =>
  cases Hs4 with | eval_set _ Hu4 _ =>
  simp_all
  exact UpdateStateComm Hneq Hu1 Hu2 Hu3 Hu4

theorem eval_cmd_set_comm
  [HasVarsImp P (List (Stmt P (Cmd P)))] [HasVarsImp P (Cmd P)] [HasVarsPure P P.Expr]
  [HasFvar P] [HasVal P] [HasBool P] [HasNot P] [DecidableEq P.Ident]:
  WellFormedSemanticEvalExprCongr δ →
  ¬ x1 = x2 →
  ¬ x1 ∈ HasVarsPure.getVars v2 →
  ¬ x2 ∈ HasVarsPure.getVars v1 →
  EvalCmd P δ σ (Cmd.set x1 (.det v1) md1) σ1 f1 →
  EvalCmd P δ σ1 (Cmd.set x2 (.det v2) md2) σ' f2 →
  EvalCmd P δ σ (Cmd.set x2 (.det v2) md2') σ2 f3 →
  EvalCmd P δ σ2 (Cmd.set x1 (.det v1) md1') σ'' f4 →
  σ' = σ'' := by
  intro Hwf Hneq Hnin1 Hnin2 Hs1 Hs2 Hs3 Hs4
  have Heval2:= semantic_eval_eq_of_eval_cmd_set_unrelated_var Hwf Hnin1 Hs1
  have Heval1:= semantic_eval_eq_of_eval_cmd_set_unrelated_var Hwf Hnin2 Hs3
  exact eval_cmd_set_comm' Hneq Heval1 Heval2 Hs1 Hs2 Hs3 Hs4

theorem eval_stmt_set_comm
  [HasVarsImp P (List (Stmt P (Cmd P)))] [HasVarsImp P (Cmd P)] [HasVarsPure P P.Expr]
  [HasFvar P] [HasVal P] [HasBool P] [HasNot P] [DecidableEq P.Ident]:
  WellFormedSemanticEvalExprCongr ρ.eval →
  ¬ x1 = x2 →
  ¬ x1 ∈ HasVarsPure.getVars v2 →
  ¬ x2 ∈ HasVarsPure.getVars v1 →
  EvalStmtSmall P (EvalCmd P) evalFun ρ (.cmd (Cmd.set x1 (.det v1) md1)) ρ1 →
  EvalStmtSmall P (EvalCmd P) evalFun ρ1 (.cmd (Cmd.set x2 (.det v2) md2)) ρ' →
  EvalStmtSmall P (EvalCmd P) evalFun ρ (.cmd (Cmd.set x2 (.det v2) md2')) ρ2 →
  EvalStmtSmall P (EvalCmd P) evalFun ρ2 (.cmd (Cmd.set x1 (.det v1) md1')) ρ'' →
  ρ'.store = ρ''.store := by
  intro Hwf Hneq Hnin1 Hnin2 Hs1 Hs2 Hs3 Hs4
  unfold EvalStmtSmall at Hs1 Hs2 Hs3 Hs4
  match Hs1, Hs2, Hs3, Hs4 with
  | .step _ _ _ (.step_cmd Hc1) (.refl _),
    .step _ _ _ (.step_cmd Hc2) (.refl _),
    .step _ _ _ (.step_cmd Hc3) (.refl _),
    .step _ _ _ (.step_cmd Hc4) (.refl _) =>
    simp
    exact eval_cmd_set_comm Hwf Hneq Hnin1 Hnin2 Hc1 Hc2 Hc3 Hc4

theorem eval_stmts_set_comm
  [HasVarsImp P (List (Stmt P (Cmd P)))] [HasVarsImp P (Cmd P)] [HasVarsPure P P.Expr]
  [HasFvar P] [HasVal P] [HasBool P] [HasNot P] [DecidableEq P.Ident] :
  WellFormedSemanticEvalExprCongr ρ.eval →
  ¬ x1 = x2 →
  ¬ x1 ∈ HasVarsPure.getVars v2 →
  ¬ x2 ∈ HasVarsPure.getVars v1 →
  EvalStmtsSmall P (EvalCmd P) evalFun ρ [(.cmd (Cmd.set x1 (.det v1) md1)), (.cmd (Cmd.set x2 (.det v2) md2))] ρ' →
  EvalStmtsSmall P (EvalCmd P) evalFun ρ [(.cmd (Cmd.set x2 (.det v2) md2')), (.cmd (Cmd.set x1 (.det v1) md1'))] ρ'' →
  ρ'.store = ρ''.store := by
  intro Hwf Hneq Hnin1 Hnin2 Heval1 Heval2
  -- Extract the four EvalCmd's from the two list executions
  -- Each list [cmd1, cmd2] decomposes via:
  -- stmts_cons → seq → cmd1 terminal → stmts [cmd2] → seq → cmd2 terminal → stmts [] → terminal
  have extract := fun (s1 s2 : Stmt P (Cmd P)) (ρ₀ ρ_final : Env P)
      (h : EvalStmtsSmall P (EvalCmd P) evalFun ρ₀ [s1, s2] ρ_final) =>
    show ∃ ρ_mid, EvalStmtSmall P (EvalCmd P) evalFun ρ₀ s1 ρ_mid ∧
        EvalStmtSmall P (EvalCmd P) evalFun ρ_mid s2 ρ_final from by
      unfold EvalStmtsSmall EvalStmtSmall at *
      match h with
      | .step _ _ _ .step_stmts_cons hrest =>
        have ⟨ρ₁, hterm1, htail1⟩ := seq_reaches_terminal P (EvalCmd P) evalFun hrest
        match htail1 with
        | .step _ _ _ .step_stmts_cons hrest2 =>
          have ⟨ρ₂, hterm2, htail2⟩ := seq_reaches_terminal P (EvalCmd P) evalFun hrest2
          match htail2 with
          | .step _ _ _ .step_stmts_nil (.refl _) =>
            exact ⟨ρ₁, hterm1, hterm2⟩
  have ⟨ρ_mid1, Hs1, Hs2⟩ := extract _ _ _ _ Heval1
  have ⟨ρ_mid2, Hs3, Hs4⟩ := extract _ _ _ _ Heval2
  exact eval_stmt_set_comm Hwf Hneq Hnin1 Hnin2 Hs1 Hs2 Hs3 Hs4

/-! ## `ReflTransT` decomposition helpers

Structural inversion lemmas for multi-step derivations indexed in `Type`
(so step counts can be used by `termination_by`).  Generic over `CmdT`
and the command-evaluation parameter. -/

section ReflTransTHelpers

variable {P : PureExpr} {CmdT : Type}
  [HasBool P] [HasNot P]
  {EvalCmd : EvalCmdParam P CmdT} {extendEval : ExtendEval P}

/-- Invert a `.seq` execution reaching terminal in `ReflTransT`: the inner
    terminates first, then the tail stmts run to terminal.  Length bound
    is strict so callers can recurse on `hstar.len`. -/
theorem seqT_reaches_terminal
    {inner : Config P CmdT} {ss : List (Stmt P CmdT)} {ρ' : Env P}
    (hstar : ReflTransT (StepStmt P EvalCmd extendEval) (.seq inner ss) (.terminal ρ')) :
    ∃ (ρ₁ : Env P), ∃ (h1 : ReflTransT (StepStmt P EvalCmd extendEval) inner (.terminal ρ₁)),
      ∃ (h2 : ReflTransT (StepStmt P EvalCmd extendEval) (.stmts ss ρ₁) (.terminal ρ')),
      h1.len + h2.len < hstar.len := by
  match hstar with
  | .step _ _ _ (.step_seq_inner h) hrest =>
    have ⟨ρ₁, hterm, htail, hlen⟩ := seqT_reaches_terminal hrest
    exact ⟨ρ₁, .step _ _ _ h hterm, htail, by simp [ReflTransT.len]; omega⟩
  | .step _ _ _ .step_seq_done hrest =>
    exact ⟨_, .refl _, hrest, by show 0 + hrest.len < 1 + hrest.len; omega⟩
  | .step _ _ _ .step_seq_exit hrest =>
    match hrest with
    | .step _ _ _ h _ => exact nomatch h

/-- Invert a `.stmts (s :: rest)` execution reaching terminal in `ReflTransT`. -/
theorem stmtsT_cons_terminal
    {s : Stmt P CmdT} {rest : List (Stmt P CmdT)} {ρ₀ ρ' : Env P}
    (hstar : ReflTransT (StepStmt P EvalCmd extendEval) (.stmts (s :: rest) ρ₀) (.terminal ρ')) :
    ∃ (ρ₁ : Env P), ∃ (h1 : ReflTransT (StepStmt P EvalCmd extendEval) (.stmt s ρ₀) (.terminal ρ₁)),
      ∃ (h2 : ReflTransT (StepStmt P EvalCmd extendEval) (.stmts rest ρ₁) (.terminal ρ')),
      h1.len + h2.len + 2 ≤ hstar.len := by
  match hstar with
  | .step _ _ _ .step_stmts_cons hrest =>
    have ⟨ρ₁, h1, h2, hlen⟩ := seqT_reaches_terminal hrest
    exact ⟨ρ₁, h1, h2, by simp [ReflTransT.len]; omega⟩

/-- Invert a block execution reaching terminal when the inner config cannot
    exit: the inner reaches terminal with a strictly shorter derivation. -/
theorem blockT_reaches_terminal_noExit
    {inner : Config P CmdT} {l : Option String} {ρ' : Env P}
    (hstar : ReflTransT (StepStmt P EvalCmd extendEval) (.block l inner) (.terminal ρ'))
    (h_no_exit : ∀ lbl ρ_x,
      ¬ StepStmtStar P EvalCmd extendEval inner (.exiting lbl ρ_x)) :
    ∃ (h : ReflTransT (StepStmt P EvalCmd extendEval) inner (.terminal ρ')),
      h.len < hstar.len := by
  suffices ∀ src tgt (hstar_g : ReflTransT (StepStmt P EvalCmd extendEval) src tgt),
      ∀ inner ρ', src = .block l inner → tgt = .terminal ρ' →
      (∀ lbl ρ_x,
        ¬ StepStmtStar P EvalCmd extendEval inner (.exiting lbl ρ_x)) →
      ∃ (h : ReflTransT (StepStmt P EvalCmd extendEval) inner (.terminal ρ')),
        h.len < hstar_g.len from
    this _ _ hstar _ _ rfl rfl h_no_exit
  intro src tgt hstar_g
  induction hstar_g with
  | refl => intro _ _ hsrc htgt _; subst hsrc; cases htgt
  | step _ mid _ hstep hrest ih =>
    intro inner ρ' hsrc htgt h_ne; subst hsrc
    cases hstep with
    | step_block_body h =>
      have h_ne' : ∀ lbl ρ_x, ¬ StepStmtStar P EvalCmd extendEval _ (.exiting lbl ρ_x) :=
        fun lbl ρ_x hx => h_ne lbl ρ_x (.step _ _ _ h hx)
      have ⟨h_inner, hlen⟩ := ih _ _ rfl htgt h_ne'
      exact ⟨.step _ _ _ h h_inner, by simp [ReflTransT.len]; omega⟩
    | step_block_done =>
      subst htgt
      exact ⟨hrest, by simp [ReflTransT.len]⟩
    | step_block_exit_none =>
      subst htgt
      exact absurd (.refl _) (h_ne _ _)
    | step_block_exit_match =>
      subst htgt
      exact absurd (.refl _) (h_ne _ _)
    | step_block_exit_mismatch =>
      subst htgt
      cases hrest with | step _ _ _ h _ => cases h

/-- Decompose `.stmts (ss₁ ++ [s])` reaching terminal into: a full `.stmts ss₁`
    run to some intermediate `ρ₁` followed by a strictly shorter `s`-run.
    The escape-free hypothesis `hcov` rules out the exiting case. -/
theorem stmtsT_append_terminal
    (ss₁ : List (Stmt P CmdT)) (s : Stmt P CmdT) (ρ₀ ρ' : Env P)
    (hstar : ReflTransT (StepStmt P EvalCmd extendEval) (.stmts (ss₁ ++ [s]) ρ₀) (.terminal ρ'))
    (hcov : Stmt.exitsCoveredByBlocks.Block.exitsCoveredByBlocks (P := P) (CmdT := CmdT) [] ss₁) :
    ∃ (ρ₁ : Env P), ∃ (_ : StepStmtStar P EvalCmd extendEval (.stmts ss₁ ρ₀) (.terminal ρ₁)),
      ∃ (hs : ReflTransT (StepStmt P EvalCmd extendEval) (.stmt s ρ₁) (.terminal ρ')),
      hs.len < hstar.len := by
  induction ss₁ generalizing ρ₀ with
  | nil =>
    have ⟨ρ₁, h1, h2, hlen⟩ := stmtsT_cons_terminal hstar
    have hρ : ρ₁ = ρ' := by
      match h2 with
      | .step _ _ _ .step_stmts_nil (.refl _) => rfl
    subst hρ
    exact ⟨ρ₀, .step _ _ _ .step_stmts_nil (.refl _), h1, by grind⟩
  | cons s' rest' ih =>
    have ⟨ρ₁, h_s', h_rest, hlen₁⟩ := stmtsT_cons_terminal hstar
    have ⟨ρ₂, h_rest', h_s, hlen₂⟩ := ih ρ₁ h_rest hcov.2
    exact ⟨ρ₂,
      ReflTrans_Transitive _ _ _ _
        (stmts_cons_step P EvalCmd extendEval s' rest' ρ₀ ρ₁ (reflTransT_to_prop h_s'))
        h_rest',
      h_s, by grind⟩

/-! ## Failing-state decomposition helpers -/

/-- Decompose a `.seq` execution reaching a failing config in `ReflTransT`:
    either failure happens inside `inner`, or `inner` terminates and
    failure happens in the tail. -/
theorem seqT_canfail
    {inner : Config P CmdT} {ss : List (Stmt P CmdT)} {cfg : Config P CmdT}
    (hstar : ReflTransT (StepStmt P EvalCmd extendEval) (.seq inner ss) cfg)
    (hf : cfg.getEnv.hasFailure = true) :
    (∃ (cfg' : Config P CmdT),
      ∃ (h : ReflTransT (StepStmt P EvalCmd extendEval) inner cfg'),
        cfg'.getEnv.hasFailure = true ∧ h.len ≤ hstar.len) ∨
    (∃ (ρ₁ : Env P),
      ∃ (h1 : ReflTransT (StepStmt P EvalCmd extendEval) inner (.terminal ρ₁)),
      ∃ (h2 : ReflTransT (StepStmt P EvalCmd extendEval) (.stmts ss ρ₁) cfg),
        h1.len + h2.len < hstar.len) := by
  match hstar with
  | .refl _ => exact .inl ⟨inner, .refl _, hf, Nat.le_refl _⟩
  | .step _ _ _ (.step_seq_inner h) hrest =>
    match seqT_canfail hrest hf with
    | .inl ⟨cfg', h_inner, hf', _⟩ =>
      exact .inl ⟨cfg', .step _ _ _ h h_inner, hf', by simp [ReflTransT.len]; omega⟩
    | .inr ⟨ρ₁, h1, h2, _⟩ =>
      exact .inr ⟨ρ₁, .step _ _ _ h h1, h2, by simp [ReflTransT.len]; omega⟩
  | .step _ _ _ .step_seq_done hrest =>
    exact .inr ⟨_, .refl _, hrest, by simp [ReflTransT.len]⟩
  | .step _ _ _ .step_seq_exit hrest =>
    match hrest with
    | .refl _ => exact .inl ⟨_, .refl _, hf, by simp [ReflTransT.len]⟩
    | .step _ _ _ h _ => exact nomatch h

/-- An empty-statement-list run that reaches a failing config must already
    have been failing. -/
theorem stmts_nil_canfail_env
    {ρ : Env P} {cfg : Config P CmdT}
    (hstar : StepStmtStar P EvalCmd extendEval
      (.stmts ([] : List (Stmt P CmdT)) ρ) cfg)
    (hf : cfg.getEnv.hasFailure = true) :
    ρ.hasFailure = true := by
  cases hstar with
  | refl => exact hf
  | step _ _ _ h1 r1 => cases h1 with
    | step_stmts_nil => cases r1 with
      | refl => exact hf
      | step _ _ _ h _ => cases h

/-- Decompose `.stmts (ss₁ ++ [s])` reaching a failing config: either
    failure happens before reaching `s`, or `ss₁` terminates at `ρ₁` and
    the failure happens in `s`. -/
theorem stmtsT_append_canfail
    (ss₁ : List (Stmt P CmdT)) (s : Stmt P CmdT) (ρ₀ : Env P)
    {cfg : Config P CmdT}
    (hstar : ReflTransT (StepStmt P EvalCmd extendEval)
      (.stmts (ss₁ ++ [s]) ρ₀) cfg)
    (hf : cfg.getEnv.hasFailure = true) :
    (∃ cfg', cfg'.getEnv.hasFailure = true ∧
      StepStmtStar P EvalCmd extendEval (.stmts ss₁ ρ₀) cfg') ∨
    (∃ (ρ₁ : Env P),
      StepStmtStar P EvalCmd extendEval (.stmts ss₁ ρ₀) (.terminal ρ₁) ∧
      ∃ (cfg₂ : Config P CmdT),
      ∃ (hs : ReflTransT (StepStmt P EvalCmd extendEval) (.stmt s ρ₁) cfg₂),
        cfg₂.getEnv.hasFailure = true ∧ hs.len < hstar.len) := by
  induction ss₁ generalizing ρ₀ with
  | nil =>
    match hstar with
    | .refl _ =>
      exact .inl ⟨.stmts [] ρ₀, hf, .refl _⟩
    | .step _ _ _ .step_stmts_cons hrest =>
      match seqT_canfail hrest hf with
      | .inl ⟨cfg', h, hf', _⟩ =>
        exact .inr ⟨ρ₀, .step _ _ _ .step_stmts_nil (.refl _), cfg', h, hf',
          by simp [ReflTransT.len]; omega⟩
      | .inr ⟨ρ₁, h1, h2, _⟩ =>
        exact .inr ⟨ρ₀, .step _ _ _ .step_stmts_nil (.refl _), .terminal ρ₁, h1,
          stmts_nil_canfail_env (reflTransT_to_prop h2) hf,
          by simp [ReflTransT.len]; omega⟩
  | cons s' rest' ih =>
    match hstar with
    | .refl _ =>
      exact .inl ⟨.stmts (s' :: rest') ρ₀, hf, .refl _⟩
    | .step _ _ _ .step_stmts_cons hrest =>
      match seqT_canfail hrest hf with
      | .inl ⟨cfg', h, hf', _⟩ =>
        exact .inl ⟨.seq cfg' rest', hf',
          .step _ _ _ .step_stmts_cons
            (seq_inner_star P EvalCmd extendEval _ cfg' rest' (reflTransT_to_prop h))⟩
      | .inr ⟨ρ₁, h1, h2, _⟩ =>
        have hpre := stmts_cons_step P EvalCmd extendEval s' rest' ρ₀ ρ₁
          (reflTransT_to_prop h1)
        match ih ρ₁ h2 with
        | .inl ⟨cfg'_rest, hf'_rest, hstar_rest⟩ =>
          exact .inl ⟨cfg'_rest, hf'_rest,
            ReflTrans_Transitive _ _ _ _ hpre hstar_rest⟩
        | .inr ⟨ρ₂, hterm_rest, cfg₂, hs, hf₂, _⟩ =>
          exact .inr ⟨ρ₂, ReflTrans_Transitive _ _ _ _ hpre hterm_rest,
            cfg₂, hs, hf₂, by simp [ReflTransT.len]; omega⟩

/-- Unwrap a failing `.block l inner` execution to a failing run on `inner`. -/
theorem block_canfail_to_inner
    {inner : Config P CmdT} {l : Option String} {cfg : Config P CmdT}
    (hstar : StepStmtStar P EvalCmd extendEval (.block l inner) cfg)
    (hf : cfg.getEnv.hasFailure = true) :
    ∃ inner', inner'.getEnv.hasFailure = true ∧
      StepStmtStar P EvalCmd extendEval inner inner' := by
  suffices ∀ src tgt, StepStmtStar P EvalCmd extendEval src tgt →
      ∀ (inner : Config P CmdT), src = .block l inner →
      tgt.getEnv.hasFailure = true →
      ∃ inner', inner'.getEnv.hasFailure = true ∧
        StepStmtStar P EvalCmd extendEval inner inner' from
    this _ _ hstar _ rfl hf
  intro src tgt hstar_g
  induction hstar_g with
  | refl =>
    intro inner hsrc hf; subst hsrc; exact ⟨inner, hf, .refl _⟩
  | step _ mid _ hstep hrest ih =>
    intro inner hsrc hf; subst hsrc
    match hstep with
    | .step_block_body h =>
      have ⟨inner', hf', hstar'⟩ := ih _ rfl hf
      exact ⟨inner', hf', .step _ _ _ h hstar'⟩
    | .step_block_done | .step_block_exit_none
    | .step_block_exit_match _ | .step_block_exit_mismatch _ =>
      match hrest with
      | .refl _ => refine ⟨_, ?_, .refl _⟩; exact hf
      | .step _ _ _ h _ => exact nomatch h

/-- Type-level variant of `block_canfail_to_inner` preserving length bounds
    on the inner derivation.  Required when the inner derivation must
    decrease for a recursive call. -/
theorem blockT_canfail_to_inner
    {inner : Config P CmdT} {l : Option String} {cfg : Config P CmdT}
    (hstar : ReflTransT (StepStmt P EvalCmd extendEval) (.block l inner) cfg)
    (hf : cfg.getEnv.hasFailure = true) :
    ∃ (inner' : Config P CmdT),
      ∃ (h : ReflTransT (StepStmt P EvalCmd extendEval) inner inner'),
        inner'.getEnv.hasFailure = true ∧ h.len ≤ hstar.len := by
  match hstar with
  | .refl _ => exact ⟨inner, .refl _, hf, Nat.le_refl _⟩
  | .step _ _ _ (.step_block_body h) hrest =>
    have ⟨inner', h_inner', hf', hlen⟩ := blockT_canfail_to_inner hrest hf
    exact ⟨inner', .step _ _ _ h h_inner', hf',
      by simp [ReflTransT.len]; omega⟩
  | .step _ _ _ .step_block_done hrest =>
    match hrest with
    | .refl _ =>
      exact ⟨.terminal _, .refl _, hf, by simp [ReflTransT.len]⟩
    | .step _ _ _ h _ => exact nomatch h
  | .step _ _ _ .step_block_exit_none hrest =>
    match hrest with
    | .refl _ =>
      exact ⟨.exiting .none _, .refl _, hf, by simp [ReflTransT.len]⟩
    | .step _ _ _ h _ => exact nomatch h
  | .step _ _ _ (.step_block_exit_match _) hrest =>
    match hrest with
    | .refl _ =>
      exact ⟨.exiting (.some _) _, .refl _, hf, by simp [ReflTransT.len]⟩
    | .step _ _ _ h _ => exact nomatch h
  | .step _ _ _ (.step_block_exit_mismatch _) hrest =>
    match hrest with
    | .refl _ =>
      exact ⟨.exiting _ _, .refl _, hf, by simp [ReflTransT.len]⟩
    | .step _ _ _ h _ => exact nomatch h
  termination_by hstar.len
  decreasing_by all_goals (simp_wf; try simp [ReflTransT.len]; try omega)

/-- Prop-level seq-canfail decomposition (without length bounds). -/
theorem seq_canfail_prop
    {inner : Config P CmdT} {ss : List (Stmt P CmdT)} {cfg : Config P CmdT}
    (hstar : StepStmtStar P EvalCmd extendEval (.seq inner ss) cfg)
    (hf : cfg.getEnv.hasFailure = true) :
    (∃ cfg', cfg'.getEnv.hasFailure = true ∧
      StepStmtStar P EvalCmd extendEval inner cfg') ∨
    (∃ ρ₁, StepStmtStar P EvalCmd extendEval inner (.terminal ρ₁) ∧
      ∃ cfg', cfg'.getEnv.hasFailure = true ∧
        StepStmtStar P EvalCmd extendEval (.stmts ss ρ₁) cfg') :=
  match seqT_canfail (reflTrans_to_T hstar) hf with
  | .inl ⟨cfg', h, hf', _⟩ => .inl ⟨cfg', hf', reflTransT_to_prop h⟩
  | .inr ⟨ρ₁, h1, h2, _⟩ => .inr ⟨ρ₁, reflTransT_to_prop h1, _, hf, reflTransT_to_prop h2⟩

end ReflTransTHelpers

end -- public section
