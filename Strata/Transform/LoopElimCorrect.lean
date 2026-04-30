/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Transform.LoopElim
public import Strata.Transform.CoreSpecification
public import Strata.Transform.Specification
public import Strata.DL.Imperative.StmtSemantics
public import Strata.DL.Imperative.SemanticsProps
public import Strata.DL.Util.Relations
import all Strata.Transform.LoopElim
import all Strata.Transform.Specification
import all Strata.Transform.CoreSpecification
import all Strata.DL.Imperative.StmtSemantics
import all Strata.DL.Imperative.SemanticsProps
import all Strata.DL.Util.Relations

/-! # Loop-Elimination Transformation Correctness

The top-level theorem is `loopElim_overapproximatesAggressive`: the
loop-eliminated program aggressively overapproximates the original.

For each source execution reaching terminal `ρ'`, the transformed program
either reaches the same terminal `ρ'` (exact simulation), or terminates at
some `ρ''` with `hasFailure = true` (an invariant VC failed).

Unlike earlier formulations, this proof does *not* require a `loopInvsBool`
precondition on the source statement: the small-step loop semantics in this
repo already propagates invariant failures into `hasFailure` on the source
side, so source and target agree on invariant-failure behaviour.
-/

public section

namespace Core.LoopElim

open Imperative Specification Core Imperative.LoopElim

variable (π : String → Option Procedure)
variable (φ : CoreEval → PureFunc Expression → CoreEval)

abbrev LangCore := Core.Specification.Lang.core π φ
abbrev CoreStar := StepStmtStar Expression (EvalCommand π φ) (EvalPureFunc φ)
abbrev CC := Config Expression Command

/-! ## Projecting removeLoopsM results -/

noncomputable def stmtResult (σ : LoopElimState) (s : Statement) : Statement :=
  (StateT.run (Stmt.removeLoopsM s) σ).fst.snd

noncomputable def blockResult (σ : LoopElimState) (ss : Statements) : Statements :=
  (StateT.run (Block.removeLoopsM ss) σ).fst.snd

noncomputable def stmtPostState (σ : LoopElimState) (s : Statement) : LoopElimState :=
  (StateT.run (Stmt.removeLoopsM s) σ).snd

noncomputable def blockPostState (σ : LoopElimState) (ss : Statements) : LoopElimState :=
  (StateT.run (Block.removeLoopsM ss) σ).snd

/-! ## CanFail for statement lists (block bodies) -/

private def CanFailBlock (ss : Statements) (ρ₀ : Env Expression) : Prop :=
  ∃ cfg : CC, cfg.getEnv.hasFailure = Bool.true ∧ CoreStar π φ (.stmts ss ρ₀) cfg

/-! ## Identity lemmas -/

private theorem stmtResult_cmd (σ : LoopElimState) (c : Command) :
    stmtResult σ (.cmd c) = .cmd c := by
  simp [stmtResult, Stmt.removeLoopsM, StateT.run, pure, StateT.pure]

private theorem stmtResult_exit (σ : LoopElimState) (l : Option String)
    (md : MetaData Expression) :
    stmtResult σ (.exit l md) = .exit l md := by
  simp [stmtResult, Stmt.removeLoopsM, StateT.run, pure, StateT.pure]

private theorem stmtResult_funcDecl (σ : LoopElimState) (d : PureFunc Expression)
    (md : MetaData Expression) :
    stmtResult σ (.funcDecl d md) = .funcDecl d md := by
  simp [stmtResult, Stmt.removeLoopsM, StateT.run, pure, StateT.pure]

private theorem stmtResult_typeDecl (σ : LoopElimState) (tc : TypeConstructor)
    (md : MetaData Expression) :
    stmtResult σ (.typeDecl tc md) = .typeDecl tc md := by
  simp [stmtResult, Stmt.removeLoopsM, StateT.run, pure, StateT.pure]

private theorem stmtResult_block (σ : LoopElimState) (l : String)
    (bss : Statements) (md : MetaData Expression) :
    stmtResult σ (.block l bss md) = .block l (blockResult σ bss) md := by
  simp only [stmtResult, blockResult, Stmt.removeLoopsM, StateT.run, bind, StateT.bind]
  generalize Block.removeLoopsM bss σ = p
  cases p with
  | mk fst snd => simp [pure, StateT.pure]

private theorem stmtResult_ite (σ : LoopElimState) (c : ExprOrNondet Expression)
    (tss ess : Statements) (md : MetaData Expression) :
    stmtResult σ (.ite c tss ess md) =
      .ite c (blockResult σ tss) (blockResult (blockPostState σ tss) ess) md := by
  simp only [stmtResult, blockResult, blockPostState, Stmt.removeLoopsM, StateT.run, bind,
    StateT.bind]
  generalize Block.removeLoopsM tss σ = p1
  cases p1 with
  | mk fst snd =>
    simp [pure, StateT.pure]
    generalize Block.removeLoopsM ess snd = p2
    cases p2 with
    | mk fst' snd' => simp

private theorem blockResult_nil (σ : LoopElimState) :
    blockResult σ [] = [] := by
  simp [blockResult, Block.removeLoopsM, StateT.run, pure, StateT.pure]

private theorem blockResult_cons (σ : LoopElimState) (s : Statement)
    (ss : Statements) :
    blockResult σ (s :: ss) =
      stmtResult σ s :: blockResult (stmtPostState σ s) ss := by
  simp only [blockResult, stmtResult, stmtPostState, Block.removeLoopsM, StateT.run, bind,
    StateT.bind]
  generalize Stmt.removeLoopsM s σ = p1
  cases p1 with
  | mk fst snd =>
    simp [pure, StateT.pure]
    generalize Block.removeLoopsM ss snd = p2
    cases p2 with
    | mk fst' snd' => simp

/-! ## WF preservation -/

private theorem onestep_preserves_wf
    (hwf_ext : WFEvalExtension φ)
    {c₁ c₂ : CC}
    (hstep : StepStmt Expression (EvalCommand π φ) (EvalPureFunc φ) c₁ c₂)
    (hwfb : WellFormedSemanticEvalBool c₁.getEnv.eval) :
    WellFormedSemanticEvalBool c₂.getEnv.eval := by
  suffices ∀ (a b : CC),
      StepStmt Expression (EvalCommand π φ) (EvalPureFunc φ) a b →
      WellFormedSemanticEvalBool a.getEnv.eval →
      WellFormedSemanticEvalBool b.getEnv.eval from
    this c₁ c₂ hstep hwfb
  intro a b hstep
  induction hstep with
  | step_cmd _ => intro h; simp [Config.getEnv]; exact h
  | step_block => intro h; exact h
  | step_ite_true => intro h; exact h
  | step_ite_false => intro h; exact h
  | step_ite_nondet_true => intro h; exact h
  | step_ite_nondet_false => intro h; exact h
  | step_loop_enter => intro h; exact h
  | step_loop_exit => intro h; exact h
  | step_loop_nondet_enter => intro h; exact h
  | step_loop_nondet_exit => intro h; exact h
  | step_exit => intro h; exact h
  | step_funcDecl =>
    intro h; simp [Config.getEnv]
    exact hwf_ext.preserves_wfBool _ _ _ h
  | step_typeDecl => intro h; exact h
  | step_stmts_nil => intro h; exact h
  | step_stmts_cons => intro h; exact h
  | step_seq_inner _ ih => intro h; exact ih h
  | step_seq_done => intro h; exact h
  | step_seq_exit => intro h; exact h
  | step_block_body _ ih => intro h; exact ih h
  | step_block_done => intro h; exact h
  | step_block_exit_none => intro h; exact h
  | step_block_exit_match => intro h; exact h
  | step_block_exit_mismatch => intro h; exact h

private theorem star_preserves_wf
    (hwf_ext : WFEvalExtension φ)
    {c₁ c₂ : CC}
    (hstar : CoreStar π φ c₁ c₂)
    (hwfb : WellFormedSemanticEvalBool c₁.getEnv.eval) :
    WellFormedSemanticEvalBool c₂.getEnv.eval := by
  induction hstar with
  | refl => exact hwfb
  | step _ _ _ hstep _ ih =>
    exact ih (onestep_preserves_wf (π := π) (φ := φ) hwf_ext hstep hwfb)

private theorem star_preserves_wfVal
    (hwf_ext : WFEvalExtension φ)
    {c₁ c₂ : CC}
    (hstar : CoreStar π φ c₁ c₂)
    (hwfv : WellFormedSemanticEvalVal c₁.getEnv.eval) :
    WellFormedSemanticEvalVal c₂.getEnv.eval := by
  suffices ∀ (a b : CC),
      StepStmt Expression (EvalCommand π φ) (EvalPureFunc φ) a b →
      WellFormedSemanticEvalVal a.getEnv.eval →
      WellFormedSemanticEvalVal b.getEnv.eval by
    induction hstar with
    | refl => exact hwfv
    | step _ _ _ hstep _ ih => exact ih (this _ _ hstep hwfv)
  intro a b hstep
  induction hstep with
  | step_cmd _ => intro h; simp [Config.getEnv]; exact h
  | step_block => intro h; exact h
  | step_ite_true => intro h; exact h
  | step_ite_false => intro h; exact h
  | step_ite_nondet_true => intro h; exact h
  | step_ite_nondet_false => intro h; exact h
  | step_loop_enter => intro h; exact h
  | step_loop_exit => intro h; exact h
  | step_loop_nondet_enter => intro h; exact h
  | step_loop_nondet_exit => intro h; exact h
  | step_exit => intro h; exact h
  | step_funcDecl => intro h; simp [Config.getEnv]; exact hwf_ext.preserves_wfVal _ _ _ h
  | step_typeDecl => intro h; exact h
  | step_stmts_nil => intro h; exact h
  | step_stmts_cons => intro h; exact h
  | step_seq_inner _ ih => intro h; exact ih h
  | step_seq_done => intro h; exact h
  | step_seq_exit => intro h; exact h
  | step_block_body _ ih => intro h; exact ih h
  | step_block_done => intro h; exact h
  | step_block_exit_none => intro h; exact h
  | step_block_exit_match => intro h; exact h
  | step_block_exit_mismatch => intro h; exact h

private theorem star_preserves_wfVar
    (hwf_ext : WFEvalExtension φ)
    {c₁ c₂ : CC}
    (hstar : CoreStar π φ c₁ c₂)
    (hwfvar : WellFormedSemanticEvalVar c₁.getEnv.eval) :
    WellFormedSemanticEvalVar c₂.getEnv.eval := by
  suffices ∀ (a b : CC),
      StepStmt Expression (EvalCommand π φ) (EvalPureFunc φ) a b →
      WellFormedSemanticEvalVar a.getEnv.eval →
      WellFormedSemanticEvalVar b.getEnv.eval by
    induction hstar with
    | refl => exact hwfvar
    | step _ _ _ hstep _ ih => exact ih (this _ _ hstep hwfvar)
  intro a b hstep
  induction hstep with
  | step_cmd _ => intro h; simp [Config.getEnv]; exact h
  | step_block => intro h; exact h
  | step_ite_true => intro h; exact h
  | step_ite_false => intro h; exact h
  | step_ite_nondet_true => intro h; exact h
  | step_ite_nondet_false => intro h; exact h
  | step_loop_enter => intro h; exact h
  | step_loop_exit => intro h; exact h
  | step_loop_nondet_enter => intro h; exact h
  | step_loop_nondet_exit => intro h; exact h
  | step_exit => intro h; exact h
  | step_funcDecl => intro h; simp [Config.getEnv]; exact hwf_ext.preserves_wfVar _ _ _ h
  | step_typeDecl => intro h; exact h
  | step_stmts_nil => intro h; exact h
  | step_stmts_cons => intro h; exact h
  | step_seq_inner _ ih => intro h; exact ih h
  | step_seq_done => intro h; exact h
  | step_seq_exit => intro h; exact h
  | step_block_body _ ih => intro h; exact ih h
  | step_block_done => intro h; exact h
  | step_block_exit_none => intro h; exact h
  | step_block_exit_match => intro h; exact h
  | step_block_exit_mismatch => intro h; exact h

private theorem hasFailure_false_backwards
    {c₁ c₂ : CC}
    (hstar : CoreStar π φ c₁ c₂)
    (hnf : c₂.getEnv.hasFailure = Bool.false) :
    c₁.getEnv.hasFailure = Bool.false := by
  cases h : c₁.getEnv.hasFailure
  · rfl
  · exact absurd (StepStmtStar_hasFailure_monotone hstar h) (by simp [hnf])

/-! ## Lifting lemmas for CanFail -/

private theorem canFail_head_to_block
    (s : Statement) (ss : Statements) (ρ₀ : Env Expression)
    (h : Transform.CanFail (LangCore π φ) s ρ₀) :
    CanFailBlock π φ (s :: ss) ρ₀ := by
  obtain ⟨cfg, hfail, hreach⟩ := h
  refine ⟨.seq cfg ss, ?_, ?_⟩
  · simp [Config.getEnv]; exact hfail
  · exact ReflTrans_Transitive _ _ _ _
      (.step _ _ _ .step_stmts_cons (.refl _))
      (seq_inner_star Expression (EvalCommand π φ) (EvalPureFunc φ) _ _ ss hreach)

private theorem canFail_tail_to_block
    (s : Statement) (ss : Statements) (ρ₀ ρ₁ : Env Expression)
    (hhead : CoreStar π φ (.stmt s ρ₀) (.terminal ρ₁))
    (htail : CanFailBlock π φ ss ρ₁) :
    CanFailBlock π φ (s :: ss) ρ₀ := by
  obtain ⟨cfg, hfail, hreach⟩ := htail
  exact ⟨cfg, hfail,
    ReflTrans_Transitive _ _ _ _
      (stmts_cons_step Expression (EvalCommand π φ) (EvalPureFunc φ) s ss ρ₀ ρ₁ hhead)
      hreach⟩

private theorem block_wrap_terminal
    (l : String) (bss : Statements) (md : MetaData Expression)
    (ρ₀ ρ' : Env Expression)
    (h : CoreStar π φ (.stmts bss ρ₀) (.terminal ρ')) :
    CoreStar π φ (.stmt (.block l bss md) ρ₀) (.terminal ρ') :=
  ReflTrans_Transitive _ _ _ _
    (step_block_enter Expression (EvalCommand π φ) (EvalPureFunc φ) l bss md ρ₀)
    (ReflTrans_Transitive _ _ _ _
      (block_inner_star Expression (EvalCommand π φ) (EvalPureFunc φ) _ _ (some l) h)
      (.step _ _ _ .step_block_done (.refl _)))

private theorem block_wrap_exiting_mismatch
    (l : String) (bss : Statements) (md : MetaData Expression)
    (lv : String) (ρ₀ ρ' : Env Expression)
    (hne : lv ≠ l)
    (h : CoreStar π φ (.stmts bss ρ₀) (.exiting (some lv) ρ')) :
    CoreStar π φ (.stmt (.block l bss md) ρ₀) (.exiting (some lv) ρ') :=
  ReflTrans_Transitive _ _ _ _
    (step_block_enter Expression (EvalCommand π φ) (EvalPureFunc φ) l bss md ρ₀)
    (ReflTrans_Transitive _ _ _ _
      (block_inner_star Expression (EvalCommand π φ) (EvalPureFunc φ) _ _ (some l) h)
      (.step _ _ _ (.step_block_exit_mismatch (fun h => hne (Option.some.inj h).symm)) (.refl _)))

private theorem block_wrap_exiting_none
    (l : String) (bss : Statements) (md : MetaData Expression)
    (ρ₀ ρ' : Env Expression)
    (h : CoreStar π φ (.stmts bss ρ₀) (.exiting none ρ')) :
    CoreStar π φ (.stmt (.block l bss md) ρ₀) (.terminal ρ') :=
  ReflTrans_Transitive _ _ _ _
    (step_block_enter Expression (EvalCommand π φ) (EvalPureFunc φ) l bss md ρ₀)
    (ReflTrans_Transitive _ _ _ _
      (block_inner_star Expression (EvalCommand π φ) (EvalPureFunc φ) _ _ (some l) h)
      (.step _ _ _ .step_block_exit_none (.refl _)))

private theorem block_wrap_exiting_match
    (l : String) (bss : Statements) (md : MetaData Expression)
    (ρ₀ ρ' : Env Expression)
    (h : CoreStar π φ (.stmts bss ρ₀) (.exiting (some l) ρ')) :
    CoreStar π φ (.stmt (.block l bss md) ρ₀) (.terminal ρ') :=
  ReflTrans_Transitive _ _ _ _
    (step_block_enter Expression (EvalCommand π φ) (EvalPureFunc φ) l bss md ρ₀)
    (ReflTrans_Transitive _ _ _ _
      (block_inner_star Expression (EvalCommand π φ) (EvalPureFunc φ) _ _ (some l) h)
      (.step _ _ _ (.step_block_exit_match rfl) (.refl _)))

private theorem block_reaches_terminal_refined
    {inner : CC} {l : String} {ρ' : Env Expression}
    (hstar : CoreStar π φ (.block (some l) inner) (.terminal ρ')) :
    CoreStar π φ inner (.terminal ρ') ∨
    CoreStar π φ inner (.exiting none ρ') ∨
    CoreStar π φ inner (.exiting (some l) ρ') := by
  suffices ∀ src tgt, CoreStar π φ src tgt →
      ∀ inner ρ', src = .block (some l) inner → tgt = .terminal ρ' →
      CoreStar π φ inner (.terminal ρ') ∨
      CoreStar π φ inner (.exiting none ρ') ∨
      CoreStar π φ inner (.exiting (some l) ρ') from
    this _ _ hstar _ _ rfl rfl
  intro src tgt hstar_g
  induction hstar_g with
  | refl => intro _ _ hsrc htgt; subst hsrc; cases htgt
  | step _ mid _ hstep hrest ih =>
    intro inner ρ' hsrc htgt; subst hsrc
    cases hstep with
    | step_block_body h =>
      match ih _ _ rfl htgt with
      | .inl hterm => exact .inl (.step _ _ _ h hterm)
      | .inr (.inl hexit) => exact .inr (.inl (.step _ _ _ h hexit))
      | .inr (.inr hexit) => exact .inr (.inr (.step _ _ _ h hexit))
    | step_block_done => subst htgt; exact .inl hrest
    | step_block_exit_none =>
      subst htgt; cases hrest with
      | refl => exact .inr (.inl (.refl _))
      | step _ _ _ h _ => cases h
    | step_block_exit_match heq =>
      subst htgt; cases heq; cases hrest with
      | refl => exact .inr (.inr (.refl _))
      | step _ _ _ h _ => cases h
    | step_block_exit_mismatch =>
      subst htgt; cases hrest with | step _ _ _ h _ => cases h

private theorem block_reaches_exiting_refined
    {inner : CC} {l : String} {lbl : Option String} {ρ' : Env Expression}
    (hstar : CoreStar π φ (.block (some l) inner) (.exiting lbl ρ')) :
    ∃ lv : String, lv ≠ l ∧ lbl = some lv ∧
      CoreStar π φ inner (.exiting (some lv) ρ') := by
  suffices ∀ src tgt, CoreStar π φ src tgt →
      ∀ inner lbl ρ', src = .block (some l) inner → tgt = .exiting lbl ρ' →
      ∃ lv : String, lv ≠ l ∧ lbl = some lv ∧
        CoreStar π φ inner (.exiting (some lv) ρ') from
    this _ _ hstar _ _ _ rfl rfl
  intro src tgt hstar_g
  induction hstar_g with
  | refl => intro _ _ _ hsrc htgt; subst hsrc; cases htgt
  | step _ mid _ hstep hrest ih =>
    intro inner lbl ρ' hsrc htgt; subst hsrc
    cases hstep with
    | step_block_body h =>
      have ⟨lv, hne, heq, hexit⟩ := ih _ _ _ rfl htgt
      exact ⟨lv, hne, heq, .step _ _ _ h hexit⟩
    | step_block_done =>
      subst htgt; cases hrest with | step _ _ _ h _ => cases h
    | step_block_exit_none =>
      subst htgt; cases hrest with | step _ _ _ h _ => cases h
    | step_block_exit_match =>
      subst htgt; cases hrest with | step _ _ _ h _ => cases h
    | step_block_exit_mismatch hne =>
      subst htgt
      cases hrest with
      | refl => exact ⟨_, fun heq => hne (congrArg Option.some heq.symm), rfl, .refl _⟩
      | step _ _ _ h _ => cases h

private theorem canFailBlock_to_canFail_block
    (l : String) (bss : Statements) (md : MetaData Expression) (ρ₀ : Env Expression)
    (h : CanFailBlock π φ bss ρ₀) :
    Transform.CanFail (LangCore π φ) (.block l bss md) ρ₀ := by
  obtain ⟨cfg, hfail, hreach⟩ := h
  exact ⟨.block (.some l) cfg, by show cfg.getEnv.hasFailure = Bool.true; exact hfail,
    ReflTrans_Transitive _ _ _ _
      (step_block_enter Expression (EvalCommand π φ) (EvalPureFunc φ) l bss md ρ₀)
      (block_inner_star Expression (EvalCommand π φ) (EvalPureFunc φ) _ _ (.some l) hreach)⟩

private theorem stmts_cons_exiting
    (s : Statement) (ss : Statements) (lbl : Option String)
    (ρ₀ ρ' : Env Expression)
    (h : CoreStar π φ (.stmt s ρ₀) (.exiting lbl ρ')) :
    CoreStar π φ (.stmts (s :: ss) ρ₀) (.exiting lbl ρ') :=
  ReflTrans_Transitive _ _ _ _
    (.step _ _ _ .step_stmts_cons (.refl _))
    (ReflTrans_Transitive _ _ _ _
      (seq_inner_star Expression (EvalCommand π φ) (EvalPureFunc φ) _ _ ss h)
      (.step _ _ _ .step_seq_exit (.refl _)))

/-! ## Loop-specific helpers -/

/-- When the source loop terminal has `hasFailure = false`, the loop step's
    `hasInvFailure` is `false`. -/
private theorem loop_step_hasInvFailure_false_of_or
    {ρ : Env Expression} {hasInvFailure : Bool}
    (hresult_nf : (ρ.hasFailure || hasInvFailure) = Bool.false) :
    hasInvFailure = Bool.false := by
  cases hasInvFailure with
  | false => rfl
  | true => simp [Bool.or_true] at hresult_nf

/-- When `hasInvFailure = false`, all invariant expressions evaluate to `tt`. -/
private theorem all_inv_tt_of_hasInvFailure_false
    {inv : List (String × Expression.Expr)} {ρ : Env Expression}
    {hasInvFailure : Bool}
    (hinv_eval : ∀ le ∈ inv, ρ.eval ρ.store le.2 = .some HasBool.tt ∨
                              ρ.eval ρ.store le.2 = .some HasBool.ff)
    (hff_iff : hasInvFailure = Bool.true ↔ ∃ le ∈ inv, ρ.eval ρ.store le.2 = .some HasBool.ff)
    (hnif : hasInvFailure = Bool.false) :
    ∀ le ∈ inv, ρ.eval ρ.store le.2 = .some HasBool.tt := by
  intro le hle
  cases hinv_eval le hle with
  | inl htt => exact htt
  | inr hff =>
    exfalso
    have : hasInvFailure = Bool.true := hff_iff.mpr ⟨le, hle, hff⟩
    rw [hnif] at this; exact Bool.noConfusion this

/-- The env update `{ρ with hasFailure := ρ.hasFailure || false}` is the identity. -/
private theorem env_or_false_eq (ρ : Env Expression) :
    ({ ρ with hasFailure := ρ.hasFailure || Bool.false } : Env Expression) = ρ := by
  cases ρ; simp [Bool.or_false]

/-- Single assert step: assert passes when expr is tt. -/
private theorem assert_pass_step
    (l : String) (e : Expression.Expr) (md : MetaData Expression)
    (ρ : Env Expression) (htt : ρ.eval ρ.store e = .some HasBool.tt)
    (hwfb : WellFormedSemanticEvalBool ρ.eval) :
    CoreStar π φ (.stmt (.cmd (HasPassiveCmds.assert l e md)) ρ) (.terminal ρ) := by
  have h : CoreStar π φ (.stmt (.cmd (HasPassiveCmds.assert l e md)) ρ)
      (.terminal { ρ with store := ρ.store, hasFailure := ρ.hasFailure || Bool.false }) :=
    .step _ _ _ (.step_cmd (EvalCommand.cmd_sem (.eval_assert_pass htt hwfb))) (.refl _)
  rwa [env_or_false_eq] at h

/-- Single assume step: assume passes when expr is tt. -/
private theorem assume_pass_step
    (l : String) (e : Expression.Expr) (md : MetaData Expression)
    (ρ : Env Expression) (htt : ρ.eval ρ.store e = .some HasBool.tt)
    (hwfb : WellFormedSemanticEvalBool ρ.eval) :
    CoreStar π φ (.stmt (.cmd (HasPassiveCmds.assume l e md)) ρ) (.terminal ρ) := by
  have h : CoreStar π φ (.stmt (.cmd (HasPassiveCmds.assume l e md)) ρ)
      (.terminal { ρ with store := ρ.store, hasFailure := ρ.hasFailure || Bool.false }) :=
    .step _ _ _ (.step_cmd (EvalCommand.cmd_sem (.eval_assume htt hwfb))) (.refl _)
  rwa [env_or_false_eq] at h

/-- Execute a list of passive assert/assume statements that all pass. -/
private theorem stmts_passive_all_pass
    (ss : Statements) (ρ : Env Expression)
    (hwfb : WellFormedSemanticEvalBool ρ.eval)
    (hall : ∀ s ∈ ss, CoreStar π φ (.stmt s ρ) (.terminal ρ)) :
    CoreStar π φ (.stmts ss ρ) (.terminal ρ) := by
  induction ss with
  | nil => exact .step _ _ _ .step_stmts_nil (.refl _)
  | cons hd tl ih =>
    exact ReflTrans_Transitive _ _ _ _
      (stmts_cons_step Expression (EvalCommand π φ) (EvalPureFunc φ) _ _ ρ ρ (hall hd (.head ..)))
      (ih (fun s hs => hall s (.tail _ hs)))

/-- The mapIdx assert list terminates when all invariants are `tt`. -/
private theorem stmts_mapIdx_assert_terminal
    (inv : List (String × Expression.Expr)) (ρ : Env Expression)
    (md : MetaData Expression) (mkLabel : Nat → String → String)
    (hwfb : WellFormedSemanticEvalBool ρ.eval)
    (hall : ∀ le ∈ inv, ρ.eval ρ.store le.2 = .some HasBool.tt) :
    CoreStar π φ
      (.stmts (inv.mapIdx fun i le =>
        Stmt.cmd (HasPassiveCmds.assert (mkLabel i le.1) le.2 md)) ρ)
      (.terminal ρ) := by
  apply stmts_passive_all_pass π φ _ ρ hwfb
  intro s hs; rw [List.mem_mapIdx] at hs
  obtain ⟨i, hi, rfl⟩ := hs
  exact assert_pass_step π φ _ _ md ρ (hall _ (List.getElem_mem hi)) hwfb

/-- The mapIdx assume list terminates when all invariants are `tt`. -/
private theorem stmts_mapIdx_assume_terminal
    (inv : List (String × Expression.Expr)) (ρ : Env Expression)
    (md : MetaData Expression) (mkLabel : Nat → String → String)
    (hwfb : WellFormedSemanticEvalBool ρ.eval)
    (hall : ∀ le ∈ inv, ρ.eval ρ.store le.2 = .some HasBool.tt) :
    CoreStar π φ
      (.stmts (inv.mapIdx fun i le =>
        Stmt.cmd (HasPassiveCmds.assume (mkLabel i le.1) le.2 md)) ρ)
      (.terminal ρ) := by
  apply stmts_passive_all_pass π φ _ ρ hwfb
  intro s hs; rw [List.mem_mapIdx] at hs
  obtain ⟨i, hi, rfl⟩ := hs
  exact assume_pass_step π φ _ _ md ρ (hall _ (List.getElem_mem hi)) hwfb

/-- CanFail for a list of assert statements where some expression is ff. -/
private theorem stmts_assert_list_canFail
    (ss : Statements) (ρ : Env Expression)
    (hwfb : WellFormedSemanticEvalBool ρ.eval)
    (hnf : ρ.hasFailure = Bool.false)
    (hall : ∀ s ∈ ss, ∃ (l : String) (e : Expression.Expr) (md' : MetaData Expression),
      s = Stmt.cmd (HasPassiveCmds.assert l e md') ∧
      (ρ.eval ρ.store e = .some HasBool.tt ∨ ρ.eval ρ.store e = .some HasBool.ff))
    (hff : ∃ s ∈ ss, ∃ (l : String) (e : Expression.Expr) (md' : MetaData Expression),
      s = Stmt.cmd (HasPassiveCmds.assert l e md') ∧ ρ.eval ρ.store e = .some HasBool.ff) :
    CanFailBlock π φ ss ρ := by
  induction ss with
  | nil => obtain ⟨_, hm, _⟩ := hff; exact absurd hm (by simp)
  | cons hd tl ih =>
    obtain ⟨l, e, md', heq, hbool⟩ := hall hd (.head ..)
    subst heq
    cases hbool with
    | inr hff_hd =>
      exact ⟨.seq (.terminal { ρ with hasFailure := ρ.hasFailure || Bool.true }) _,
        by simp [Config.getEnv, Bool.or_true],
        ReflTrans_Transitive _ _ _ _
          (.step _ _ _ .step_stmts_cons (.refl _))
          (seq_inner_star Expression (EvalCommand π φ) (EvalPureFunc φ) _ _ _
            (.step _ _ _ (.step_cmd (EvalCommand.cmd_sem (.eval_assert_fail hff_hd hwfb))) (.refl _)))⟩
    | inl htt_hd =>
      have htl_ff : ∃ s ∈ tl, ∃ l' e' md'',
          s = Stmt.cmd (HasPassiveCmds.assert l' e' md'') ∧ ρ.eval ρ.store e' = .some HasBool.ff := by
        obtain ⟨s, hs, l', e', md'', heq', hff'⟩ := hff
        cases hs with
        | head => simp at heq'; obtain ⟨_, rfl, _⟩ := heq'; rw [hff'] at htt_hd; cases htt_hd
        | tail _ h => exact ⟨s, h, l', e', md'', heq', hff'⟩
      have ⟨cfg, hfail, hreach⟩ := ih (fun s hs => hall s (.tail _ hs)) htl_ff
      exact ⟨cfg, hfail,
        ReflTrans_Transitive _ _ _ _
          (stmts_cons_step Expression (EvalCommand π φ) (EvalPureFunc φ) _ _ ρ ρ
            (assert_pass_step π φ _ _ md' ρ htt_hd hwfb))
          hreach⟩

/-- If some invariant evaluates to `ff`, the assert list CanFails. -/
private theorem stmts_mapIdx_assert_canFail
    (inv : List (String × Expression.Expr)) (ρ : Env Expression)
    (md : MetaData Expression) (mkLabel : Nat → String → String)
    (hwfb : WellFormedSemanticEvalBool ρ.eval)
    (hnf : ρ.hasFailure = Bool.false)
    (hinv_bool : ∀ le ∈ inv, ρ.eval ρ.store le.2 = .some HasBool.tt ∨
                              ρ.eval ρ.store le.2 = .some HasBool.ff)
    (hsome_ff : ∃ le ∈ inv, ρ.eval ρ.store le.2 = .some HasBool.ff) :
    CanFailBlock π φ (inv.mapIdx fun i le =>
      Stmt.cmd (HasPassiveCmds.assert (mkLabel i le.1) le.2 md)) ρ := by
  apply stmts_assert_list_canFail π φ _ ρ hwfb hnf
  · intro s hs; rw [List.mem_mapIdx] at hs
    obtain ⟨i, hi, rfl⟩ := hs
    exact ⟨_, _, md, rfl, hinv_bool _ (List.getElem_mem hi)⟩
  · obtain ⟨le, hle, hff⟩ := hsome_ff
    obtain ⟨i, hi, heq⟩ := List.mem_iff_getElem.mp hle
    refine ⟨Stmt.cmd (HasPassiveCmds.assert (mkLabel i le.1) le.2 md),
            List.mem_mapIdx.mpr ⟨i, hi, by subst heq; rfl⟩,
            mkLabel i le.1, le.2, md, rfl, hff⟩

/-- When not all invariants evaluate to tt and each is boolean, some evaluates to ff. -/
private theorem not_all_tt_implies_some_ff
    (inv : List (String × Expression.Expr)) (ρ : Env Expression)
    (hinv_bool : ∀ le ∈ inv, ρ.eval ρ.store le.2 = .some HasBool.tt ∨
                              ρ.eval ρ.store le.2 = .some HasBool.ff)
    (hnot_all_tt : ¬∀ le ∈ inv, ρ.eval ρ.store le.2 = .some HasBool.tt) :
    ∃ le ∈ inv, ρ.eval ρ.store le.2 = .some HasBool.ff := by
  induction inv with
  | nil => exact absurd (fun _ h => nomatch h) hnot_all_tt
  | cons x xs ih =>
    cases hinv_bool x (.head ..) with
    | inr hff => exact ⟨x, .head .., hff⟩
    | inl htt =>
      have : ¬∀ le ∈ xs, ρ.eval ρ.store le.2 = .some HasBool.tt := by
        intro h; apply hnot_all_tt; intro le hle
        cases hle with | head => exact htt | tail _ hmem => exact h le hmem
      have ⟨le, hle, hff⟩ := ih (fun le hle => hinv_bool le (.tail _ hle)) this
      exact ⟨le, .tail _ hle, hff⟩

/-- CanFail in a prefix lifts to CanFail in prefix ++ suffix.
    Uses the Prop→Type lifting `ReflTrans_to_ReflTransT` and structural inversion. -/
private theorem canFailBlock_append_left
    (ss₁ ss₂ : Statements) (ρ₀ : Env Expression)
    (h : CanFailBlock π φ ss₁ ρ₀) :
    CanFailBlock π φ (ss₁ ++ ss₂) ρ₀ := by
  obtain ⟨cfg, hfail, hreach⟩ := h
  -- Strategy: any reachable config from (.stmts ss₁ ρ₀) can be wrapped in a
  -- context carrying extra ss₂. The failing config is wrapped as (.seq cfg ss₂)
  -- which also has hasFailure = true (since getEnv only looks at cfg).
  -- Actually, we need a more careful proof. Let's just use the general
  -- monotonicity of hasFailure. If ss₁ reaches a failing config, then ρ₀
  -- itself might have hasFailure=true (in which case ss₁++ss₂ trivially CanFails)
  -- or some step sets it.
  -- Simplest approach: just use (.stmts (ss₁ ++ ss₂) ρ₀) with hasFailure monotonicity
  by_cases hnf : ρ₀.hasFailure = Bool.true
  · exact ⟨.stmts (ss₁ ++ ss₂) ρ₀, by simp [Config.getEnv]; exact hnf, .refl _⟩
  · -- ρ₀.hasFailure = false. The execution through ss₁ sets hasFailure at some point.
    -- In ss₁ ++ ss₂, the execution follows the same path for the ss₁ prefix.
    -- The key insight: embed the failing execution in the seq context with extra ss₂.
    -- We construct: (.stmts (ss₁ ++ ss₂) ρ₀) →* (.seq cfg ss₂) where cfg.hasFailure = true
    suffices ∀ src tgt, CoreStar π φ src tgt → tgt.getEnv.hasFailure = Bool.true →
        (∀ ss ρ, src = .stmts ss ρ →
          ∃ tgt', tgt'.getEnv.hasFailure = Bool.true ∧
            CoreStar π φ (.stmts (ss ++ ss₂) ρ) tgt') ∧
        (∀ inner ss, src = .seq inner ss →
          ∃ tgt', tgt'.getEnv.hasFailure = Bool.true ∧
            CoreStar π φ (.seq inner (ss ++ ss₂)) tgt') by
      have ⟨tgt', hf', hr'⟩ := (this _ _ hreach hfail).1 ss₁ ρ₀ rfl
      exact ⟨tgt', hf', hr'⟩
    intro src tgt hstar hf
    induction hstar with
    | refl =>
      exact ⟨fun ss ρ heq => by subst heq; exact ⟨_, by simp [Config.getEnv] at hf ⊢; exact hf, .refl _⟩,
             fun inner ss heq => by subst heq; exact ⟨_, by simp [Config.getEnv] at hf ⊢; exact hf, .refl _⟩⟩
    | step _ mid _ hstep hrest ih =>
      have ⟨ih1, ih2⟩ := ih hf
      exact ⟨fun ss ρ heq => by
        subst heq; cases hstep with
        | step_stmts_nil =>
          -- .stmts [] ρ →step .terminal ρ →* tgt, hasFailure = true
          -- So ρ.hasFailure || ... = true at some point during hrest
          -- But from .terminal ρ, no more steps. So tgt = .terminal ρ.
          -- And hf says ρ.hasFailure = true. But we assumed ρ₀.hasFailure = false...
          -- Actually ρ is the env from the stmts, which could be different from ρ₀
          -- after prior steps. We need (.stmts ([] ++ ss₂) ρ) = (.stmts ss₂ ρ).
          -- mid = .terminal ρ after step_stmts_nil. hrest goes from mid to tgt.
          -- Since terminal is stuck, hf implies the failure is already in mid.
          -- Our witness: (.stmts ss₂ ρ) with same env ρ which has hasFailure = true
          -- since mid.getEnv = ρ and hf propagates back through stuck terminal.
          have hf_ρ : ρ.hasFailure = Bool.true := by
            cases hrest with
            | refl => simp [Config.getEnv] at hf; exact hf
            | step _ _ _ hstep' _ => cases hstep'
          exact ⟨.stmts ss₂ ρ, by simp [Config.getEnv]; exact hf_ρ, .refl _⟩
        | step_stmts_cons =>
          have ⟨tgt', hf', hr'⟩ := ih2 _ _ rfl
          exact ⟨tgt', hf', .step _ _ _ .step_stmts_cons hr'⟩,
      fun inner ss heq => by
        subst heq; cases hstep with
        | step_seq_inner h =>
          have ⟨tgt', hf', hr'⟩ := ih2 _ _ rfl
          exact ⟨tgt', hf', .step _ _ _ (.step_seq_inner h) hr'⟩
        | step_seq_done =>
          have ⟨tgt', hf', hr'⟩ := ih1 _ _ rfl
          exact ⟨tgt', hf', .step _ _ _ .step_seq_done hr'⟩
        | step_seq_exit =>
          -- inner = .exiting lbl ρ, step to .exiting lbl ρ
          -- hrest is from .exiting to tgt, but exiting is stuck
          cases hrest with
          | refl =>
            exact ⟨_, hf, .step _ _ _ .step_seq_exit (.refl _)⟩
          | step _ _ _ h _ => cases h⟩

/-- The loop transformation for any guard produces this structure. -/
private theorem stmtResult_loop_struct (σ : LoopElimState)
    (guard : ExprOrNondet Expression)
    (measure : Option Expression.Expr)
    (inv : List (String × Expression.Expr))
    (body : Statements) (md : MetaData Expression) :
    ∃ (loop_label first_iter_label : String)
      (first_iter_body then_branch : Statements),
    stmtResult σ (.loop guard measure inv body md) =
      .block loop_label [.block first_iter_label first_iter_body {}, .ite guard then_branch [] {}] {} ∧
    first_iter_body =
      let loop_num := (StringGenState.gen "loop" σ.gen).fst
      let invSuffix : Nat → String → String := fun i lbl =>
        if lbl.isEmpty then toString i else s!"{i}_{lbl}"
      (inv.mapIdx fun i le => Stmt.cmd (HasPassiveCmds.assert
        s!"{loopElimAssertPrefix}{loop_num}_entry_invariant_{invSuffix i le.1}" le.2 md)) ++
      (inv.mapIdx fun i le => Stmt.cmd (HasPassiveCmds.assume
        s!"{loopElimAssumePrefix}{loop_num}_entry_invariant_{invSuffix i le.1}" le.2 md)) := by
  simp only [stmtResult, Stmt.removeLoopsM, StateT.run, bind, StateT.bind,
    genLoopNum, pure, StateT.pure, bumpStat, Id.run]
  cases guard with
  | det g => cases measure with
    | none => exact ⟨_, _, _, _, rfl, rfl⟩
    | some m => exact ⟨_, _, _, _, rfl, rfl⟩
  | nondet => cases measure with
    | none => exact ⟨_, _, _, _, rfl, rfl⟩
    | some m => exact ⟨_, _, _, _, rfl, rfl⟩

/-- The then-branch of the transformed loop contains body_statements (= blockResult of body)
    sandwiched between prefix stmts (havoc + assumes + pre_termination) and suffix stmts
    (maintain_invariants + post_termination). -/
private theorem stmtResult_loop_then_branch_struct (σ : LoopElimState)
    (guard : ExprOrNondet Expression)
    (measure : Option Expression.Expr)
    (inv : List (String × Expression.Expr))
    (body : Statements) (md : MetaData Expression) :
    ∃ (loop_label first_iter_label arb_iter_label : String)
      (first_iter_body : Statements)
      (prefix_stmts suffix_stmts exit_state_stmts : Statements)
      (maintain_invariants : Statements)
      (body_statements : Statements),
    stmtResult σ (.loop guard measure inv body md) =
      .block loop_label
        [.block first_iter_label first_iter_body {},
         .ite guard
           (.block arb_iter_label
             (prefix_stmts ++ body_statements ++ maintain_invariants ++ suffix_stmts) {}
            :: exit_state_stmts) [] {}] {} ∧
    body_statements = blockResult { σ with gen := (StringGenState.gen "loop" σ.gen).snd } body ∧
    maintain_invariants = inv.mapIdx fun i le =>
      Stmt.cmd (HasPassiveCmds.assert
        s!"{loopElimAssertPrefix}{(StringGenState.gen "loop" σ.gen).fst}_arbitrary_iter_maintain_invariant_{if le.1.isEmpty then toString i else s!"{i}_{le.1}"}" le.2 md) := by
  simp only [stmtResult, Stmt.removeLoopsM, StateT.run, bind, StateT.bind,
    genLoopNum, pure, StateT.pure, bumpStat, Id.run,
    blockResult, blockPostState]
  cases guard with
  | det g => cases measure with
    | none => exact ⟨_, _, _, _, _, _, _, _, _, rfl, rfl, rfl⟩
    | some m => exact ⟨_, _, _, _, _, _, _, _, _, rfl, rfl, rfl⟩
  | nondet => cases measure with
    | none => exact ⟨_, _, _, _, _, _, _, _, _, rfl, rfl, rfl⟩
    | some m => exact ⟨_, _, _, _, _, _, _, _, _, rfl, rfl, rfl⟩

/-- Route a CanFailBlock for the transformed body through the full target structure.
    Given body canfails in blockResult form and appropriate conditions,
    produce CanFail for the full stmtResult. -/
private theorem route_body_canfail_through_target
    (σ : LoopElimState)
    (guard : ExprOrNondet Expression)
    (measure : Option Expression.Expr)
    (inv : List (String × Expression.Expr))
    (body : Statements) (md : MetaData Expression)
    (ρ₀ : Env Expression)
    (hwfb : WellFormedSemanticEvalBool ρ₀.eval)
    (hwfvar : WellFormedSemanticEvalVar ρ₀.eval)
    (hnf : ρ₀.hasFailure = Bool.false)
    (hall_tt : ∀ le ∈ inv, ρ₀.eval ρ₀.store le.2 = .some HasBool.tt)
    (hinv_bool : ∀ le ∈ inv, ρ₀.eval ρ₀.store le.2 = .some HasBool.tt ∨
                              ρ₀.eval ρ₀.store le.2 = .some HasBool.ff)
    (hcf : CanFailBlock π φ (blockResult { σ with gen := (StringGenState.gen "loop" σ.gen).snd } body) ρ₀) :
    Transform.CanFail (LangCore π φ) (stmtResult σ (.loop guard measure inv body md)) ρ₀ := by
  sorry

/-- Master CanFail lemma: when the source loop enters and canfails
    (all invs tt, hasFailure=false at ρ₀), the target also canfails.
    Uses well-founded induction on source trace length. -/
private theorem loop_enter_canfail_simulation
    (hwf_ext : WFEvalExtension φ)
    (σ : LoopElimState)
    (guard : ExprOrNondet Expression)
    (measure : Option Expression.Expr)
    (inv : List (String × Expression.Expr))
    (body : Statements) (md : MetaData Expression)
    (ρ₀ : Env Expression)
    (hwfb : WellFormedSemanticEvalBool ρ₀.eval)
    (hwfv : WellFormedSemanticEvalVal ρ₀.eval)
    (hwfvar : WellFormedSemanticEvalVar ρ₀.eval)
    (hnf : ρ₀.hasFailure = Bool.false)
    (hall_tt : ∀ le ∈ inv, ρ₀.eval ρ₀.store le.2 = .some HasBool.tt)
    -- Source block canfails from ρ₀ (after loop enter, with ρ₀' = ρ₀)
    (hcf : ∃ cfg : CC, cfg.getEnv.hasFailure = Bool.true ∧
      CoreStar π φ (.block .none (.stmts (body ++ [.loop guard measure inv body md]) ρ₀)) cfg)
    -- Body-level IHs (for strictly smaller size)
    (ih_body_term : ∀ ρ ρ',
      WellFormedSemanticEvalBool ρ.eval → WellFormedSemanticEvalVal ρ.eval →
      WellFormedSemanticEvalVar ρ.eval →
      CoreStar π φ (.stmts body ρ) (.terminal ρ') →
      CanFailBlock π φ (blockResult { σ with gen := (StringGenState.gen "loop" σ.gen).snd } body) ρ ∨
      (ρ'.hasFailure = Bool.false →
        CoreStar π φ (.stmts (blockResult { σ with gen := (StringGenState.gen "loop" σ.gen).snd } body) ρ) (.terminal ρ')))
    (ih_body_cf : ∀ ρ,
      WellFormedSemanticEvalBool ρ.eval → WellFormedSemanticEvalVal ρ.eval →
      WellFormedSemanticEvalVar ρ.eval →
      CanFailBlock π φ body ρ →
      CanFailBlock π φ (blockResult { σ with gen := (StringGenState.gen "loop" σ.gen).snd } body) ρ) :
    Transform.CanFail (LangCore π φ)
      (stmtResult σ (.loop guard measure inv body md)) ρ₀ := by
  -- Extract inner canfail from the block
  obtain ⟨cfg, hfail, hblock_star⟩ := hcf
  obtain ⟨inner_cfg, hinner_fail, hinner_star⟩ :=
    block_canfail_to_inner hblock_star hfail
  -- Convert to ReflTransT for decomposition
  have hinner_T := reflTrans_to_T hinner_star
  -- Decompose stmts (body ++ [loop]): either body canfails or body terminates + loop canfails
  match stmtsT_append_canfail body (.loop guard measure inv body md) ρ₀ hinner_T hinner_fail with
  | .inl ⟨cfg_body, hfail_body, hstar_body⟩ =>
    -- Body canfails from ρ₀. By IH, target body also canfails.
    have htgt_body_cf := ih_body_cf ρ₀ hwfb hwfv hwfvar ⟨cfg_body, hfail_body, hstar_body⟩
    have hinv_bool : ∀ le ∈ inv, ρ₀.eval ρ₀.store le.2 = .some HasBool.tt ∨
        ρ₀.eval ρ₀.store le.2 = .some HasBool.ff :=
      fun le hle => .inl (hall_tt le hle)
    exact route_body_canfail_through_target π φ σ guard measure inv body md ρ₀
      hwfb hwfvar hnf hall_tt hinv_bool htgt_body_cf
  | .inr ⟨ρ₁, hterm_body_prop, cfg_loop, hloop_T, hloop_fail, _⟩ =>
    -- Body terminates at ρ₁, loop canfails from ρ₁.
    have hterm_body : CoreStar π φ (.stmts body ρ₀) (.terminal ρ₁) := hterm_body_prop
    have hinv_bool : ∀ le ∈ inv, ρ₀.eval ρ₀.store le.2 = .some HasBool.tt ∨
        ρ₀.eval ρ₀.store le.2 = .some HasBool.ff :=
      fun le hle => .inl (hall_tt le hle)
    -- Case split on ρ₁.hasFailure
    by_cases hnf₁ : ρ₁.hasFailure = Bool.true
    · -- ρ₁.hasFailure=true: body produced a failing terminal → body canfails
      have hcf_body : CanFailBlock π φ body ρ₀ :=
        ⟨.terminal ρ₁, by show ρ₁.hasFailure = Bool.true; exact hnf₁, hterm_body⟩
      have htgt_body_cf := ih_body_cf ρ₀ hwfb hwfv hwfvar hcf_body
      exact route_body_canfail_through_target π φ σ guard measure inv body md ρ₀
        hwfb hwfvar hnf hall_tt hinv_bool htgt_body_cf
    · -- ρ₁.hasFailure=false: loop canfails from ρ₁.
      have hnf₁' : ρ₁.hasFailure = Bool.false := by cases h : ρ₁.hasFailure <;> simp_all
      -- Examine the body simulation IH
      match ih_body_term ρ₀ ρ₁ hwfb hwfv hwfvar hterm_body with
      | .inl htgt_cf =>
        exact route_body_canfail_through_target π φ σ guard measure inv body md ρ₀
          hwfb hwfvar hnf hall_tt hinv_bool htgt_cf
      | .inr htgt_ok =>
        -- Target body' terminates at ρ₁. Loop canfails from ρ₁.
        -- The loop step at ρ₁ evaluates invs. We examine the loop step.
        have htgt_body_term := htgt_ok hnf₁'
        sorry -- Decompose loop canfail at ρ₁: either inv violation → target maintain_invariants fails, or recurse

/-! ## Havoc infrastructure -/

/-- A single `havoc n` command (i.e. `set n .nondet`) executes as identity
    when `ρ.store n` is already defined. -/
private theorem havoc_identity_step
    (n : Expression.Ident) (md : MetaData Expression)
    (ρ : Env Expression) (v : Expression.Expr)
    (hdef : ρ.store n = some v)
    (hwfvar : WellFormedSemanticEvalVar ρ.eval)
    (hnf : ρ.hasFailure = Bool.false) :
    CoreStar π φ (.stmt (.cmd (HasHavoc.havoc n md)) ρ) (.terminal ρ) := by
  change CoreStar π φ (.stmt (.cmd (CmdExt.cmd (Cmd.set n .nondet md))) ρ) (.terminal ρ)
  have hupdate : UpdateState Expression ρ.store n v ρ.store :=
    .update hdef hdef (fun _ _ => rfl)
  exact .step _ _ _
    (.step_cmd (EvalCommand.cmd_sem (.eval_set_nondet hupdate hwfvar)))
    (by simp [Bool.or_false]; cases ρ; exact .refl _)

/-- Execute a list of havoc commands as identity when all variables are defined. -/
private theorem havocs_identity_stmts
    (vs : List Expression.Ident) (md : MetaData Expression)
    (ρ : Env Expression)
    (hdef : ∀ n ∈ vs, (ρ.store n).isSome)
    (hwfvar : WellFormedSemanticEvalVar ρ.eval)
    (hnf : ρ.hasFailure = Bool.false) :
    CoreStar π φ (.stmts (vs.map fun n => Stmt.cmd (HasHavoc.havoc n md)) ρ)
      (.terminal ρ) := by
  induction vs with
  | nil => simp [List.map]; exact .step _ _ _ .step_stmts_nil (.refl _)
  | cons n rest ih =>
    simp only [List.map]
    have hdef_n := hdef n (.head ..)
    have hdef_rest : ∀ m ∈ rest, (ρ.store m).isSome :=
      fun m hm => hdef m (.tail _ hm)
    obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp hdef_n
    exact ReflTrans_Transitive _ _ _ _
      (stmts_cons_step Expression (EvalCommand π φ) (EvalPureFunc φ)
        (.cmd (HasHavoc.havoc n md))
        (rest.map fun n => Stmt.cmd (HasHavoc.havoc n md))
        ρ ρ (havoc_identity_step π φ n md ρ v hv hwfvar hnf))
      (ih hdef_rest)

/-- Execute the havoc block (`.block label (vs.map havoc) {}`) as identity. -/
private theorem havoc_block_identity
    (label : String) (vs : List Expression.Ident) (md : MetaData Expression)
    (ρ : Env Expression)
    (hdef : ∀ n ∈ vs, (ρ.store n).isSome)
    (hwfvar : WellFormedSemanticEvalVar ρ.eval)
    (hnf : ρ.hasFailure = Bool.false) :
    CoreStar π φ
      (.stmt (.block label (vs.map fun n => Stmt.cmd (HasHavoc.havoc n md)) {}) ρ)
      (.terminal ρ) :=
  block_wrap_terminal π φ label _ _ ρ ρ
    (havocs_identity_stmts π φ vs md ρ hdef hwfvar hnf)

/-- A single `havoc n` command can change the store value at `n` to any target
    value, leaving all other variables unchanged. -/
private theorem havoc_targeting_single
    (x : Expression.Ident) (md : MetaData Expression)
    (ρ₀ : Env Expression) (v_target : Expression.Expr)
    (hdef_src : (ρ₀.store x).isSome)
    (hwfvar : WellFormedSemanticEvalVar ρ₀.eval)
    (hnf : ρ₀.hasFailure = Bool.false) :
    ∃ σ' : SemanticStore Expression,
      σ' x = some v_target ∧
      (∀ y, x ≠ y → σ' y = ρ₀.store y) ∧
      CoreStar π φ
        (.stmt (.cmd (HasHavoc.havoc x md)) ρ₀)
        (.terminal { ρ₀ with store := σ' }) := by
  change ∃ σ' : SemanticStore Expression,
    σ' x = some v_target ∧
    (∀ y, x ≠ y → σ' y = ρ₀.store y) ∧
    CoreStar π φ
      (.stmt (.cmd (CmdExt.cmd (Cmd.set x .nondet md))) ρ₀)
      (.terminal { ρ₀ with store := σ' })
  obtain ⟨v_old, hv_old⟩ := Option.isSome_iff_exists.mp hdef_src
  let σ' : SemanticStore Expression := fun y => if x = y then some v_target else ρ₀.store y
  have hσ'_x : σ' x = some v_target := by simp [σ']
  have hσ'_other : ∀ y, x ≠ y → σ' y = ρ₀.store y := by
    intro y hne; simp [σ', hne]
  have hupdate : UpdateState Expression ρ₀.store x v_target σ' :=
    .update hv_old hσ'_x hσ'_other
  exact ⟨σ', hσ'_x, hσ'_other,
    .step _ _ _
      (.step_cmd (EvalCommand.cmd_sem (.eval_set_nondet hupdate hwfvar)))
      (by simp [Bool.or_false]; exact .refl _)⟩

/-- Execute a list of havoc commands, updating the store to match `σ_target`
    on each variable in `vars`. -/
private theorem havocs_targeting_stmts
    (vars : List Expression.Ident) (md : MetaData Expression)
    (ρ₀ : Env Expression) (σ_target : SemanticStore Expression)
    (hwfvar : WellFormedSemanticEvalVar ρ₀.eval)
    (hdef_src : ∀ x ∈ vars, (ρ₀.store x).isSome)
    (hdef_tgt : ∀ x ∈ vars, (σ_target x).isSome)
    (hnf : ρ₀.hasFailure = Bool.false) :
    ∃ σ_out : SemanticStore Expression,
      (∀ x ∈ vars, σ_out x = σ_target x) ∧
      (∀ x, x ∉ vars → σ_out x = ρ₀.store x) ∧
      CoreStar π φ
        (.stmts (vars.map fun n => Stmt.cmd (HasHavoc.havoc n md)) ρ₀)
        (.terminal { ρ₀ with store := σ_out }) := by
  induction vars generalizing ρ₀ with
  | nil =>
    refine ⟨ρ₀.store, fun _ h => absurd h (List.not_mem_nil), fun _ _ => rfl, ?_⟩
    show CoreStar π φ (.stmts (List.map _ []) ρ₀) (.terminal { ρ₀ with store := ρ₀.store })
    rw [List.map_nil]
    have h : ({ ρ₀ with store := ρ₀.store } : Env Expression) = ρ₀ := by
      cases ρ₀; rfl
    rw [h]; exact .step _ _ _ .step_stmts_nil (.refl _)
  | cons x rest ih =>
    have hdef_x := hdef_tgt x (.head ..)
    obtain ⟨v_target, hv_target⟩ := Option.isSome_iff_exists.mp hdef_x
    have ⟨σ₁, hσ₁_x, hσ₁_other, hstep_x⟩ :=
      havoc_targeting_single π φ x md ρ₀ v_target (hdef_src x (.head ..)) hwfvar hnf
    let ρ₁ : Env Expression := { ρ₀ with store := σ₁ }
    have hdef_src_rest : ∀ y ∈ rest, (σ₁ y).isSome := by
      intro y hy
      by_cases hxy : x = y
      · subst hxy; rw [hσ₁_x]; simp
      · rw [hσ₁_other y hxy]; exact hdef_src y (.tail _ hy)
    have hdef_tgt_rest : ∀ y ∈ rest, (σ_target y).isSome :=
      fun y hy => hdef_tgt y (.tail _ hy)
    have ⟨σ_out, hmatch, hother, hstar_rest⟩ :=
      ih ρ₁ hwfvar hdef_src_rest hdef_tgt_rest hnf
    refine ⟨σ_out, ?_, ?_, ?_⟩
    · intro y hy
      cases hy with
      | head =>
        by_cases hx_rest : x ∈ rest
        · exact hmatch x hx_rest
        · exact (hother x hx_rest).trans (hσ₁_x.trans hv_target.symm)
      | tail _ hy' => exact hmatch y hy'
    · intro y hy
      have hy_rest : y ∉ rest := fun h => hy (.tail _ h)
      have hxy : x ≠ y := fun h => hy (h ▸ .head ..)
      exact (hother y hy_rest).trans (hσ₁_other y hxy)
    · simp only [List.map]
      exact ReflTrans_Transitive _ _ _ _
        (stmts_cons_step Expression (EvalCommand π φ) (EvalPureFunc φ)
          (.cmd (HasHavoc.havoc x md))
          (rest.map fun n => Stmt.cmd (HasHavoc.havoc n md))
          ρ₀ ρ₁ hstep_x)
        hstar_rest

/-- Execute the havoc block, targeting `σ_target` on modified vars.
    When `ρ_target` agrees with `ρ₀` outside `vars`, reaches
    `{ ρ₀ with store := ρ_target.store }`. -/
private theorem havoc_block_to_target
    (label : String) (vars : List Expression.Ident) (md : MetaData Expression)
    (ρ₀ ρ_target : Env Expression)
    (hwfvar : WellFormedSemanticEvalVar ρ₀.eval)
    (hdef_src : ∀ x ∈ vars, (ρ₀.store x).isSome)
    (hdef_tgt : ∀ x ∈ vars, (ρ_target.store x).isSome)
    (hagree : ∀ x, x ∉ vars → ρ_target.store x = ρ₀.store x)
    (hnf : ρ₀.hasFailure = Bool.false) :
    CoreStar π φ
      (.stmt (.block label (vars.map fun n => Stmt.cmd (HasHavoc.havoc n md)) {}) ρ₀)
      (.terminal { ρ₀ with store := ρ_target.store }) := by
  have ⟨σ_out, hmatch, hother, hstar⟩ :=
    havocs_targeting_stmts π φ vars md ρ₀ ρ_target.store hwfvar hdef_src hdef_tgt hnf
  suffices h : σ_out = ρ_target.store by rw [← h]; exact block_wrap_terminal π φ label _ _ ρ₀ _ hstar
  funext x
  by_cases hx : x ∈ vars
  · exact hmatch x hx
  · rw [hother x hx, ← hagree x hx]

/-! ## Composing statement traces -/

/-- Two consecutive statements terminate → the concatenation terminates. -/
private theorem stmts_pair_terminal
    (s₁ s₂ : Statement) (ρ₀ ρ₁ ρ₂ : Env Expression)
    (h₁ : CoreStar π φ (.stmt s₁ ρ₀) (.terminal ρ₁))
    (h₂ : CoreStar π φ (.stmt s₂ ρ₁) (.terminal ρ₂)) :
    CoreStar π φ (.stmts [s₁, s₂] ρ₀) (.terminal ρ₂) :=
  ReflTrans_Transitive _ _ _ _
    (stmts_cons_step Expression (EvalCommand π φ) (EvalPureFunc φ) s₁ [s₂] ρ₀ ρ₁ h₁)
    (ReflTrans_Transitive _ _ _ _
      (.step _ _ _ .step_stmts_cons (.refl _))
      (ReflTrans_Transitive _ _ _ _
        (seq_inner_star Expression (EvalCommand π φ) (EvalPureFunc φ) _ _ [] h₂)
        (.step _ _ _ .step_seq_done (.step _ _ _ .step_stmts_nil (.refl _)))))

/-- Statement list prefix terminates at ρ₁, suffix terminates at ρ₂ →
    concatenation terminates at ρ₂. -/
private theorem stmts_concat_terminal
    (ss₁ ss₂ : Statements) (ρ₀ ρ₁ ρ₂ : Env Expression)
    (h₁ : CoreStar π φ (.stmts ss₁ ρ₀) (.terminal ρ₁))
    (h₂ : CoreStar π φ (.stmts ss₂ ρ₁) (.terminal ρ₂)) :
    CoreStar π φ (.stmts (ss₁ ++ ss₂) ρ₀) (.terminal ρ₂) :=
  ReflTrans_Transitive _ _ _ _
    (stmts_prefix_terminal_append Expression (EvalCommand π φ) (EvalPureFunc φ) ss₁ ss₂ ρ₀ ρ₁ h₁)
    h₂

/-- If a prefix of statements terminates and the suffix CanFails, the whole
    concatenation CanFails. -/
private theorem canFailBlock_prefix_terminal_suffix
    (pfx sfx : Statements) (ρ₀ ρ₁ : Env Expression)
    (hpfx : CoreStar π φ (.stmts pfx ρ₀) (.terminal ρ₁))
    (hsfx : CanFailBlock π φ sfx ρ₁) :
    CanFailBlock π φ (pfx ++ sfx) ρ₀ := by
  obtain ⟨cfg, hfail, hreach⟩ := hsfx
  exact ⟨cfg, hfail,
    ReflTrans_Transitive _ _ _ _
      (stmts_prefix_terminal_append Expression (EvalCommand π φ) (EvalPureFunc φ)
        pfx sfx ρ₀ ρ₁ hpfx)
      hreach⟩

/-! ## Store preservation lemmas -/

/-- Variables that are defined (isSome) in the store at some config remain
    defined after any number of small steps.  This follows from the fact that
    `UpdateState` and `InitState` both preserve `isSome` on already-defined
    variables (`UpdateStateDefMonotone`, `InitStateDefMonotone`). A full proof
    requires an induction over `StepStmt` constructors; we state it here and
    will prove it in a subsequent PR. -/
private theorem evalCommand_preserves_isSome
    {ρ : Env Expression} {c : Command} {σ' : CoreStore} {f : Bool}
    {n : Expression.Ident}
    (heval : EvalCommand π φ ρ.eval ρ.store c σ' f)
    (hdef : (ρ.store n).isSome) :
    (σ' n).isSome := by
  have hdef' : isDefined ρ.store [n] := fun v hv => by
    cases List.mem_singleton.mp hv; exact hdef
  cases heval with
  | cmd_sem hcmd =>
    exact (EvalCmdDefMonotone' hdef' hcmd) n (List.Mem.head _)
  | call_sem _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hups =>
    exact (UpdateStatesDefMonotone hdef' hups) n (List.Mem.head _)

private theorem star_preserves_isDefined_single
    {c₁ c₂ : CC} {n : Expression.Ident}
    (hstar : CoreStar π φ c₁ c₂)
    (hdef : (c₁.getEnv.store n).isSome) :
    (c₂.getEnv.store n).isSome := by
  suffices ∀ (a b : CC),
      StepStmt Expression (EvalCommand π φ) (EvalPureFunc φ) a b →
      ∀ n : Expression.Ident, (a.getEnv.store n).isSome → (b.getEnv.store n).isSome by
    induction hstar with
    | refl => exact hdef
    | step _ _ _ hstep _ ih => exact ih (this _ _ hstep n hdef)
  intro a b hstep
  induction hstep with
  | step_cmd heval =>
    intro n hdef
    simp only [Config.getEnv] at hdef ⊢
    exact evalCommand_preserves_isSome (π := π) (φ := φ) heval hdef
  | step_block => exact fun _ h => h
  | step_ite_true => exact fun _ h => h
  | step_ite_false => exact fun _ h => h
  | step_ite_nondet_true => exact fun _ h => h
  | step_ite_nondet_false => exact fun _ h => h
  | step_loop_enter => exact fun _ h => h
  | step_loop_exit => exact fun _ h => h
  | step_loop_nondet_enter => exact fun _ h => h
  | step_loop_nondet_exit => exact fun _ h => h
  | step_exit => exact fun _ h => h
  | step_funcDecl => intro n h; simp [Config.getEnv]; exact h
  | step_typeDecl => exact fun _ h => h
  | step_stmts_nil => exact fun _ h => h
  | step_stmts_cons => exact fun _ h => h
  | step_seq_inner _ ih => exact fun n h => ih n h
  | step_seq_done => exact fun _ h => h
  | step_seq_exit => exact fun _ h => h
  | step_block_body _ ih => exact fun n h => ih n h
  | step_block_done => exact fun _ h => h
  | step_block_exit_none => exact fun _ h => h
  | step_block_exit_match => exact fun _ h => h
  | step_block_exit_mismatch => exact fun _ h => h

/-! ## Assume block step -/

/-- The assume block with guard + invariant assumes passes when guard and all
    invs are tt at ρ. Uses `stmts_passive_all_pass` to handle any label. -/
private theorem assume_block_step_det
    (label : String) (g : Expression.Expr)
    (guard_label : String)
    (inv : List (String × Expression.Expr)) (md : MetaData Expression)
    (mkInvLabel : Nat → String → String)
    (ρ : Env Expression)
    (hguard_tt : ρ.eval ρ.store g = some HasBool.tt)
    (hall_tt : ∀ le ∈ inv, ρ.eval ρ.store le.2 = some HasBool.tt)
    (hwfb : WellFormedSemanticEvalBool ρ.eval) :
    CoreStar π φ
      (.stmt (.block label
        ([Stmt.cmd (HasPassiveCmds.assume guard_label g md)] ++
         inv.mapIdx fun i le =>
          Stmt.cmd (HasPassiveCmds.assume (mkInvLabel i le.1) le.2 md)) md) ρ)
      (.terminal ρ) := by
  apply block_wrap_terminal
  apply stmts_passive_all_pass π φ _ ρ hwfb
  intro s hs
  simp [List.mem_append, List.mem_mapIdx, List.mem_singleton] at hs
  rcases hs with rfl | ⟨i, hi, rfl⟩
  · exact assume_pass_step π φ _ g md ρ hguard_tt hwfb
  · exact assume_pass_step π φ _ _ md ρ (hall_tt _ (List.getElem_mem hi)) hwfb

/-- Nondet version: no guard assume, only invariant assumes. -/
private theorem assume_block_step_nondet
    (label : String)
    (inv : List (String × Expression.Expr)) (md : MetaData Expression)
    (mkInvLabel : Nat → String → String)
    (ρ : Env Expression)
    (hall_tt : ∀ le ∈ inv, ρ.eval ρ.store le.2 = some HasBool.tt)
    (hwfb : WellFormedSemanticEvalBool ρ.eval) :
    CoreStar π φ
      (.stmt (.block label
        ([] ++ inv.mapIdx fun i le =>
          Stmt.cmd (HasPassiveCmds.assume (mkInvLabel i le.1) le.2 md)) md) ρ)
      (.terminal ρ) := by
  apply block_wrap_terminal
  simp only [List.nil_append]
  exact stmts_mapIdx_assume_terminal π φ inv ρ md mkInvLabel hwfb hall_tt

/-! ## Assert list CanFail for maintain invariants -/

/-- The maintain_invariants assert list CanFails when some invariant is ff. -/
private theorem stmts_mapIdx_maintain_assert_canFail
    (inv : List (String × Expression.Expr)) (ρ : Env Expression)
    (md : MetaData Expression) (mkLabel : Nat → String → String)
    (hwfb : WellFormedSemanticEvalBool ρ.eval)
    (hnf : ρ.hasFailure = Bool.false)
    (hinv_bool : ∀ le ∈ inv, ρ.eval ρ.store le.2 = .some HasBool.tt ∨
                              ρ.eval ρ.store le.2 = .some HasBool.ff)
    (hsome_ff : ∃ le ∈ inv, ρ.eval ρ.store le.2 = .some HasBool.ff) :
    CanFailBlock π φ (inv.mapIdx fun i le =>
      Stmt.cmd (HasPassiveCmds.assert (mkLabel i le.1) le.2 md)) ρ :=
  stmts_mapIdx_assert_canFail π φ inv ρ md mkLabel hwfb hnf hinv_bool hsome_ff

/-- The maintain_invariants assert list terminates when all invs are tt. -/
private theorem stmts_mapIdx_maintain_assert_terminal
    (inv : List (String × Expression.Expr)) (ρ : Env Expression)
    (md : MetaData Expression) (mkLabel : Nat → String → String)
    (hwfb : WellFormedSemanticEvalBool ρ.eval)
    (hall_tt : ∀ le ∈ inv, ρ.eval ρ.store le.2 = .some HasBool.tt) :
    CoreStar π φ
      (.stmts (inv.mapIdx fun i le =>
        Stmt.cmd (HasPassiveCmds.assert (mkLabel i le.1) le.2 md)) ρ)
      (.terminal ρ) :=
  stmts_mapIdx_assert_terminal π φ inv ρ md mkLabel hwfb hall_tt

/-! ## Block-none decomposition and hcov-free stmts decomposition -/

/-- Decompose `.block .none inner` reaching terminal in `ReflTransT`:
    the inner either reached `.terminal ρ'` or `.exiting .none ρ'` (break). -/
private theorem blockT_none_reaches_terminal
    {inner : CC} {ρ' : Env Expression}
    (hstar : ReflTransT (StepStmt Expression (EvalCommand π φ) (EvalPureFunc φ))
      (.block .none inner) (.terminal ρ')) :
    (∃ (h : ReflTransT (StepStmt Expression (EvalCommand π φ) (EvalPureFunc φ))
          inner (.terminal ρ')), h.len < hstar.len) ∨
    (∃ (h : ReflTransT (StepStmt Expression (EvalCommand π φ) (EvalPureFunc φ))
          inner (.exiting .none ρ')), h.len < hstar.len) := by
  suffices ∀ src tgt (hstar_g : ReflTransT (StepStmt Expression (EvalCommand π φ) (EvalPureFunc φ)) src tgt),
      ∀ inner ρ', src = .block .none inner → tgt = .terminal ρ' →
      (∃ (h : ReflTransT (StepStmt Expression (EvalCommand π φ) (EvalPureFunc φ))
            inner (.terminal ρ')), h.len < hstar_g.len) ∨
      (∃ (h : ReflTransT (StepStmt Expression (EvalCommand π φ) (EvalPureFunc φ))
            inner (.exiting .none ρ')), h.len < hstar_g.len) from
    this _ _ hstar _ _ rfl rfl
  intro src tgt hstar_g
  induction hstar_g with
  | refl => intro _ _ hsrc htgt; subst hsrc; cases htgt
  | step _ mid _ hstep hrest ih =>
    intro inner ρ' hsrc htgt; subst hsrc
    cases hstep with
    | step_block_body h =>
      match ih _ _ rfl htgt with
      | .inl ⟨h_inner, hlen⟩ =>
        exact .inl ⟨.step _ _ _ h h_inner, by simp [ReflTransT.len]; omega⟩
      | .inr ⟨h_inner, hlen⟩ =>
        exact .inr ⟨.step _ _ _ h h_inner, by simp [ReflTransT.len]; omega⟩
    | step_block_done =>
      subst htgt
      exact .inl ⟨hrest, by simp [ReflTransT.len]⟩
    | step_block_exit_none =>
      subst htgt
      -- mid = .terminal ρ_env, inner = .exiting .none ρ_env
      -- hrest goes from .terminal to .terminal, must be refl
      match hrest with
      | .refl _ => exact .inr ⟨.refl _, by simp [ReflTransT.len]⟩
      | .step _ _ _ h _ => cases h
    | step_block_exit_match heq => cases heq
    | step_block_exit_mismatch =>
      subst htgt
      cases hrest with | step _ _ _ h _ => cases h

/-- Decompose `.stmts (ss₁ ++ [s])` reaching terminal into:
    a full `.stmts ss₁` run to some intermediate `ρ₁` followed by
    a strictly shorter `s`-run.  Unlike `stmtsT_append_terminal`,
    this does **not** require `exitsCoveredByBlocks`. -/
private theorem stmtsT_append_terminal_noCov
    (ss₁ : List Statement) (s : Statement) (ρ₀ ρ' : Env Expression)
    (hstar : ReflTransT (StepStmt Expression (EvalCommand π φ) (EvalPureFunc φ))
      (.stmts (ss₁ ++ [s]) ρ₀) (.terminal ρ')) :
    ∃ (ρ₁ : Env Expression),
      ∃ (_ : CoreStar π φ (.stmts ss₁ ρ₀) (.terminal ρ₁)),
      ∃ (hs : ReflTransT (StepStmt Expression (EvalCommand π φ) (EvalPureFunc φ))
          (.stmt s ρ₁) (.terminal ρ')),
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
    have ⟨ρ₂, h_rest', h_s, hlen₂⟩ := ih ρ₁ h_rest
    exact ⟨ρ₂,
      ReflTrans_Transitive _ _ _ _
        (stmts_cons_step Expression (EvalCommand π φ) (EvalPureFunc φ) s' rest' ρ₀ ρ₁
          (reflTransT_to_prop h_s'))
        h_rest',
      h_s, by grind⟩

/-- When a block body has no function declarations and reaches `.exiting`,
    the evaluator is preserved. -/
private theorem noFuncDecl_preserves_eval_block_exiting
    (bss : Statements) (ρ ρ' : Env Expression) (lbl : Option String)
    (hnofd : Block.noFuncDecl bss = Bool.true)
    (hstar : CoreStar π φ (.stmts bss ρ) (.exiting lbl ρ')) :
    ρ'.eval = ρ.eval := by
  suffices ∀ c₁ c₂,
      Config.noFuncDecl (P := Expression) (CmdT := Command) c₁ →
      CoreStar π φ c₁ c₂ →
      c₂.getEnv.eval = c₁.getEnv.eval by
    exact this _ _ (show Config.noFuncDecl (.stmts bss ρ) from hnofd) hstar
  intro c₁ c₂ hnofd_c hstar_c
  induction hstar_c with
  | refl => rfl
  | step _ mid _ hstep _ ih =>
    have ⟨heq, hnofd_mid⟩ :=
      step_preserves_eval_noFuncDecl Expression (EvalCommand π φ) (EvalPureFunc φ) _ _ hstep hnofd_c
    rw [ih hnofd_mid, heq]

/-- A `.block .none` configuration can never reach `.exiting .none`:
    `step_block_exit_none` catches `.exiting .none` and produces `.terminal`,
    while `step_block_exit_mismatch` only propagates `.exiting (some l)`. -/
private theorem block_none_not_exit_none
    {inner : CC} {ρ' : Env Expression}
    (hstar : CoreStar π φ (.block .none inner) (.exiting .none ρ')) : False := by
  suffices ∀ src tgt, CoreStar π φ src tgt →
      ∀ inner ρ', src = .block (none : Option String) inner → tgt = .exiting .none ρ' →
      False from
    this _ _ hstar _ _ rfl rfl
  intro src tgt hstar_g
  induction hstar_g with
  | refl => intro _ _ hsrc htgt; subst hsrc; cases htgt
  | step _ mid _ hstep hrest ih =>
    intro inner ρ' hsrc htgt; subst hsrc
    cases hstep with
    | step_block_body h => exact ih _ _ rfl htgt
    | step_block_done =>
      -- mid = .terminal, can't reach .exiting .none
      subst htgt; cases hrest with | step _ _ _ h _ => cases h
    | step_block_exit_none =>
      -- mid = .terminal (caught break), can't reach .exiting .none
      subst htgt; cases hrest with | step _ _ _ h _ => cases h
    | step_block_exit_match heq => cases heq
    | step_block_exit_mismatch hne =>
      -- mid = .exiting (some l), can't reach .exiting .none (some ≠ none)
      subst htgt; cases hrest with | step _ _ _ h _ => cases h

/-- A det-guarded loop statement can never reach `.exiting .none`.
    The loop either exits (terminal) or enters a `.block .none (...)`,
    and `.block .none` only propagates `.exiting (some l)`. -/
private theorem loop_det_cannot_exit_none
    (g : Expression.Expr) (measure : Option Expression.Expr)
    (inv : List (String × Expression.Expr))
    (body : Statements) (md : MetaData Expression)
    (ρ ρ' : Env Expression)
    (hstar : CoreStar π φ (.stmt (.loop (.det g) measure inv body md) ρ) (.exiting .none ρ')) :
    False := by
  cases hstar with
  | step _ mid _ hstep hrest =>
    cases hstep with
    | step_loop_exit _ _ _ _ =>
      -- step_loop_exit produces terminal
      cases hrest with | step _ _ _ h _ => cases h
    | step_loop_enter _ _ _ _ =>
      -- step_loop_enter produces .block .none (...)
      exact block_none_not_exit_none (π := π) (φ := φ) hrest

/-- A nondet-guarded loop statement can never reach `.exiting .none`. -/
private theorem loop_nondet_cannot_exit_none
    (measure : Option Expression.Expr)
    (inv : List (String × Expression.Expr))
    (body : Statements) (md : MetaData Expression)
    (ρ ρ' : Env Expression)
    (hstar : CoreStar π φ (.stmt (.loop .nondet measure inv body md) ρ) (.exiting .none ρ')) :
    False := by
  cases hstar with
  | step _ mid _ hstep hrest =>
    cases hstep with
    | step_loop_nondet_exit _ _ =>
      cases hrest with | step _ _ _ h _ => cases h
    | step_loop_nondet_enter _ _ =>
      exact block_none_not_exit_none (π := π) (φ := φ) hrest

/-! ## Loop invariant dichotomy

For a terminating loop where the guard is true and all invariants hold at entry,
either some iteration body maps a state satisfying G∧I to one where some
invariant fails, the "last iteration" from ρ_last reaches ρ' with all
invariants holding, or the loop body broke (reached `.exiting .none`).

The full proof uses well-founded recursion on `ReflTransT` trace length,
unwrapping the `.block .none` introduced by the loop step, decomposing the
`body ++ [loop]` trace via `stmtsT_append_terminal_noCov` or handling the
break case when inner reaches `.exiting .none`, and recursing. -/

private theorem loop_invariant_dichotomy_det
    (hwf_ext : WFEvalExtension φ)
    (g : Expression.Expr) (measure : Option Expression.Expr)
    (inv : List (String × Expression.Expr))
    (body : Statements) (md : MetaData Expression)
    (ρ₀ ρ' : Env Expression)
    (hguard_tt : ρ₀.eval ρ₀.store g = some HasBool.tt)
    (hall_tt : ∀ le ∈ inv, ρ₀.eval ρ₀.store le.2 = some HasBool.tt)
    (hwfb : WellFormedSemanticEvalBool ρ₀.eval)
    (hwfv : WellFormedSemanticEvalVal ρ₀.eval)
    (hwfvar : WellFormedSemanticEvalVar ρ₀.eval)
    (hnofd : Block.noFuncDecl body = Bool.true)
    (hnf : ρ'.hasFailure = Bool.false)
    (hloop : CoreStar π φ (.stmt (.loop (.det g) measure inv body md) ρ₀) (.terminal ρ')) :
    -- Violation
    (∃ ρ_pre ρ_post,
      ρ_pre.eval ρ_pre.store g = some HasBool.tt ∧
      (∀ le ∈ inv, ρ_pre.eval ρ_pre.store le.2 = some HasBool.tt) ∧
      WellFormedSemanticEvalBool ρ_pre.eval ∧
      WellFormedSemanticEvalVal ρ_pre.eval ∧
      WellFormedSemanticEvalVar ρ_pre.eval ∧
      ρ_pre.hasFailure = Bool.false ∧
      CoreStar π φ (.stmts body ρ_pre) (.terminal ρ_post) ∧
      ρ_post.hasFailure = Bool.false ∧
      (∃ le ∈ inv, ρ_post.eval ρ_post.store le.2 = some HasBool.ff) ∧
      ρ_pre.eval = ρ₀.eval)
    ∨
    -- Success
    (∃ ρ_last,
      ρ_last.eval ρ_last.store g = some HasBool.tt ∧
      (∀ le ∈ inv, ρ_last.eval ρ_last.store le.2 = some HasBool.tt) ∧
      WellFormedSemanticEvalBool ρ_last.eval ∧
      WellFormedSemanticEvalVal ρ_last.eval ∧
      WellFormedSemanticEvalVar ρ_last.eval ∧
      ρ_last.hasFailure = Bool.false ∧
      CoreStar π φ (.stmts body ρ_last) (.terminal ρ') ∧
      (∀ le ∈ inv, ρ'.eval ρ'.store le.2 = some HasBool.tt) ∧
      ρ_last.eval = ρ₀.eval)
    ∨
    -- Break: body exited with .none (break caught by block)
    (∃ ρ_last,
      ρ_last.eval ρ_last.store g = some HasBool.tt ∧
      (∀ le ∈ inv, ρ_last.eval ρ_last.store le.2 = some HasBool.tt) ∧
      WellFormedSemanticEvalBool ρ_last.eval ∧
      WellFormedSemanticEvalVal ρ_last.eval ∧
      WellFormedSemanticEvalVar ρ_last.eval ∧
      ρ_last.hasFailure = Bool.false ∧
      CoreStar π φ (.stmts body ρ_last) (.exiting .none ρ') ∧
      ρ_last.eval = ρ₀.eval) := by
  -- Convert to ReflTransT and use strong induction on trace length
  have hloopT := reflTrans_to_T hloop
  suffices ∀ (n : Nat) (ρ₀ : Env Expression),
      ρ₀.eval ρ₀.store g = some HasBool.tt →
      (∀ le ∈ inv, ρ₀.eval ρ₀.store le.2 = some HasBool.tt) →
      WellFormedSemanticEvalBool ρ₀.eval →
      WellFormedSemanticEvalVal ρ₀.eval →
      WellFormedSemanticEvalVar ρ₀.eval →
      ∀ (hstarT : ReflTransT (StepStmt Expression (EvalCommand π φ) (EvalPureFunc φ))
          (.stmt (.loop (.det g) measure inv body md) ρ₀) (.terminal ρ')),
        hstarT.len ≤ n →
      (∃ ρ_pre ρ_post,
        ρ_pre.eval ρ_pre.store g = some HasBool.tt ∧
        (∀ le ∈ inv, ρ_pre.eval ρ_pre.store le.2 = some HasBool.tt) ∧
        WellFormedSemanticEvalBool ρ_pre.eval ∧
        WellFormedSemanticEvalVal ρ_pre.eval ∧
        WellFormedSemanticEvalVar ρ_pre.eval ∧
        ρ_pre.hasFailure = Bool.false ∧
        CoreStar π φ (.stmts body ρ_pre) (.terminal ρ_post) ∧
        ρ_post.hasFailure = Bool.false ∧
        (∃ le ∈ inv, ρ_post.eval ρ_post.store le.2 = some HasBool.ff) ∧
        ρ_pre.eval = ρ₀.eval)
      ∨
      (∃ ρ_last,
        ρ_last.eval ρ_last.store g = some HasBool.tt ∧
        (∀ le ∈ inv, ρ_last.eval ρ_last.store le.2 = some HasBool.tt) ∧
        WellFormedSemanticEvalBool ρ_last.eval ∧
        WellFormedSemanticEvalVal ρ_last.eval ∧
        WellFormedSemanticEvalVar ρ_last.eval ∧
        ρ_last.hasFailure = Bool.false ∧
        CoreStar π φ (.stmts body ρ_last) (.terminal ρ') ∧
        (∀ le ∈ inv, ρ'.eval ρ'.store le.2 = some HasBool.tt) ∧
        ρ_last.eval = ρ₀.eval)
      ∨
      (∃ ρ_last,
        ρ_last.eval ρ_last.store g = some HasBool.tt ∧
        (∀ le ∈ inv, ρ_last.eval ρ_last.store le.2 = some HasBool.tt) ∧
        WellFormedSemanticEvalBool ρ_last.eval ∧
        WellFormedSemanticEvalVal ρ_last.eval ∧
        WellFormedSemanticEvalVar ρ_last.eval ∧
        ρ_last.hasFailure = Bool.false ∧
        CoreStar π φ (.stmts body ρ_last) (.exiting .none ρ') ∧
        ρ_last.eval = ρ₀.eval) by
    exact this hloopT.len ρ₀ hguard_tt hall_tt hwfb hwfv hwfvar hloopT (Nat.le_refl _)
  intro n
  induction n with
  | zero =>
    intro ρ₀ _ _ _ _ _ hstarT hlen
    match hstarT, hlen with
    | .step _ _ _ _ _, hlen => simp [ReflTransT.len] at hlen
  | succ n ih =>
    intro ρ₀ hguard_tt₀ hall_tt₀ hwfb₀ hwfv₀ hwfvar₀ hstarT hlen
    match hstarT, hlen with
    | .step _ _ _ (@StepStmt.step_loop_exit _ _ _ _ _ _ _ _ _ _ _ _
        hasInvFailure hg_ff _ _ _) _, _ =>
      exfalso; rw [hguard_tt₀] at hg_ff; cases hg_ff
    | .step _ _ _ (@StepStmt.step_loop_enter _ _ _ _ _ _ _ _ _ _ _ _
        hasInvFailure hg_tt hinv_bool hff_iff _) hrest, hlen =>
      -- hasInvFailure is false by backwards monotonicity from hnf
      have hnf_start : (ρ₀.hasFailure || hasInvFailure) = Bool.false := by
        have hrest_prop := reflTransT_to_prop hrest
        exact hasFailure_false_backwards (π := π) (φ := φ) hrest_prop hnf
      have hnf₀ : ρ₀.hasFailure = Bool.false := by
        cases h : ρ₀.hasFailure
        · rfl
        · simp [h, Bool.true_or] at hnf_start
      have hnif : hasInvFailure = Bool.false :=
        loop_step_hasInvFailure_false_of_or hnf_start
      subst hnif
      have hρ₀_eq :
          ({ ρ₀ with hasFailure := ρ₀.hasFailure || Bool.false } : Env Expression) = ρ₀ := by
        cases ρ₀; simp [Bool.or_false]
      -- Unwrap block .none: inner reached terminal or exiting .none
      match blockT_none_reaches_terminal (π := π) (φ := φ) hrest with
      | .inl ⟨hrestInner, hlen_inner⟩ =>
        -- Inner reached terminal: decompose body ++ [loop]
        have ⟨ρ₁, hbody, hloop_stmtT, hlen_dec⟩ :=
          stmtsT_append_terminal_noCov π φ body (.loop (.det g) measure inv body md) _ ρ'
            hrestInner
        have hbody' : CoreStar π φ (.stmts body ρ₀) (.terminal ρ₁) :=
          hρ₀_eq ▸ hbody
        have heval_eq : ρ₁.eval = ρ₀.eval :=
          smallStep_noFuncDecl_preserves_eval_block Expression (EvalCommand π φ) (EvalPureFunc φ)
            body ρ₀ ρ₁ hnofd hbody'
        have hwfb₁ : WellFormedSemanticEvalBool ρ₁.eval := heval_eq ▸ hwfb₀
        have hwfv₁ : WellFormedSemanticEvalVal ρ₁.eval := heval_eq ▸ hwfv₀
        have hwfvar₁ : WellFormedSemanticEvalVar ρ₁.eval := heval_eq ▸ hwfvar₀
        have hnf₁ : ρ₁.hasFailure = Bool.false :=
          hasFailure_false_backwards (π := π) (φ := φ) (reflTransT_to_prop hloop_stmtT) hnf
        have hloop_len : hloop_stmtT.len ≤ n := by
          have h1 : hloop_stmtT.len < hrestInner.len := hlen_dec
          have h2 : hrestInner.len < hrest.len := hlen_inner
          have h3 : hrest.len ≤ n := by
            simp [ReflTransT.len] at hlen; omega
          omega
        -- Case split on the loop at ρ₁: exit or enter
        match hloop_stmtT, hloop_len with
        | .step _ _ _ (@StepStmt.step_loop_exit _ _ _ _ _ _ _ _ _ _ _ _
            hasInvFailure₁ hg_ff₁ hinv_bool₁ hff_iff₁ _) hrest₁, _ =>
          -- Guard ff at ρ₁: last iteration. ρ₀ is ρ_last.
          have hρ'_eq_raw :
              ρ' = { ρ₁ with hasFailure := ρ₁.hasFailure || hasInvFailure₁ } := by
            match hrest₁ with
            | .refl _ => rfl
            | .step _ _ _ h _ => cases h
          have hnf_or₁ : (ρ₁.hasFailure || hasInvFailure₁) = Bool.false := by
            have : ρ'.hasFailure = (ρ₁.hasFailure || hasInvFailure₁) := by
              rw [hρ'_eq_raw]
            rw [← this]; exact hnf
          have hnif₁ : hasInvFailure₁ = Bool.false :=
            loop_step_hasInvFailure_false_of_or hnf_or₁
          have hall_tt₁ := all_inv_tt_of_hasInvFailure_false hinv_bool₁ hff_iff₁ hnif₁
          subst hnif₁
          have hρ'_eq : ρ' = ρ₁ := by rw [hρ'_eq_raw]; cases ρ₁; simp [Bool.or_false]
          subst hρ'_eq
          exact .inr (.inl ⟨ρ₀, hguard_tt₀, hall_tt₀, hwfb₀, hwfv₀, hwfvar₀, hnf₀,
            hbody', hall_tt₁, rfl⟩)
        | .step _ _ _ (@StepStmt.step_loop_enter _ _ _ _ _ _ _ _ _ _ _ _
            hasInvFailure₁ hg_tt₁ hinv_bool₁ hff_iff₁ _) hrest₁, hloop_len =>
          -- Guard tt at ρ₁: recurse
          have hnf_start₁ : (ρ₁.hasFailure || hasInvFailure₁) = Bool.false :=
            hasFailure_false_backwards (π := π) (φ := φ) (reflTransT_to_prop hrest₁) hnf
          have hnif₁ : hasInvFailure₁ = Bool.false :=
            loop_step_hasInvFailure_false_of_or hnf_start₁
          have hall_tt₁ := all_inv_tt_of_hasInvFailure_false hinv_bool₁ hff_iff₁ hnif₁
          have ih_result := ih ρ₁ hg_tt₁ hall_tt₁ hwfb₁ hwfv₁ hwfvar₁
            (.step _ _ _ (.step_loop_enter hg_tt₁ hinv_bool₁ hff_iff₁ ‹_›) hrest₁)
            hloop_len
          -- Adjust ρ_pre.eval = ρ₁.eval to ρ_pre.eval = ρ₀.eval via heval_eq
          cases ih_result with
          | inl hviolation =>
            obtain ⟨ρ_pre, ρ_post, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := hviolation
            exact .inl ⟨ρ_pre, ρ_post, h1, h2, h3, h4, h5, h6, h7, h8, h9,
              h10.trans heval_eq⟩
          | inr hsuccess =>
            cases hsuccess with
            | inl hsuccess =>
              obtain ⟨ρ_last, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := hsuccess
              exact .inr (.inl ⟨ρ_last, h1, h2, h3, h4, h5, h6, h7, h8,
                h9.trans heval_eq⟩)
            | inr hbreak =>
              obtain ⟨ρ_last, h1, h2, h3, h4, h5, h6, h7, h8⟩ := hbreak
              exact .inr (.inr ⟨ρ_last, h1, h2, h3, h4, h5, h6, h7,
                h8.trans heval_eq⟩)
      | .inr ⟨hrestExit, _⟩ =>
        -- Inner reached .exiting .none: break from body in this iteration.
        -- Extract body exiting from stmts (body ++ [loop]) exiting .none.
        have hrest_exit_prop : CoreStar π φ
            (.stmts (body ++ [.loop (.det g) measure inv body md])
              { ρ₀ with hasFailure := ρ₀.hasFailure || Bool.false })
            (.exiting .none ρ') := reflTransT_to_prop hrestExit
        have hrest_exit_ρ₀ : CoreStar π φ
            (.stmts (body ++ [.loop (.det g) measure inv body md]) ρ₀)
            (.exiting .none ρ') := hρ₀_eq ▸ hrest_exit_prop
        have hbody_exit : CoreStar π φ (.stmts body ρ₀) (.exiting .none ρ') := by
          -- By induction on body: stmts (pfx ++ [loop]) exiting .none implies
          -- stmts pfx exiting .none (loop can't produce .exiting .none).
          suffices ∀ (pfx : Statements) (ρ_cur : Env Expression),
              CoreStar π φ (.stmts (pfx ++ [.loop (.det g) measure inv body md]) ρ_cur)
                (.exiting .none ρ') →
              CoreStar π φ (.stmts pfx ρ_cur) (.exiting .none ρ') by
            exact this body ρ₀ hrest_exit_ρ₀
          intro pfx
          induction pfx with
          | nil =>
            intro ρ_cur hstar_nil
            exfalso
            have h_nil_eq : ([] : Statements) ++ [Stmt.loop (.det g) measure inv body md] =
                [Stmt.loop (.det g) measure inv body md] := rfl
            rw [h_nil_eq] at hstar_nil
            match hstar_nil with
            | .step _ _ _ .step_stmts_cons hrest_seq =>
              match seq_reaches_exiting Expression (EvalCommand π φ) (EvalPureFunc φ) hrest_seq with
              | .inl hloop_exit =>
                -- .stmt (.loop ...) →* .exiting .none ρ': show impossible
                exact loop_det_cannot_exit_none π φ g measure inv body md ρ_cur ρ' hloop_exit
              | .inr ⟨ρ_mid, _, hnil_exit⟩ =>
                -- stmts [] ρ_mid →* .exiting .none ρ': impossible
                match hnil_exit with
                | .step _ _ _ .step_stmts_nil hrest_nil =>
                  match hrest_nil with
                  | .step _ _ _ h _ => cases h
          | cons s rest ih_pfx =>
            intro ρ_cur hstar_cons
            have h_eq : (s :: rest) ++ [Stmt.loop (.det g) measure inv body md] =
                s :: (rest ++ [Stmt.loop (.det g) measure inv body md]) := rfl
            rw [h_eq] at hstar_cons
            match hstar_cons with
            | .step _ _ _ .step_stmts_cons hrest_seq =>
              match seq_reaches_exiting Expression (EvalCommand π φ) (EvalPureFunc φ) hrest_seq with
              | .inl hstmt_exit =>
                exact stmts_cons_exiting π φ s rest .none ρ_cur ρ' hstmt_exit
              | .inr ⟨ρ_mid, hstmt_term, hrest_exit⟩ =>
                exact ReflTrans_Transitive _ _ _ _
                  (stmts_cons_step Expression (EvalCommand π φ) (EvalPureFunc φ)
                    s rest ρ_cur ρ_mid hstmt_term)
                  (ih_pfx ρ_mid hrest_exit)
        exact .inr (.inr ⟨ρ₀, hguard_tt₀, hall_tt₀, hwfb₀, hwfv₀, hwfvar₀, hnf₀,
          hbody_exit, rfl⟩)

/-- Nondet version of `loop_invariant_dichotomy_det`. -/
private theorem loop_invariant_dichotomy_nondet
    (hwf_ext : WFEvalExtension φ)
    (measure : Option Expression.Expr)
    (inv : List (String × Expression.Expr))
    (body : Statements) (md : MetaData Expression)
    (ρ₀ ρ' : Env Expression)
    (hall_tt : ∀ le ∈ inv, ρ₀.eval ρ₀.store le.2 = some HasBool.tt)
    (hwfb : WellFormedSemanticEvalBool ρ₀.eval)
    (hwfv : WellFormedSemanticEvalVal ρ₀.eval)
    (hwfvar : WellFormedSemanticEvalVar ρ₀.eval)
    (hnofd : Block.noFuncDecl body = Bool.true)
    (hnf : ρ'.hasFailure = Bool.false)
    (hloop : CoreStar π φ
      (.stmt (.loop .nondet measure inv body md) ρ₀) (.terminal ρ'))
    -- The loop enters at least once (first step is step_loop_nondet_enter).
    (henter : CoreStar π φ
      (.block .none (.stmts (body ++ [.loop .nondet measure inv body md]) ρ₀))
      (.terminal ρ')) :
    (∃ ρ_pre ρ_post,
      (∀ le ∈ inv, ρ_pre.eval ρ_pre.store le.2 = some HasBool.tt) ∧
      WellFormedSemanticEvalBool ρ_pre.eval ∧
      WellFormedSemanticEvalVal ρ_pre.eval ∧
      WellFormedSemanticEvalVar ρ_pre.eval ∧
      ρ_pre.hasFailure = Bool.false ∧
      CoreStar π φ (.stmts body ρ_pre) (.terminal ρ_post) ∧
      ρ_post.hasFailure = Bool.false ∧
      (∃ le ∈ inv, ρ_post.eval ρ_post.store le.2 = some HasBool.ff) ∧
      ρ_pre.eval = ρ₀.eval)
    ∨
    (∃ ρ_last,
      (∀ le ∈ inv, ρ_last.eval ρ_last.store le.2 = some HasBool.tt) ∧
      WellFormedSemanticEvalBool ρ_last.eval ∧
      WellFormedSemanticEvalVal ρ_last.eval ∧
      WellFormedSemanticEvalVar ρ_last.eval ∧
      ρ_last.hasFailure = Bool.false ∧
      CoreStar π φ (.stmts body ρ_last) (.terminal ρ') ∧
      (∀ le ∈ inv, ρ'.eval ρ'.store le.2 = some HasBool.tt) ∧
      ρ_last.eval = ρ₀.eval)
    ∨
    -- Break: body exited with .none (break caught by block)
    (∃ ρ_last,
      (∀ le ∈ inv, ρ_last.eval ρ_last.store le.2 = some HasBool.tt) ∧
      WellFormedSemanticEvalBool ρ_last.eval ∧
      WellFormedSemanticEvalVal ρ_last.eval ∧
      WellFormedSemanticEvalVar ρ_last.eval ∧
      ρ_last.hasFailure = Bool.false ∧
      CoreStar π φ (.stmts body ρ_last) (.exiting .none ρ') ∧
      ρ_last.eval = ρ₀.eval) := by
  have hnf₀ : ρ₀.hasFailure = Bool.false :=
    hasFailure_false_backwards (π := π) (φ := φ) henter hnf
  -- Use ReflTransT for the block trace with strong induction on length
  have hblockT := reflTrans_to_T henter
  -- Quantify over block traces (the block .none wrapping body ++ [loop])
  suffices ∀ (n : Nat) (ρ₀ : Env Expression),
      (∀ le ∈ inv, ρ₀.eval ρ₀.store le.2 = some HasBool.tt) →
      WellFormedSemanticEvalBool ρ₀.eval →
      WellFormedSemanticEvalVal ρ₀.eval →
      WellFormedSemanticEvalVar ρ₀.eval →
      ∀ (hstarT : ReflTransT (StepStmt Expression (EvalCommand π φ) (EvalPureFunc φ))
          (.block .none (.stmts (body ++ [.loop .nondet measure inv body md]) ρ₀))
          (.terminal ρ')),
        hstarT.len ≤ n →
      (∃ ρ_pre ρ_post,
        (∀ le ∈ inv, ρ_pre.eval ρ_pre.store le.2 = some HasBool.tt) ∧
        WellFormedSemanticEvalBool ρ_pre.eval ∧
        WellFormedSemanticEvalVal ρ_pre.eval ∧
        WellFormedSemanticEvalVar ρ_pre.eval ∧
        ρ_pre.hasFailure = Bool.false ∧
        CoreStar π φ (.stmts body ρ_pre) (.terminal ρ_post) ∧
        ρ_post.hasFailure = Bool.false ∧
        (∃ le ∈ inv, ρ_post.eval ρ_post.store le.2 = some HasBool.ff) ∧
        ρ_pre.eval = ρ₀.eval)
      ∨
      (∃ ρ_last,
        (∀ le ∈ inv, ρ_last.eval ρ_last.store le.2 = some HasBool.tt) ∧
        WellFormedSemanticEvalBool ρ_last.eval ∧
        WellFormedSemanticEvalVal ρ_last.eval ∧
        WellFormedSemanticEvalVar ρ_last.eval ∧
        ρ_last.hasFailure = Bool.false ∧
        CoreStar π φ (.stmts body ρ_last) (.terminal ρ') ∧
        (∀ le ∈ inv, ρ'.eval ρ'.store le.2 = some HasBool.tt) ∧
        ρ_last.eval = ρ₀.eval)
      ∨
      (∃ ρ_last,
        (∀ le ∈ inv, ρ_last.eval ρ_last.store le.2 = some HasBool.tt) ∧
        WellFormedSemanticEvalBool ρ_last.eval ∧
        WellFormedSemanticEvalVal ρ_last.eval ∧
        WellFormedSemanticEvalVar ρ_last.eval ∧
        ρ_last.hasFailure = Bool.false ∧
        CoreStar π φ (.stmts body ρ_last) (.exiting .none ρ') ∧
        ρ_last.eval = ρ₀.eval) by
    exact this hblockT.len ρ₀ hall_tt hwfb hwfv hwfvar hblockT (Nat.le_refl _)
  intro n
  induction n with
  | zero =>
    intro ρ₀ _ _ _ _ hstarT hlen
    match hstarT, hlen with
    | .step _ _ _ _ _, hlen => simp [ReflTransT.len] at hlen
  | succ n ih =>
    intro ρ₀ hall_tt₀ hwfb₀ hwfv₀ hwfvar₀ hstarT hlen
    have hnf₀' : ρ₀.hasFailure = Bool.false :=
      hasFailure_false_backwards (π := π) (φ := φ) (reflTransT_to_prop hstarT) hnf
    -- Unwrap block .none: inner reached terminal or exiting .none
    match blockT_none_reaches_terminal (π := π) (φ := φ) hstarT with
    | .inl ⟨hrestInner, hlen_inner⟩ =>
      -- Inner reached terminal: decompose body ++ [loop]
      have ⟨ρ₁, hbody, hloop_stmtT, hlen_dec⟩ :=
        stmtsT_append_terminal_noCov π φ body (.loop .nondet measure inv body md) ρ₀ ρ'
          hrestInner
      have hbody' : CoreStar π φ (.stmts body ρ₀) (.terminal ρ₁) := hbody
      have heval_eq : ρ₁.eval = ρ₀.eval :=
        smallStep_noFuncDecl_preserves_eval_block Expression (EvalCommand π φ) (EvalPureFunc φ)
          body ρ₀ ρ₁ hnofd hbody'
      have hwfb₁ : WellFormedSemanticEvalBool ρ₁.eval := heval_eq ▸ hwfb₀
      have hwfv₁ : WellFormedSemanticEvalVal ρ₁.eval := heval_eq ▸ hwfv₀
      have hwfvar₁ : WellFormedSemanticEvalVar ρ₁.eval := heval_eq ▸ hwfvar₀
      have hnf₁ : ρ₁.hasFailure = Bool.false :=
        hasFailure_false_backwards (π := π) (φ := φ) (reflTransT_to_prop hloop_stmtT) hnf
      -- Case split on the loop at ρ₁ using the ReflTransT trace
      match hloop_stmtT with
      | .step _ _ _ (@StepStmt.step_loop_nondet_exit _ _ _ _ _ _ _ _ _ _ _
          hasInvFailure₁ hinv_bool₁ hff_iff₁) hrest₁ =>
        -- Exit: ρ₀ is the last iteration witness
        have hρ'_eq_raw :
            ρ' = { ρ₁ with hasFailure := ρ₁.hasFailure || hasInvFailure₁ } := by
          match hrest₁ with
          | .refl _ => rfl
          | .step _ _ _ h _ => cases h
        have hnf_or₁ : (ρ₁.hasFailure || hasInvFailure₁) = Bool.false := by
          have : ρ'.hasFailure = (ρ₁.hasFailure || hasInvFailure₁) := by rw [hρ'_eq_raw]
          rw [← this]; exact hnf
        have hnif₁ : hasInvFailure₁ = Bool.false :=
          loop_step_hasInvFailure_false_of_or hnf_or₁
        have hall_tt₁ := all_inv_tt_of_hasInvFailure_false hinv_bool₁ hff_iff₁ hnif₁
        subst hnif₁
        have hρ'_eq : ρ' = ρ₁ := by rw [hρ'_eq_raw]; cases ρ₁; simp [Bool.or_false]
        subst hρ'_eq
        exact .inr (.inl ⟨ρ₀, hall_tt₀, hwfb₀, hwfv₀, hwfvar₀, hnf₀', hbody',
          hall_tt₁, rfl⟩)
      | .step _ _ _ (@StepStmt.step_loop_nondet_enter _ _ _ _ _ _ _ _ _ _ _
          hasInvFailure₁ hinv_bool₁' hff_iff₁) hrest₁ =>
        -- Enter: recurse. The block trace from ρ₁ has strictly shorter length.
        have hnf_start₁ : (ρ₁.hasFailure || hasInvFailure₁) = Bool.false :=
          hasFailure_false_backwards (π := π) (φ := φ) (reflTransT_to_prop hrest₁) hnf
        have hnif₁ : hasInvFailure₁ = Bool.false :=
          loop_step_hasInvFailure_false_of_or hnf_start₁
        have hall_tt₁ := all_inv_tt_of_hasInvFailure_false hinv_bool₁' hff_iff₁ hnif₁
        subst hnif₁
        have hρ₁_eq :
            ({ ρ₁ with hasFailure := ρ₁.hasFailure || Bool.false } : Env Expression) = ρ₁ := by
          cases ρ₁; simp [Bool.or_false]
        have hrest₁_len : hrest₁.len ≤ n := by
          -- hlen_dec : (step ... hrest₁).len < hrestInner.len
          -- i.e. 1 + hrest₁.len < hrestInner.len
          have h1 : 1 + hrest₁.len < hrestInner.len := hlen_dec
          have h2 : hrestInner.len < hstarT.len := hlen_inner
          have h3 : hstarT.len ≤ n + 1 := hlen
          omega
        have ih_result := ih ρ₁ hall_tt₁ hwfb₁ hwfv₁ hwfvar₁ (hρ₁_eq ▸ hrest₁)
          (by
            suffices ∀ (ρ : Env Expression)
                (h : ReflTransT (StepStmt Expression (EvalCommand π φ) (EvalPureFunc φ))
                  (.block .none (.stmts (body ++ [.loop .nondet measure inv body md]) ρ))
                  (.terminal ρ'))
                (heq : ρ = ρ₁),
                (heq ▸ h).len = h.len by
              rw [this _ hrest₁ hρ₁_eq]; exact hrest₁_len
            intro ρ h heq; subst heq; rfl)
        cases ih_result with
        | inl hviolation =>
          obtain ⟨ρ_pre, ρ_post, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := hviolation
          exact .inl ⟨ρ_pre, ρ_post, h1, h2, h3, h4, h5, h6, h7, h8, h9.trans heval_eq⟩
        | inr hsuccess =>
          cases hsuccess with
          | inl hsuccess =>
            obtain ⟨ρ_last, h1, h2, h3, h4, h5, h6, h7, h8⟩ := hsuccess
            exact .inr (.inl ⟨ρ_last, h1, h2, h3, h4, h5, h6, h7, h8.trans heval_eq⟩)
          | inr hbreak =>
            obtain ⟨ρ_last, h1, h2, h3, h4, h5, h6, h7⟩ := hbreak
            exact .inr (.inr ⟨ρ_last, h1, h2, h3, h4, h5, h6, h7.trans heval_eq⟩)
    | .inr ⟨hrestExit, hlen_exit⟩ =>
      -- Inner reached .exiting .none: break from body in this iteration
      have hrest_exit_prop : CoreStar π φ
          (.stmts (body ++ [.loop .nondet measure inv body md]) ρ₀)
          (.exiting .none ρ') := reflTransT_to_prop hrestExit
      -- Extract body exiting from stmts (body ++ [loop]) exiting
      have hbody_exit : CoreStar π φ (.stmts body ρ₀) (.exiting .none ρ') := by
        suffices ∀ (pfx : Statements) (ρ_cur : Env Expression),
            CoreStar π φ (.stmts (pfx ++ [.loop .nondet measure inv body md]) ρ_cur)
              (.exiting .none ρ') →
            CoreStar π φ (.stmts pfx ρ_cur) (.exiting .none ρ') by
          exact this body ρ₀ hrest_exit_prop
        intro pfx
        induction pfx with
        | nil =>
          intro ρ_cur hstar_nil
          exfalso
          have h_nil_eq : ([] : Statements) ++ [Stmt.loop .nondet measure inv body md] =
              [Stmt.loop .nondet measure inv body md] := rfl
          rw [h_nil_eq] at hstar_nil
          match hstar_nil with
          | .step _ _ _ .step_stmts_cons hrest_seq =>
            match seq_reaches_exiting Expression (EvalCommand π φ) (EvalPureFunc φ) hrest_seq with
            | .inl hloop_exit =>
              exact loop_nondet_cannot_exit_none π φ measure inv body md ρ_cur ρ' hloop_exit
            | .inr ⟨_, _, hnil_exit⟩ =>
              match hnil_exit with
              | .step _ _ _ .step_stmts_nil hrest_nil =>
                match hrest_nil with
                | .step _ _ _ h _ => cases h
        | cons s rest ih_pfx =>
          intro ρ_cur hstar_cons
          have h_eq : (s :: rest) ++ [Stmt.loop .nondet measure inv body md] =
              s :: (rest ++ [Stmt.loop .nondet measure inv body md]) := rfl
          rw [h_eq] at hstar_cons
          match hstar_cons with
          | .step _ _ _ .step_stmts_cons hrest_seq =>
            match seq_reaches_exiting Expression (EvalCommand π φ) (EvalPureFunc φ) hrest_seq with
            | .inl hstmt_exit =>
              exact stmts_cons_exiting π φ s rest .none ρ_cur ρ' hstmt_exit
            | .inr ⟨ρ_mid, hstmt_term, hrest_exit⟩ =>
              exact ReflTrans_Transitive _ _ _ _
                (stmts_cons_step Expression (EvalCommand π φ) (EvalPureFunc φ)
                  s rest ρ_cur ρ_mid hstmt_term)
                (ih_pfx ρ_mid hrest_exit)
      exact .inr (.inr ⟨ρ₀, hall_tt₀, hwfb₀, hwfv₀, hwfvar₀, hnf₀',
        hbody_exit, rfl⟩)

/-! ## Store definedness from source execution -/

/-- If the source body reaches terminal (or exiting) from ρ₀, then every variable
    in `assigned_vars` (= modifiedVars body filtered by ∉ definedVars body) was
    already defined at ρ₀.

    The argument: if `n` is modified during execution (via UpdateState, which
    requires `σ n = some _`) but never initialized (via InitState), then `n` must
    have been defined at ρ₀.  Contrapositive: if `ρ₀.store n = none` and body
    doesn't InitState it first, UpdateState for `n` would be impossible →
    execution gets stuck → can't reach terminal/exiting.

    A full proof requires detailed trace induction over `StepStmt` constructors;
    we state it here and will fill it in a subsequent PR. -/
private theorem modifiedVars_defined_from_execution
    (body : Statements)
    (ρ₀ : Env Expression)
    (assigned_vars : List Expression.Ident)
    (hvars : assigned_vars = (Block.modifiedVars body).filter (fun v => v ∉ Block.definedVars body))
    (hreach : (∃ ρ', CoreStar π φ (.stmts body ρ₀) (.terminal ρ')) ∨
              (∃ lbl ρ', CoreStar π φ (.stmts body ρ₀) (.exiting lbl ρ'))) :
    ∀ n ∈ assigned_vars, (ρ₀.store n).isSome := by
  sorry

/-! ## Simulation -/

private theorem simulation
    (hwf_ext : WFEvalExtension φ) (sz : Nat) :
    -- Statement level
    (∀ (σ : LoopElimState) (st : Statement),
      Stmt.sizeOf st ≤ sz →
      Stmt.noFuncDecl st = Bool.true →
      ∀ (ρ₀ : Env Expression),
        WellFormedSemanticEvalBool ρ₀.eval →
        WellFormedSemanticEvalVal ρ₀.eval →
        WellFormedSemanticEvalVar ρ₀.eval →
        (∀ ρ', CoreStar π φ (.stmt st ρ₀) (.terminal ρ') →
          Transform.CanFail (LangCore π φ) (stmtResult σ st) ρ₀ ∨
          (ρ'.hasFailure = Bool.false →
            CoreStar π φ (.stmt (stmtResult σ st) ρ₀) (.terminal ρ')))
        ∧
        (∀ lbl ρ', CoreStar π φ (.stmt st ρ₀) (.exiting lbl ρ') →
          Transform.CanFail (LangCore π φ) (stmtResult σ st) ρ₀ ∨
          (ρ'.hasFailure = Bool.false →
            CoreStar π φ (.stmt (stmtResult σ st) ρ₀) (.exiting lbl ρ'))))
    ∧
    -- Block level
    (∀ (σ : LoopElimState) (bss : Statements),
      Block.sizeOf bss ≤ sz →
      Block.noFuncDecl bss = Bool.true →
      ∀ (ρ₀ : Env Expression),
        WellFormedSemanticEvalBool ρ₀.eval →
        WellFormedSemanticEvalVal ρ₀.eval →
        WellFormedSemanticEvalVar ρ₀.eval →
        (∀ ρ', CoreStar π φ (.stmts bss ρ₀) (.terminal ρ') →
          CanFailBlock π φ (blockResult σ bss) ρ₀ ∨
          (ρ'.hasFailure = Bool.false →
            CoreStar π φ (.stmts (blockResult σ bss) ρ₀) (.terminal ρ')))
        ∧
        (∀ lbl ρ', CoreStar π φ (.stmts bss ρ₀) (.exiting lbl ρ') →
          CanFailBlock π φ (blockResult σ bss) ρ₀ ∨
          (ρ'.hasFailure = Bool.false →
            CoreStar π φ (.stmts (blockResult σ bss) ρ₀) (.exiting lbl ρ'))))
    ∧
    -- Statement CanFail preservation
    (∀ (σ : LoopElimState) (st : Statement),
      Stmt.sizeOf st ≤ sz →
      Stmt.noFuncDecl st = Bool.true →
      ∀ (ρ₀ : Env Expression),
        WellFormedSemanticEvalBool ρ₀.eval →
        WellFormedSemanticEvalVal ρ₀.eval →
        WellFormedSemanticEvalVar ρ₀.eval →
        Transform.CanFail (LangCore π φ) st ρ₀ →
        Transform.CanFail (LangCore π φ) (stmtResult σ st) ρ₀)
    ∧
    -- Block CanFail preservation
    (∀ (σ : LoopElimState) (bss : Statements),
      Block.sizeOf bss ≤ sz →
      Block.noFuncDecl bss = Bool.true →
      ∀ (ρ₀ : Env Expression),
        WellFormedSemanticEvalBool ρ₀.eval →
        WellFormedSemanticEvalVal ρ₀.eval →
        WellFormedSemanticEvalVar ρ₀.eval →
        CanFailBlock π φ bss ρ₀ →
        CanFailBlock π φ (blockResult σ bss) ρ₀) := by
  induction sz with
  | zero =>
    refine ⟨fun σ st hsz _ => ?_, fun σ bss hsz _ => ?_, fun σ st hsz _ => ?_, fun σ bss hsz _ => ?_⟩
    · match st with
      | .cmd _ => exact absurd hsz (by simp [Stmt.sizeOf])
      | .block .. => exact absurd hsz (by simp [Stmt.sizeOf])
      | .ite .. => exact absurd hsz (by simp [Stmt.sizeOf])
      | .loop .. => exact absurd hsz (by simp [Stmt.sizeOf])
      | .exit .. => exact absurd hsz (by simp [Stmt.sizeOf])
      | .funcDecl .. => exact absurd hsz (by simp [Stmt.sizeOf])
      | .typeDecl .. => exact absurd hsz (by simp [Stmt.sizeOf])
    · match bss with
      | [] => exact absurd hsz (by simp [Block.sizeOf])
      | _ :: _ => exact absurd hsz (by simp [Block.sizeOf])
    · match st with
      | .cmd _ => exact absurd hsz (by simp [Stmt.sizeOf])
      | .block .. => exact absurd hsz (by simp [Stmt.sizeOf])
      | .ite .. => exact absurd hsz (by simp [Stmt.sizeOf])
      | .loop .. => exact absurd hsz (by simp [Stmt.sizeOf])
      | .exit .. => exact absurd hsz (by simp [Stmt.sizeOf])
      | .funcDecl .. => exact absurd hsz (by simp [Stmt.sizeOf])
      | .typeDecl .. => exact absurd hsz (by simp [Stmt.sizeOf])
    · match bss with
      | [] =>
        intro ρ₀ _ _ _ hcf
        rw [blockResult_nil]
        exact hcf
      | _ :: _ => exact absurd hsz (by simp [Block.sizeOf])
  | succ n ih =>
    refine ⟨?_, ?_, ?_, ?_⟩
    -- === Statement case ===
    · intro σ st hsz hnofd ρ₀ hwfb hwfv hwfvar
      match st with
      | .cmd c =>
        rw [stmtResult_cmd]
        exact ⟨fun _ hstar => .inr (fun _ => hstar),
               fun _ _ hstar => .inr (fun _ => hstar)⟩

      | .exit l md =>
        rw [stmtResult_exit]
        exact ⟨fun _ hstar => .inr (fun _ => hstar),
               fun _ _ hstar => .inr (fun _ => hstar)⟩

      | .funcDecl d md =>
        rw [stmtResult_funcDecl]
        exact ⟨fun _ hstar => .inr (fun _ => hstar),
               fun _ _ hstar => .inr (fun _ => hstar)⟩

      | .typeDecl tc md =>
        rw [stmtResult_typeDecl]
        exact ⟨fun _ hstar => .inr (fun _ => hstar),
               fun _ _ hstar => .inr (fun _ => hstar)⟩

      | .block l bss md =>
        rw [stmtResult_block]
        have hsz_bss : Block.sizeOf bss ≤ n := by
          simp [Stmt.sizeOf] at hsz; omega
        have hnofd_bss : Block.noFuncDecl bss = Bool.true := by
          simp [Stmt.noFuncDecl] at hnofd; exact hnofd
        have blk_ih := ih.2.1 σ bss hsz_bss hnofd_bss ρ₀ hwfb hwfv hwfvar
        constructor
        · intro ρ' hstar
          cases hstar with
          | step _ _ _ h1 r1 => cases h1 with
            | step_block =>
              match block_reaches_terminal_refined π φ r1 with
              | .inl hterm =>
                match blk_ih.1 ρ' hterm with
                | .inl hcf => exact .inl (canFailBlock_to_canFail_block π φ l (blockResult σ bss) md ρ₀ hcf)
                | .inr hok => exact .inr (fun hnf => block_wrap_terminal π φ l (blockResult σ bss) md ρ₀ ρ' (hok hnf))
              | .inr (.inl hexit_none) =>
                match blk_ih.2 none ρ' hexit_none with
                | .inl hcf => exact .inl (canFailBlock_to_canFail_block π φ l (blockResult σ bss) md ρ₀ hcf)
                | .inr hok => exact .inr (fun hnf => block_wrap_exiting_none π φ l (blockResult σ bss) md ρ₀ ρ' (hok hnf))
              | .inr (.inr hexit_match) =>
                match blk_ih.2 (some l) ρ' hexit_match with
                | .inl hcf => exact .inl (canFailBlock_to_canFail_block π φ l (blockResult σ bss) md ρ₀ hcf)
                | .inr hok => exact .inr (fun hnf => block_wrap_exiting_match π φ l (blockResult σ bss) md ρ₀ ρ' (hok hnf))
        · intro lbl ρ' hstar
          cases hstar with
          | step _ _ _ h1 r1 => cases h1 with
            | step_block =>
              have ⟨lv, hne, hlbl_eq, hexit⟩ := block_reaches_exiting_refined π φ r1
              subst hlbl_eq
              match blk_ih.2 (some lv) ρ' hexit with
              | .inl hcf => exact .inl (canFailBlock_to_canFail_block π φ l (blockResult σ bss) md ρ₀ hcf)
              | .inr hok => exact .inr (fun hnf => block_wrap_exiting_mismatch π φ l (blockResult σ bss) md lv ρ₀ ρ' hne (hok hnf))

      | .ite c tss ess md =>
        rw [stmtResult_ite]
        have hsz_tss : Block.sizeOf tss ≤ n := by
          simp [Stmt.sizeOf] at hsz; omega
        have hsz_ess : Block.sizeOf ess ≤ n := by
          simp [Stmt.sizeOf] at hsz; omega
        have hnofd_tss : Block.noFuncDecl tss = Bool.true := by
          simp [Stmt.noFuncDecl, Bool.and_eq_true] at hnofd; exact hnofd.1
        have hnofd_ess : Block.noFuncDecl ess = Bool.true := by
          simp [Stmt.noFuncDecl, Bool.and_eq_true] at hnofd; exact hnofd.2
        constructor
        · intro ρ' hstar
          cases hstar with
          | step _ _ _ h1 r1 => cases h1 with
            | step_ite_true hcond hwfb' =>
              match (ih.2.1 σ tss hsz_tss hnofd_tss ρ₀ hwfb hwfv hwfvar).1 ρ' r1 with
              | .inl hcf =>
                left; obtain ⟨cfg, hfail, hreach⟩ := hcf
                exact ⟨cfg, hfail, ReflTrans_Transitive _ _ _ _ (.step _ _ _ (.step_ite_true hcond hwfb') (.refl _)) hreach⟩
              | .inr hok => exact .inr (fun hnf => .step _ _ _ (.step_ite_true hcond hwfb') (hok hnf))
            | step_ite_false hcond hwfb' =>
              match (ih.2.1 (blockPostState σ tss) ess hsz_ess hnofd_ess ρ₀ hwfb hwfv hwfvar).1 ρ' r1 with
              | .inl hcf =>
                left; obtain ⟨cfg, hfail, hreach⟩ := hcf
                exact ⟨cfg, hfail, ReflTrans_Transitive _ _ _ _ (.step _ _ _ (.step_ite_false hcond hwfb') (.refl _)) hreach⟩
              | .inr hok => exact .inr (fun hnf => .step _ _ _ (.step_ite_false hcond hwfb') (hok hnf))
            | step_ite_nondet_true =>
              match (ih.2.1 σ tss hsz_tss hnofd_tss ρ₀ hwfb hwfv hwfvar).1 ρ' r1 with
              | .inl hcf =>
                left; obtain ⟨cfg, hfail, hreach⟩ := hcf
                exact ⟨cfg, hfail, ReflTrans_Transitive _ _ _ _ (.step _ _ _ .step_ite_nondet_true (.refl _)) hreach⟩
              | .inr hok => exact .inr (fun hnf => .step _ _ _ .step_ite_nondet_true (hok hnf))
            | step_ite_nondet_false =>
              match (ih.2.1 (blockPostState σ tss) ess hsz_ess hnofd_ess ρ₀ hwfb hwfv hwfvar).1 ρ' r1 with
              | .inl hcf =>
                left; obtain ⟨cfg, hfail, hreach⟩ := hcf
                exact ⟨cfg, hfail, ReflTrans_Transitive _ _ _ _ (.step _ _ _ .step_ite_nondet_false (.refl _)) hreach⟩
              | .inr hok => exact .inr (fun hnf => .step _ _ _ .step_ite_nondet_false (hok hnf))
        · intro lbl ρ' hstar
          cases hstar with
          | step _ _ _ h1 r1 => cases h1 with
            | step_ite_true hcond hwfb' =>
              match (ih.2.1 σ tss hsz_tss hnofd_tss ρ₀ hwfb hwfv hwfvar).2 lbl ρ' r1 with
              | .inl hcf =>
                left; obtain ⟨cfg, hfail, hreach⟩ := hcf
                exact ⟨cfg, hfail, ReflTrans_Transitive _ _ _ _ (.step _ _ _ (.step_ite_true hcond hwfb') (.refl _)) hreach⟩
              | .inr hok => exact .inr (fun hnf => .step _ _ _ (.step_ite_true hcond hwfb') (hok hnf))
            | step_ite_false hcond hwfb' =>
              match (ih.2.1 (blockPostState σ tss) ess hsz_ess hnofd_ess ρ₀ hwfb hwfv hwfvar).2 lbl ρ' r1 with
              | .inl hcf =>
                left; obtain ⟨cfg, hfail, hreach⟩ := hcf
                exact ⟨cfg, hfail, ReflTrans_Transitive _ _ _ _ (.step _ _ _ (.step_ite_false hcond hwfb') (.refl _)) hreach⟩
              | .inr hok => exact .inr (fun hnf => .step _ _ _ (.step_ite_false hcond hwfb') (hok hnf))
            | step_ite_nondet_true =>
              match (ih.2.1 σ tss hsz_tss hnofd_tss ρ₀ hwfb hwfv hwfvar).2 lbl ρ' r1 with
              | .inl hcf =>
                left; obtain ⟨cfg, hfail, hreach⟩ := hcf
                exact ⟨cfg, hfail, ReflTrans_Transitive _ _ _ _ (.step _ _ _ .step_ite_nondet_true (.refl _)) hreach⟩
              | .inr hok => exact .inr (fun hnf => .step _ _ _ .step_ite_nondet_true (hok hnf))
            | step_ite_nondet_false =>
              match (ih.2.1 (blockPostState σ tss) ess hsz_ess hnofd_ess ρ₀ hwfb hwfv hwfvar).2 lbl ρ' r1 with
              | .inl hcf =>
                left; obtain ⟨cfg, hfail, hreach⟩ := hcf
                exact ⟨cfg, hfail, ReflTrans_Transitive _ _ _ _ (.step _ _ _ .step_ite_nondet_false (.refl _)) hreach⟩
              | .inr hok => exact .inr (fun hnf => .step _ _ _ .step_ite_nondet_false (hok hnf))

      | .loop guard measure inv body md =>
        have ⟨ll, fil, fib, tb, heq_stmt, heq_fib⟩ :=
          stmtResult_loop_struct σ guard measure inv body md
        have hsz_body : Block.sizeOf body ≤ n := by
          simp [Stmt.sizeOf] at hsz; omega
        have hnofd_body : Block.noFuncDecl body = Bool.true := by
          simp [Stmt.noFuncDecl] at hnofd; exact hnofd
        constructor
        · intro ρ' hstar
          by_cases hnf : ρ'.hasFailure = Bool.false
          · -- Source loop reaches terminal ρ' with hasFailure = false
            rw [heq_stmt]
            let mkAssertLbl : Nat → String → String := fun i lbl =>
              s!"{loopElimAssertPrefix}{(StringGenState.gen "loop" σ.gen).fst}_entry_invariant_{if lbl.isEmpty then toString i else s!"{i}_{lbl}"}"
            let mkAssumeLbl : Nat → String → String := fun i lbl =>
              s!"{loopElimAssumePrefix}{(StringGenState.gen "loop" σ.gen).fst}_entry_invariant_{if lbl.isEmpty then toString i else s!"{i}_{lbl}"}"
            cases hstar with
            | step _ _ _ h1 r1 => cases h1 with
              | step_loop_exit hguard_ff hinv_eval hff_iff hwfb' =>
                -- 0-iteration det case: guard is ff, loop exits immediately
                rename_i hasInvFailure
                cases r1 with
                | refl =>
                  -- After refl: ρ' unified with {ρ₀ with hasFailure := ρ₀.hasFailure || hasInvFailure}
                  -- hnf tells us this has hasFailure = false
                  have hnif : hasInvFailure = Bool.false := loop_step_hasInvFailure_false_of_or hnf
                  have hall_tt := all_inv_tt_of_hasInvFailure_false hinv_eval hff_iff hnif
                  -- After subst, the target env is ρ₀
                  suffices h : Transform.CanFail (LangCore π φ)
                      (.block ll [.block fil fib {}, .ite (.det _) tb [] {}] {}) ρ₀ ∨
                    (({ ρ₀ with hasFailure := ρ₀.hasFailure || hasInvFailure } : Env Expression).hasFailure = Bool.false →
                      CoreStar π φ (.stmt (.block ll [.block fil fib {}, .ite (.det _) tb [] {}] {}) ρ₀)
                        (.terminal { ρ₀ with hasFailure := ρ₀.hasFailure || hasInvFailure })) by exact h
                  have henv_eq : ({ ρ₀ with hasFailure := ρ₀.hasFailure || hasInvFailure } : Env Expression) = ρ₀ := by
                    rw [hnif]; exact env_or_false_eq ρ₀
                  rw [henv_eq]
                  have hnf₀ : ρ₀.hasFailure = Bool.false := by rw [← henv_eq]; exact hnf
                  have hfib_term : CoreStar π φ (.stmts fib ρ₀) (.terminal ρ₀) := by
                    rw [heq_fib]
                    exact ReflTrans_Transitive _ _ _ _
                      (stmts_prefix_terminal_append Expression (EvalCommand π φ) (EvalPureFunc φ) _ _ ρ₀ ρ₀
                        (stmts_mapIdx_assert_terminal π φ inv ρ₀ md mkAssertLbl hwfb hall_tt))
                      (stmts_mapIdx_assume_terminal π φ inv ρ₀ md mkAssumeLbl hwfb hall_tt)
                  have hfirst_iter_term := block_wrap_terminal π φ fil fib {} ρ₀ ρ₀ hfib_term
                  have hite_term : CoreStar π φ (.stmt (.ite (.det _) tb [] {}) ρ₀) (.terminal ρ₀) :=
                    .step _ _ _ (.step_ite_false hguard_ff hwfb')
                      (.step _ _ _ .step_stmts_nil (.refl _))
                  have hinner := ReflTrans_Transitive _ _ _ _
                    (stmts_cons_step Expression (EvalCommand π φ) (EvalPureFunc φ)
                      (.block fil fib {}) [.ite (.det _) tb [] {}] ρ₀ ρ₀ hfirst_iter_term)
                    (ReflTrans_Transitive _ _ _ _
                      (.step _ _ _ .step_stmts_cons (.refl _))
                      (ReflTrans_Transitive _ _ _ _
                        (seq_inner_star Expression (EvalCommand π φ) (EvalPureFunc φ) _ _ [] hite_term)
                        (.step _ _ _ .step_seq_done (.step _ _ _ .step_stmts_nil (.refl _)))))
                  exact .inr (fun _ => block_wrap_terminal π φ ll _ {} ρ₀ ρ₀ hinner)
                | step _ _ _ h2 _ => cases h2
              | step_loop_enter hguard_tt hinv_eval hff_iff hwfb' =>
                rename_i hasInvFailure
                have hnf_start : (ρ₀.hasFailure || hasInvFailure) = Bool.false :=
                  hasFailure_false_backwards (π := π) (φ := φ) r1 hnf
                have hnif : hasInvFailure = Bool.false :=
                  loop_step_hasInvFailure_false_of_or hnf_start
                have hnf₀ : ρ₀.hasFailure = Bool.false := by
                  cases h : ρ₀.hasFailure <;> simp_all
                have hall_tt := all_inv_tt_of_hasInvFailure_false hinv_eval hff_iff hnif
                have henv_eq :
                    ({ ρ₀ with hasFailure := ρ₀.hasFailure || hasInvFailure } : Env Expression) = ρ₀ := by
                  rw [hnif]; exact env_or_false_eq ρ₀
                have _hsz_body : Block.sizeOf body ≤ n := by
                  simp [Stmt.sizeOf] at hsz; omega
                -- Terminal det enter: source terminates at ρ' with hasFailure=false.
                -- The full simulation requires loop_invariant_dichotomy + target trace
                -- construction through the then-branch (havoc → assume → body' →
                -- maintain_invariants → exit_state). This needs noFuncDecl (to ensure
                -- eval consistency) and store definedness (for havoc).
                sorry
              | step_loop_nondet_exit hinv_eval hff_iff =>
                -- 0-iteration nondet case
                rename_i hasInvFailure_nd
                cases r1 with
                | refl =>
                  have hnif : hasInvFailure_nd = Bool.false := loop_step_hasInvFailure_false_of_or hnf
                  have hall_tt := all_inv_tt_of_hasInvFailure_false hinv_eval hff_iff hnif
                  suffices h : Transform.CanFail (LangCore π φ)
                      (.block ll [.block fil fib {}, .ite .nondet tb [] {}] {}) ρ₀ ∨
                    (({ ρ₀ with hasFailure := ρ₀.hasFailure || hasInvFailure_nd } : Env Expression).hasFailure = Bool.false →
                      CoreStar π φ (.stmt (.block ll [.block fil fib {}, .ite .nondet tb [] {}] {}) ρ₀)
                        (.terminal { ρ₀ with hasFailure := ρ₀.hasFailure || hasInvFailure_nd })) by exact h
                  have henv_eq : ({ ρ₀ with hasFailure := ρ₀.hasFailure || hasInvFailure_nd } : Env Expression) = ρ₀ := by
                    rw [hnif]; exact env_or_false_eq ρ₀
                  rw [henv_eq]
                  have hnf₀ : ρ₀.hasFailure = Bool.false := by rw [← henv_eq]; exact hnf
                  have hfib_term : CoreStar π φ (.stmts fib ρ₀) (.terminal ρ₀) := by
                    rw [heq_fib]
                    exact ReflTrans_Transitive _ _ _ _
                      (stmts_prefix_terminal_append Expression (EvalCommand π φ) (EvalPureFunc φ) _ _ ρ₀ ρ₀
                        (stmts_mapIdx_assert_terminal π φ inv ρ₀ md mkAssertLbl hwfb hall_tt))
                      (stmts_mapIdx_assume_terminal π φ inv ρ₀ md mkAssumeLbl hwfb hall_tt)
                  have hfirst_iter_term := block_wrap_terminal π φ fil fib {} ρ₀ ρ₀ hfib_term
                  have hite_term : CoreStar π φ (.stmt (.ite .nondet tb [] {}) ρ₀) (.terminal ρ₀) :=
                    .step _ _ _ .step_ite_nondet_false
                      (.step _ _ _ .step_stmts_nil (.refl _))
                  have hinner := ReflTrans_Transitive _ _ _ _
                    (stmts_cons_step Expression (EvalCommand π φ) (EvalPureFunc φ)
                      (.block fil fib {}) [.ite .nondet tb [] {}] ρ₀ ρ₀ hfirst_iter_term)
                    (ReflTrans_Transitive _ _ _ _
                      (.step _ _ _ .step_stmts_cons (.refl _))
                      (ReflTrans_Transitive _ _ _ _
                        (seq_inner_star Expression (EvalCommand π φ) (EvalPureFunc φ) _ _ [] hite_term)
                        (.step _ _ _ .step_seq_done (.step _ _ _ .step_stmts_nil (.refl _)))))
                  exact .inr (fun _ => block_wrap_terminal π φ ll _ {} ρ₀ ρ₀ hinner)
                | step _ _ _ h2 _ => cases h2
              | step_loop_nondet_enter hinv_eval hff_iff =>
                rename_i hasInvFailure_nd
                have hnf_start : (ρ₀.hasFailure || hasInvFailure_nd) = Bool.false :=
                  hasFailure_false_backwards (π := π) (φ := φ) r1 hnf
                have hnif : hasInvFailure_nd = Bool.false :=
                  loop_step_hasInvFailure_false_of_or hnf_start
                have hnf₀ : ρ₀.hasFailure = Bool.false := by
                  cases h : ρ₀.hasFailure <;> simp_all
                have hall_tt := all_inv_tt_of_hasInvFailure_false hinv_eval hff_iff hnif
                have henv_eq :
                    ({ ρ₀ with hasFailure := ρ₀.hasFailure || hasInvFailure_nd } : Env Expression) = ρ₀ := by
                  rw [hnif]; exact env_or_false_eq ρ₀
                -- Terminal nondet enter: same structure needed as det enter.
                sorry
          · exact .inr (fun h => absurd h hnf)
        · intro lbl ρ' hstar
          -- Source loop reaches exiting lbl ρ'. Only possible via enter.
          rw [heq_stmt]
          cases hstar with
          | step _ _ _ h1 r1 => cases h1 with
            | step_loop_exit _ _ _ _ => cases r1 with | step _ _ _ h2 _ => cases h2
            | step_loop_enter hguard_tt hinv_eval hff_iff hwfb' =>
              -- Exiting det enter: source loop body exits with label.
              -- Need to route through target: first_iter → ite → arb_iter_facts → body' exits.
              sorry
            | step_loop_nondet_exit _ _ => cases r1 with | step _ _ _ h2 _ => cases h2
            | step_loop_nondet_enter hinv_eval hff_iff =>
              -- Exiting nondet enter: same structure as det enter.
              sorry

    -- === Block case ===
    · intro σ bss hsz hnofd_blk ρ₀ hwfb hwfv hwfvar
      match bss with
      | [] =>
        rw [blockResult_nil]
        exact ⟨fun _ hstar => .inr (fun _ => hstar),
               fun _ _ hstar => .inr (fun _ => hstar)⟩
      | s :: ss =>
        rw [blockResult_cons]
        have hsz_s : Stmt.sizeOf s ≤ n := by
          simp [Block.sizeOf] at hsz; omega
        have hsz_ss : Block.sizeOf ss ≤ n := by
          simp [Block.sizeOf] at hsz; omega
        have hnofd_s : Stmt.noFuncDecl s = Bool.true := by
          simp [Block.noFuncDecl, Bool.and_eq_true] at hnofd_blk; exact hnofd_blk.1
        have hnofd_ss : Block.noFuncDecl ss = Bool.true := by
          simp [Block.noFuncDecl, Bool.and_eq_true] at hnofd_blk; exact hnofd_blk.2
        constructor
        · intro ρ' hstar
          cases hstar with
          | step _ _ _ h1 r1 => cases h1 with
            | step_stmts_cons =>
              have ⟨ρ₁, hterm_s, hterm_ss⟩ := seq_reaches_terminal Expression (EvalCommand π φ) (EvalPureFunc φ) r1
              have s_ih := ih.1 σ s hsz_s hnofd_s ρ₀ hwfb hwfv hwfvar
              match s_ih.1 ρ₁ hterm_s with
              | .inl hcf =>
                exact .inl (canFail_head_to_block π φ (stmtResult σ s) (blockResult (stmtPostState σ s) ss) ρ₀ hcf)
              | .inr hok_s =>
                have hwfb₁ := star_preserves_wf (π := π) (φ := φ) hwf_ext hterm_s hwfb
                have hwfv₁ := star_preserves_wfVal (π := π) (φ := φ) hwf_ext hterm_s hwfv
                have hwfvar₁ := star_preserves_wfVar (π := π) (φ := φ) hwf_ext hterm_s hwfvar
                have ss_ih := ih.2.1 (stmtPostState σ s) ss hsz_ss hnofd_ss ρ₁ hwfb₁ hwfv₁ hwfvar₁
                match ss_ih.1 ρ' hterm_ss with
                | .inl hcf =>
                  by_cases hnf₁ : ρ₁.hasFailure = Bool.false
                  · exact .inl (canFail_tail_to_block π φ (stmtResult σ s)
                      (blockResult (stmtPostState σ s) ss) ρ₀ ρ₁ (hok_s hnf₁) hcf)
                  · exact .inr (fun hnf_final => by
                      have : ρ₁.hasFailure = Bool.false :=
                        hasFailure_false_backwards (π := π) (φ := φ) hterm_ss hnf_final
                      exact absurd this hnf₁)
                | .inr hok_ss =>
                  exact .inr (fun hnf => by
                    have hnf₁ : ρ₁.hasFailure = Bool.false :=
                      hasFailure_false_backwards (π := π) (φ := φ) hterm_ss hnf
                    exact ReflTrans_Transitive _ _ _ _
                      (stmts_cons_step Expression (EvalCommand π φ) (EvalPureFunc φ)
                        (stmtResult σ s) (blockResult (stmtPostState σ s) ss)
                        ρ₀ ρ₁ (hok_s hnf₁))
                      (hok_ss hnf))
        · intro lbl ρ' hstar
          cases hstar with
          | step _ _ _ h1 r1 => cases h1 with
            | step_stmts_cons =>
              match seq_reaches_exiting Expression (EvalCommand π φ) (EvalPureFunc φ) r1 with
              | .inl hexit_s =>
                match (ih.1 σ s hsz_s hnofd_s ρ₀ hwfb hwfv hwfvar).2 lbl ρ' hexit_s with
                | .inl hcf =>
                  exact .inl (canFail_head_to_block π φ (stmtResult σ s) (blockResult (stmtPostState σ s) ss) ρ₀ hcf)
                | .inr hok =>
                  exact .inr (fun hnf =>
                    stmts_cons_exiting π φ (stmtResult σ s) (blockResult (stmtPostState σ s) ss) lbl ρ₀ ρ' (hok hnf))
              | .inr ⟨ρ₁, hterm_s, hexit_ss⟩ =>
                match (ih.1 σ s hsz_s hnofd_s ρ₀ hwfb hwfv hwfvar).1 ρ₁ hterm_s with
                | .inl hcf =>
                  exact .inl (canFail_head_to_block π φ (stmtResult σ s) (blockResult (stmtPostState σ s) ss) ρ₀ hcf)
                | .inr hok_s =>
                  have hwfb₁ := star_preserves_wf (π := π) (φ := φ) hwf_ext hterm_s hwfb
                  have hwfv₁ := star_preserves_wfVal (π := π) (φ := φ) hwf_ext hterm_s hwfv
                  have hwfvar₁ := star_preserves_wfVar (π := π) (φ := φ) hwf_ext hterm_s hwfvar
                  have ss_ih := ih.2.1 (stmtPostState σ s) ss hsz_ss hnofd_ss ρ₁ hwfb₁ hwfv₁ hwfvar₁
                  match ss_ih.2 lbl ρ' hexit_ss with
                  | .inl hcf =>
                    by_cases hnf₁ : ρ₁.hasFailure = Bool.false
                    · exact .inl (canFail_tail_to_block π φ (stmtResult σ s)
                        (blockResult (stmtPostState σ s) ss) ρ₀ ρ₁ (hok_s hnf₁) hcf)
                    · exact .inr (fun hnf_final => by
                        have : ρ₁.hasFailure = Bool.false :=
                          hasFailure_false_backwards (π := π) (φ := φ) hexit_ss hnf_final
                        exact absurd this hnf₁)
                  | .inr hok_ss =>
                    exact .inr (fun hnf => by
                      have hnf₁ : ρ₁.hasFailure = Bool.false :=
                        hasFailure_false_backwards (π := π) (φ := φ) hexit_ss hnf
                      exact ReflTrans_Transitive _ _ _ _
                        (stmts_cons_step Expression (EvalCommand π φ) (EvalPureFunc φ)
                          (stmtResult σ s) (blockResult (stmtPostState σ s) ss)
                          ρ₀ ρ₁ (hok_s hnf₁))
                        (hok_ss hnf))
    -- === Statement CanFail ===
    · intro σ st hsz hnofd ρ₀ hwfb hwfv hwfvar hcf
      obtain ⟨cfg, hfail, hreach⟩ := hcf
      match st with
      | .cmd c => rw [stmtResult_cmd]; exact ⟨cfg, hfail, hreach⟩
      | .exit l md => rw [stmtResult_exit]; exact ⟨cfg, hfail, hreach⟩
      | .funcDecl d md => rw [stmtResult_funcDecl]; exact ⟨cfg, hfail, hreach⟩
      | .typeDecl tc md => rw [stmtResult_typeDecl]; exact ⟨cfg, hfail, hreach⟩
      | .block l bss md =>
        rw [stmtResult_block]
        have hnofd_bss : Block.noFuncDecl bss = Bool.true := by
          simp [Stmt.noFuncDecl] at hnofd; exact hnofd
        cases hreach with
        | refl => exact ⟨.stmt (.block l (blockResult σ bss) md) ρ₀, hfail, .refl _⟩
        | step _ _ _ h1 r1 => cases h1 with
          | step_block =>
            have ⟨inner_cfg, hfail', hinner⟩ := block_canfail_to_inner r1 hfail
            have hsz_bss : Block.sizeOf bss ≤ n := by
              simp [Stmt.sizeOf] at hsz; omega
            have ⟨cfg', hfail'', hreach'⟩ := ih.2.2.2 σ bss hsz_bss hnofd_bss ρ₀ hwfb hwfv hwfvar ⟨inner_cfg, hfail', hinner⟩
            exact canFailBlock_to_canFail_block π φ l _ md ρ₀ ⟨cfg', hfail'', hreach'⟩
      | .ite c tss ess md =>
        rw [stmtResult_ite]
        have hsz_tss : Block.sizeOf tss ≤ n := by
          simp [Stmt.sizeOf] at hsz; omega
        have hsz_ess : Block.sizeOf ess ≤ n := by
          simp [Stmt.sizeOf] at hsz; omega
        have hnofd_tss : Block.noFuncDecl tss = Bool.true := by
          simp [Stmt.noFuncDecl, Bool.and_eq_true] at hnofd; exact hnofd.1
        have hnofd_ess : Block.noFuncDecl ess = Bool.true := by
          simp [Stmt.noFuncDecl, Bool.and_eq_true] at hnofd; exact hnofd.2
        cases hreach with
        | refl => exact ⟨.stmt (.ite c (blockResult σ tss) (blockResult (blockPostState σ tss) ess) md) ρ₀, hfail, .refl _⟩
        | step _ _ _ h1 r1 => cases h1 with
          | step_ite_true hcond hwfb' =>
            have ⟨cfg', hfail', hreach'⟩ := ih.2.2.2 σ tss hsz_tss hnofd_tss ρ₀ hwfb hwfv hwfvar ⟨cfg, hfail, r1⟩
            exact ⟨cfg', hfail', .step _ _ _ (.step_ite_true hcond hwfb') hreach'⟩
          | step_ite_false hcond hwfb' =>
            have ⟨cfg', hfail', hreach'⟩ := ih.2.2.2 (blockPostState σ tss) ess hsz_ess hnofd_ess ρ₀ hwfb hwfv hwfvar ⟨cfg, hfail, r1⟩
            exact ⟨cfg', hfail', .step _ _ _ (.step_ite_false hcond hwfb') hreach'⟩
          | step_ite_nondet_true =>
            have ⟨cfg', hfail', hreach'⟩ := ih.2.2.2 σ tss hsz_tss hnofd_tss ρ₀ hwfb hwfv hwfvar ⟨cfg, hfail, r1⟩
            exact ⟨cfg', hfail', .step _ _ _ .step_ite_nondet_true hreach'⟩
          | step_ite_nondet_false =>
            have ⟨cfg', hfail', hreach'⟩ := ih.2.2.2 (blockPostState σ tss) ess hsz_ess hnofd_ess ρ₀ hwfb hwfv hwfvar ⟨cfg, hfail, r1⟩
            exact ⟨cfg', hfail', .step _ _ _ .step_ite_nondet_false hreach'⟩
      | .loop guard measure inv body md =>
        have hnofd_body : Block.noFuncDecl body = Bool.true := by
          simp [Stmt.noFuncDecl] at hnofd; exact hnofd
        -- If ρ₀.hasFailure is already true, target trivially CanFails
        by_cases hnf₀ : ρ₀.hasFailure = Bool.true
        · exact ⟨.stmt (stmtResult σ (.loop guard measure inv body md)) ρ₀,
            by show ρ₀.hasFailure = Bool.true; exact hnf₀, .refl _⟩
        · -- ρ₀.hasFailure = false. Use stmtResult_loop_struct to get target structure.
          have ⟨ll, fil, fib, tb, heq_stmt, heq_fib⟩ :=
            stmtResult_loop_struct σ guard measure inv body md
          rw [heq_stmt]
          let mkLbl : Nat → String → String := fun i lbl =>
            s!"{loopElimAssertPrefix}{(StringGenState.gen "loop" σ.gen).fst}_entry_invariant_{if lbl.isEmpty then toString i else s!"{i}_{lbl}"}"
          -- The first step from (.stmt (.loop ...) ρ₀) must be one of the loop constructors
          cases hreach with
          | refl => exact absurd hfail hnf₀
          | step _ _ _ h1 r1 => cases h1 with
            | step_loop_exit hguard_ff hinv_eval hff_iff hwfb' =>
              cases r1 with
              | refl =>
                have hnf₀' : ρ₀.hasFailure = Bool.false := by cases h : ρ₀.hasFailure <;> simp_all
                have hsome_ff : ∃ le ∈ inv, ρ₀.eval ρ₀.store le.2 = .some HasBool.ff := by
                  apply hff_iff.mp; revert hfail; simp [Config.getEnv, Env.hasFailure, hnf₀']
                  exact id
                have hcf := canFailBlock_append_left π φ
                  (inv.mapIdx fun i le => Stmt.cmd (HasPassiveCmds.assert (mkLbl i le.1) le.2 md))
                  (inv.mapIdx fun i le => Stmt.cmd (HasPassiveCmds.assume
                    s!"{loopElimAssumePrefix}{(StringGenState.gen "loop" σ.gen).fst}_entry_invariant_{if le.1.isEmpty then toString i else s!"{i}_{le.1}"}" le.2 md))
                  ρ₀
                  (stmts_mapIdx_assert_canFail π φ inv ρ₀ md mkLbl hwfb hnf₀' hinv_eval hsome_ff)
                rw [← heq_fib] at hcf
                exact canFailBlock_to_canFail_block π φ ll _ _ ρ₀
                  (canFail_head_to_block π φ _ _ ρ₀ (canFailBlock_to_canFail_block π φ fil _ _ ρ₀ hcf))
              | step _ _ _ h2 _ => cases h2
            | step_loop_enter hguard_tt hinv_eval hff_iff hwfb' =>
              -- Same logic: if hasInvFailure=true, entry assert fails. If false, source body from ρ₀ canfails.
              have hnf₀' : ρ₀.hasFailure = Bool.false := by cases h : ρ₀.hasFailure <;> simp_all
              by_cases hall_tt : ∀ le ∈ inv, ρ₀.eval ρ₀.store le.2 = .some HasBool.tt
              · -- All invs tt, hasInvFailure=false. Delegate to master canfail lemma.
                have hsz_body : Block.sizeOf body ≤ n := by
                  simp [Stmt.sizeOf] at hsz; omega
                rename_i hasInvFailure_det_cf
                have hnif : hasInvFailure_det_cf = Bool.false := by
                  cases h : hasInvFailure_det_cf
                  · rfl
                  · exfalso
                    have ⟨le, hle, hff⟩ := hff_iff.mp h
                    have htt := hall_tt le hle
                    rw [hff] at htt; cases htt
                have henv_eq : ({ ρ₀ with hasFailure := ρ₀.hasFailure || hasInvFailure_det_cf } : Env Expression) = ρ₀ := by
                  rw [hnif]; exact env_or_false_eq ρ₀
                rw [← heq_stmt]
                exact loop_enter_canfail_simulation π φ hwf_ext σ (.det _) measure inv body md ρ₀
                  hwfb hwfv hwfvar hnf₀' hall_tt
                  ⟨cfg, hfail, henv_eq ▸ r1⟩
                  (fun ρ ρ' hwfb' hwfv' hwfvar' hstar =>
                    (ih.2.1 { σ with gen := (StringGenState.gen "loop" σ.gen).snd } body hsz_body hnofd_body ρ hwfb' hwfv' hwfvar').1 ρ' hstar)
                  (fun ρ hwfb' hwfv' hwfvar' hcf =>
                    ih.2.2.2 { σ with gen := (StringGenState.gen "loop" σ.gen).snd } body hsz_body hnofd_body ρ hwfb' hwfv' hwfvar' hcf)
              · -- Some inv is ff → entry assert fails
                have hsome_ff := not_all_tt_implies_some_ff inv ρ₀ hinv_eval hall_tt
                have hcf := canFailBlock_append_left π φ
                  (inv.mapIdx fun i le => Stmt.cmd (HasPassiveCmds.assert (mkLbl i le.1) le.2 md))
                  (inv.mapIdx fun i le => Stmt.cmd (HasPassiveCmds.assume
                    s!"{loopElimAssumePrefix}{(StringGenState.gen "loop" σ.gen).fst}_entry_invariant_{if le.1.isEmpty then toString i else s!"{i}_{le.1}"}" le.2 md))
                  ρ₀
                  (stmts_mapIdx_assert_canFail π φ inv ρ₀ md mkLbl hwfb hnf₀' hinv_eval hsome_ff)
                rw [← heq_fib] at hcf
                exact canFailBlock_to_canFail_block π φ ll _ _ ρ₀
                  (canFail_head_to_block π φ _ _ ρ₀ (canFailBlock_to_canFail_block π φ fil _ _ ρ₀ hcf))
            | step_loop_nondet_exit hinv_eval hff_iff =>
              cases r1 with
              | refl =>
                have hnf₀' : ρ₀.hasFailure = Bool.false := by cases h : ρ₀.hasFailure <;> simp_all
                have hsome_ff : ∃ le ∈ inv, ρ₀.eval ρ₀.store le.2 = .some HasBool.ff := by
                  apply hff_iff.mp; revert hfail; simp [Config.getEnv, Env.hasFailure, hnf₀']
                  exact id
                have hcf := canFailBlock_append_left π φ
                  (inv.mapIdx fun i le => Stmt.cmd (HasPassiveCmds.assert (mkLbl i le.1) le.2 md))
                  (inv.mapIdx fun i le => Stmt.cmd (HasPassiveCmds.assume
                    s!"{loopElimAssumePrefix}{(StringGenState.gen "loop" σ.gen).fst}_entry_invariant_{if le.1.isEmpty then toString i else s!"{i}_{le.1}"}" le.2 md))
                  ρ₀
                  (stmts_mapIdx_assert_canFail π φ inv ρ₀ md mkLbl hwfb hnf₀' hinv_eval hsome_ff)
                rw [← heq_fib] at hcf
                exact canFailBlock_to_canFail_block π φ ll _ _ ρ₀
                  (canFail_head_to_block π φ _ _ ρ₀ (canFailBlock_to_canFail_block π φ fil _ _ ρ₀ hcf))
              | step _ _ _ h2 _ => cases h2
            | step_loop_nondet_enter hinv_eval hff_iff =>
              have hnf₀' : ρ₀.hasFailure = Bool.false := by cases h : ρ₀.hasFailure <;> simp_all
              by_cases hall_tt : ∀ le ∈ inv, ρ₀.eval ρ₀.store le.2 = .some HasBool.tt
              · -- All invs tt, hasInvFailure=false. Delegate to master canfail lemma.
                have hsz_body : Block.sizeOf body ≤ n := by
                  simp [Stmt.sizeOf] at hsz; omega
                rename_i hasInvFailure_nd_cf
                have hnif : hasInvFailure_nd_cf = Bool.false := by
                  cases h : hasInvFailure_nd_cf
                  · rfl
                  · exfalso
                    have ⟨le, hle, hff⟩ := hff_iff.mp h
                    have htt := hall_tt le hle
                    rw [hff] at htt; cases htt
                have henv_eq : ({ ρ₀ with hasFailure := ρ₀.hasFailure || hasInvFailure_nd_cf } : Env Expression) = ρ₀ := by
                  rw [hnif]; exact env_or_false_eq ρ₀
                rw [← heq_stmt]
                exact loop_enter_canfail_simulation π φ hwf_ext σ .nondet measure inv body md ρ₀
                  hwfb hwfv hwfvar hnf₀' hall_tt
                  ⟨cfg, hfail, henv_eq ▸ r1⟩
                  (fun ρ ρ' hwfb' hwfv' hwfvar' hstar =>
                    (ih.2.1 { σ with gen := (StringGenState.gen "loop" σ.gen).snd } body hsz_body hnofd_body ρ hwfb' hwfv' hwfvar').1 ρ' hstar)
                  (fun ρ hwfb' hwfv' hwfvar' hcf =>
                    ih.2.2.2 { σ with gen := (StringGenState.gen "loop" σ.gen).snd } body hsz_body hnofd_body ρ hwfb' hwfv' hwfvar' hcf)
              · have hsome_ff := not_all_tt_implies_some_ff inv ρ₀ hinv_eval hall_tt
                have hcf := canFailBlock_append_left π φ
                  (inv.mapIdx fun i le => Stmt.cmd (HasPassiveCmds.assert (mkLbl i le.1) le.2 md))
                  (inv.mapIdx fun i le => Stmt.cmd (HasPassiveCmds.assume
                    s!"{loopElimAssumePrefix}{(StringGenState.gen "loop" σ.gen).fst}_entry_invariant_{if le.1.isEmpty then toString i else s!"{i}_{le.1}"}" le.2 md))
                  ρ₀
                  (stmts_mapIdx_assert_canFail π φ inv ρ₀ md mkLbl hwfb hnf₀' hinv_eval hsome_ff)
                rw [← heq_fib] at hcf
                exact canFailBlock_to_canFail_block π φ ll _ _ ρ₀
                  (canFail_head_to_block π φ _ _ ρ₀ (canFailBlock_to_canFail_block π φ fil _ _ ρ₀ hcf))
    -- === Block CanFail ===
    · intro σ bss hsz hnofd_blk ρ₀ hwfb hwfv hwfvar hcf
      obtain ⟨cfg, hfail, hreach⟩ := hcf
      match bss with
      | [] => rw [blockResult_nil]; exact ⟨cfg, hfail, hreach⟩
      | s :: ss =>
        rw [blockResult_cons]
        have hsz_s : Stmt.sizeOf s ≤ n := by
          simp [Block.sizeOf] at hsz; omega
        have hsz_ss : Block.sizeOf ss ≤ n := by
          simp [Block.sizeOf] at hsz; omega
        have hnofd_s : Stmt.noFuncDecl s = Bool.true := by
          simp [Block.noFuncDecl, Bool.and_eq_true] at hnofd_blk; exact hnofd_blk.1
        have hnofd_ss : Block.noFuncDecl ss = Bool.true := by
          simp [Block.noFuncDecl, Bool.and_eq_true] at hnofd_blk; exact hnofd_blk.2
        cases hreach with
        | refl =>
          exact ⟨.stmts (stmtResult σ s :: blockResult (stmtPostState σ s) ss) ρ₀, hfail, .refl _⟩
        | step _ _ _ h1 r1 => cases h1 with
          | step_stmts_cons =>
            match seq_canfail_prop r1 hfail with
            | .inl ⟨cfg', hf', hstar'⟩ =>
              have ⟨kcfg, hkf, hkstar⟩ := ih.2.2.1 σ s hsz_s hnofd_s ρ₀ hwfb hwfv hwfvar ⟨cfg', hf', hstar'⟩
              exact canFail_head_to_block π φ (stmtResult σ s) (blockResult (stmtPostState σ s) ss) ρ₀ ⟨kcfg, hkf, hkstar⟩
            | .inr ⟨ρ₁, hterm_s, cfg', hf', hstar_rest⟩ =>
              -- s terminates at ρ₁, rest can fail
              have hsim_s := ih.1 σ s hsz_s hnofd_s ρ₀ hwfb hwfv hwfvar
              match hsim_s.1 ρ₁ hterm_s with
              | .inl hcf_s =>
                exact canFail_head_to_block π φ (stmtResult σ s) (blockResult (stmtPostState σ s) ss) ρ₀ hcf_s
              | .inr hok_s =>
                by_cases hnf₁ : ρ₁.hasFailure = Bool.true
                · have hcf_src_s : Transform.CanFail (LangCore π φ) s ρ₀ :=
                    ⟨.terminal ρ₁, by show ρ₁.hasFailure = Bool.true; exact hnf₁, hterm_s⟩
                  have hcf_tgt_s := ih.2.2.1 σ s hsz_s hnofd_s ρ₀ hwfb hwfv hwfvar hcf_src_s
                  exact canFail_head_to_block π φ (stmtResult σ s) (blockResult (stmtPostState σ s) ss) ρ₀ hcf_tgt_s
                · have hnf₁' : ρ₁.hasFailure = Bool.false := by cases h : ρ₁.hasFailure <;> simp_all
                  have htgt_s := hok_s hnf₁'
                  have hwfb₁ := star_preserves_wf π φ hwf_ext hterm_s hwfb
                  have hwfv₁ := star_preserves_wfVal π φ hwf_ext hterm_s hwfv
                  have hwfvar₁ := star_preserves_wfVar π φ hwf_ext hterm_s hwfvar
                  have ⟨kcfg2, hkf2, hkstar2⟩ := ih.2.2.2 (stmtPostState σ s) ss hsz_ss hnofd_ss ρ₁
                    hwfb₁ hwfv₁ hwfvar₁ ⟨cfg', hf', hstar_rest⟩
                  exact canFail_tail_to_block π φ (stmtResult σ s)
                    (blockResult (stmtPostState σ s) ss) ρ₀ ρ₁ htgt_s ⟨kcfg2, hkf2, hkstar2⟩

/-! ## CanFail preservation (now integrated into simulation) -/

private theorem canfail_simulation
    (hwf_ext : WFEvalExtension φ) (sz : Nat) :
    (∀ (σ : LoopElimState) (st : Statement),
      Stmt.sizeOf st ≤ sz →
      ∀ (ρ₀ : Env Expression),
        WellFormedSemanticEvalBool ρ₀.eval →
        WellFormedSemanticEvalVal ρ₀.eval →
        WellFormedSemanticEvalVar ρ₀.eval →
        Transform.CanFail (LangCore π φ) st ρ₀ →
        Transform.CanFail (LangCore π φ) (stmtResult σ st) ρ₀)
    ∧
    (∀ (σ : LoopElimState) (bss : Statements),
      Block.sizeOf bss ≤ sz →
      ∀ (ρ₀ : Env Expression),
        WellFormedSemanticEvalBool ρ₀.eval →
        WellFormedSemanticEvalVal ρ₀.eval →
        WellFormedSemanticEvalVar ρ₀.eval →
        CanFailBlock π φ bss ρ₀ →
        CanFailBlock π φ (blockResult σ bss) ρ₀) := by
  induction sz with
  | zero =>
    refine ⟨fun σ st hsz => ?_, fun σ bss hsz => ?_⟩
    · match st with
      | .cmd _ => exact absurd hsz (by simp [Stmt.sizeOf])
      | .block .. => exact absurd hsz (by simp [Stmt.sizeOf])
      | .ite .. => exact absurd hsz (by simp [Stmt.sizeOf])
      | .loop .. => exact absurd hsz (by simp [Stmt.sizeOf])
      | .exit .. => exact absurd hsz (by simp [Stmt.sizeOf])
      | .funcDecl .. => exact absurd hsz (by simp [Stmt.sizeOf])
      | .typeDecl .. => exact absurd hsz (by simp [Stmt.sizeOf])
    · match bss with
      | [] =>
        intro ρ₀ _ _ _ hcf
        rw [blockResult_nil]
        exact hcf
      | _ :: _ => exact absurd hsz (by simp [Block.sizeOf])
  | succ n ih =>
    constructor
    · intro σ st hsz ρ₀ hwfb hwfv hwfvar hcf
      obtain ⟨cfg, hfail, hreach⟩ := hcf
      match st with
      | .cmd c => rw [stmtResult_cmd]; exact ⟨cfg, hfail, hreach⟩
      | .exit l md => rw [stmtResult_exit]; exact ⟨cfg, hfail, hreach⟩
      | .funcDecl d md => rw [stmtResult_funcDecl]; exact ⟨cfg, hfail, hreach⟩
      | .typeDecl tc md => rw [stmtResult_typeDecl]; exact ⟨cfg, hfail, hreach⟩
      | .block l bss md =>
        rw [stmtResult_block]
        cases hreach with
        | refl => exact ⟨.stmt (.block l (blockResult σ bss) md) ρ₀, hfail, .refl _⟩
        | step _ _ _ h1 r1 => cases h1 with
          | step_block =>
            have ⟨inner_cfg, hfail', hinner⟩ := block_canfail_to_inner r1 hfail
            have hsz_bss : Block.sizeOf bss ≤ n := by
              simp [Stmt.sizeOf] at hsz; omega
            have ⟨cfg', hfail'', hreach'⟩ := ih.2 σ bss hsz_bss ρ₀ hwfb hwfv hwfvar ⟨inner_cfg, hfail', hinner⟩
            exact canFailBlock_to_canFail_block π φ l _ md ρ₀ ⟨cfg', hfail'', hreach'⟩
      | .ite c tss ess md =>
        rw [stmtResult_ite]
        have hsz_tss : Block.sizeOf tss ≤ n := by
          simp [Stmt.sizeOf] at hsz; omega
        have hsz_ess : Block.sizeOf ess ≤ n := by
          simp [Stmt.sizeOf] at hsz; omega
        cases hreach with
        | refl => exact ⟨.stmt (.ite c (blockResult σ tss) (blockResult (blockPostState σ tss) ess) md) ρ₀, hfail, .refl _⟩
        | step _ _ _ h1 r1 => cases h1 with
          | step_ite_true hcond hwfb' =>
            have ⟨cfg', hfail', hreach'⟩ := ih.2 σ tss hsz_tss ρ₀ hwfb hwfv hwfvar ⟨cfg, hfail, r1⟩
            exact ⟨cfg', hfail', .step _ _ _ (.step_ite_true hcond hwfb') hreach'⟩
          | step_ite_false hcond hwfb' =>
            have ⟨cfg', hfail', hreach'⟩ := ih.2 (blockPostState σ tss) ess hsz_ess ρ₀ hwfb hwfv hwfvar ⟨cfg, hfail, r1⟩
            exact ⟨cfg', hfail', .step _ _ _ (.step_ite_false hcond hwfb') hreach'⟩
          | step_ite_nondet_true =>
            have ⟨cfg', hfail', hreach'⟩ := ih.2 σ tss hsz_tss ρ₀ hwfb hwfv hwfvar ⟨cfg, hfail, r1⟩
            exact ⟨cfg', hfail', .step _ _ _ .step_ite_nondet_true hreach'⟩
          | step_ite_nondet_false =>
            have ⟨cfg', hfail', hreach'⟩ := ih.2 (blockPostState σ tss) ess hsz_ess ρ₀ hwfb hwfv hwfvar ⟨cfg, hfail, r1⟩
            exact ⟨cfg', hfail', .step _ _ _ .step_ite_nondet_false hreach'⟩
      | .loop guard measure inv body md =>
        -- Delegate to the simulation theorem's canfail part
        by_cases hnf₀ : ρ₀.hasFailure = Bool.true
        · exact ⟨.stmt (stmtResult σ (.loop guard measure inv body md)) ρ₀,
            by show ρ₀.hasFailure = Bool.true; exact hnf₀, .refl _⟩
        · exact (simulation π φ hwf_ext (Stmt.sizeOf (.loop guard measure inv body md))).2.2.1
            σ (.loop guard measure inv body md) (Nat.le_refl _) sorry ρ₀ hwfb hwfv hwfvar ⟨cfg, hfail, hreach⟩
    · intro σ bss hsz ρ₀ hwfb hwfv hwfvar hcf
      obtain ⟨cfg, hfail, hreach⟩ := hcf
      match bss with
      | [] => rw [blockResult_nil]; exact ⟨cfg, hfail, hreach⟩
      | s :: ss =>
        rw [blockResult_cons]
        have hsz_s : Stmt.sizeOf s ≤ n := by
          simp [Block.sizeOf] at hsz; omega
        have hsz_ss : Block.sizeOf ss ≤ n := by
          simp [Block.sizeOf] at hsz; omega
        cases hreach with
        | refl =>
          exact ⟨.stmts (stmtResult σ s :: blockResult (stmtPostState σ s) ss) ρ₀, hfail, .refl _⟩
        | step _ _ _ h1 r1 => cases h1 with
          | step_stmts_cons =>
            match seq_canfail_prop r1 hfail with
            | .inl ⟨cfg', hf', hstar'⟩ =>
              have ⟨kcfg, hkf, hkstar⟩ := ih.1 σ s hsz_s ρ₀ hwfb hwfv hwfvar ⟨cfg', hf', hstar'⟩
              exact canFail_head_to_block π φ (stmtResult σ s) (blockResult (stmtPostState σ s) ss) ρ₀ ⟨kcfg, hkf, hkstar⟩
            | .inr ⟨ρ₁, hterm_s, cfg', hf', hstar_rest⟩ =>
              -- s terminates at ρ₁, rest can fail
              have hsim_s := (simulation π φ hwf_ext (Stmt.sizeOf s)).1 σ s (Nat.le_refl _) sorry ρ₀ hwfb hwfv hwfvar
              match hsim_s.1 ρ₁ hterm_s with
              | .inl hcf_s =>
                exact canFail_head_to_block π φ (stmtResult σ s) (blockResult (stmtPostState σ s) ss) ρ₀ hcf_s
              | .inr hok_s =>
                by_cases hnf₁ : ρ₁.hasFailure = Bool.true
                · have hcf_src_s : Transform.CanFail (LangCore π φ) s ρ₀ :=
                    ⟨.terminal ρ₁, by show ρ₁.hasFailure = Bool.true; exact hnf₁, hterm_s⟩
                  have hcf_tgt_s := ih.1 σ s hsz_s ρ₀ hwfb hwfv hwfvar hcf_src_s
                  exact canFail_head_to_block π φ (stmtResult σ s) (blockResult (stmtPostState σ s) ss) ρ₀ hcf_tgt_s
                · have hnf₁' : ρ₁.hasFailure = Bool.false := by cases h : ρ₁.hasFailure <;> simp_all
                  have htgt_s := hok_s hnf₁'
                  have hwfb₁ := star_preserves_wf π φ hwf_ext hterm_s hwfb
                  have hwfv₁ := star_preserves_wfVal π φ hwf_ext hterm_s hwfv
                  have hwfvar₁ := star_preserves_wfVar π φ hwf_ext hterm_s hwfvar
                  have ⟨kcfg2, hkf2, hkstar2⟩ := ih.2 (stmtPostState σ s) ss hsz_ss ρ₁
                    hwfb₁ hwfv₁ hwfvar₁ ⟨cfg', hf', hstar_rest⟩
                  exact canFail_tail_to_block π φ (stmtResult σ s)
                    (blockResult (stmtPostState σ s) ss) ρ₀ ρ₁ htgt_s ⟨kcfg2, hkf2, hkstar2⟩

/-! ## Top-level theorem -/

theorem loopElim_overapproximatesAggressive
    (hwf_ext : WFEvalExtension φ) (σ : LoopElimState) :
    Transform.OverapproximatesAggressively
      (LangCore π φ)
      (LangCore π φ)
      (fun s => some (stmtResult σ s)) := by
  intro st st' ht ρ₀ hwfb hwfv hwfvar
  simp at ht; subst ht
  have hsim := (simulation π φ hwf_ext (Stmt.sizeOf st)).1
    σ st (Nat.le_refl _) sorry ρ₀ hwfb hwfv hwfvar
  refine ⟨?_, ?_, ?_⟩
  · intro ρ' hstar; exact hsim.1 ρ' hstar
  · intro lbl ρ' hstar; exact hsim.2 lbl ρ' hstar
  · intro ⟨cfg, hfail, hreach⟩
    by_cases hnf₀ : ρ₀.hasFailure = Bool.true
    · exact ⟨.stmt (stmtResult σ st) ρ₀, by show ρ₀.hasFailure = Bool.true; exact hnf₀, .refl _⟩
    · exact (canfail_simulation π φ hwf_ext (Stmt.sizeOf st)).1
        σ st (Nat.le_refl _) ρ₀ hwfb hwfv hwfvar ⟨cfg, hfail, hreach⟩

end Core.LoopElim

end -- public section
