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

abbrev LangCore (reserved : List String := []) :=
  Core.Specification.Lang.core π φ reserved
abbrev CoreStar := StepStmtStar Expression (EvalCommand π φ) (EvalPureFunc φ)
abbrev CC := Config Expression Command

/-! ## projectStore helpers -/

private theorem projectStore_id {σ σ' : SemanticStore Expression}
    (h : ∀ x, σ' x ≠ none → σ x ≠ none) :
    projectStore σ σ' = σ' := by
  funext x
  simp [projectStore]
  intro hx
  cases heq : σ' x
  · rfl
  · exact absurd hx (h x (by simp [heq]))

private theorem projectStore_self (σ : SemanticStore Expression) :
    projectStore σ σ = σ := by
  exact projectStore_id (fun _ h => h)

private theorem projectStore_sub {σ₀ σ' : SemanticStore Expression}
    (h : ∀ x, (σ' x).isSome → (σ₀ x).isSome) :
    projectStore σ₀ σ' = σ' :=
  projectStore_id (fun x hne => by simp [Option.ne_none_iff_isSome] at hne ⊢; exact h x hne)

private theorem env_with_same_store (ρ : Env Expression) :
    { ρ with store := ρ.store } = ρ := by
  cases ρ; simp

private theorem projectStore_self_env (ρ : Env Expression) :
    ({ ρ with store := projectStore ρ.store ρ.store } : Env Expression) = ρ := by
  have h : projectStore ρ.store ρ.store = ρ.store := projectStore_self ρ.store
  simp [h]

/-! ## Projecting removeLoopsM results -/

/-- Run the `ExceptT`-wrapped monadic computation, yielding the raw pair. -/
noncomputable def stmtRun (σ : LoopElimState) (s : Statement) :
    Except String (Bool × Statement) × LoopElimState :=
  StateT.run (ExceptT.run (Stmt.removeLoopsM s)) σ

noncomputable def blockRun (σ : LoopElimState) (ss : Statements) :
    Except String (Bool × Statements) × LoopElimState :=
  StateT.run (ExceptT.run (Block.removeLoopsM ss)) σ

/-- The transformation succeeded (did not throw). -/
noncomputable def stmtOk (σ : LoopElimState) (s : Statement) : Prop :=
  (stmtRun σ s).fst.isOk = Bool.true

noncomputable def blockOk (σ : LoopElimState) (ss : Statements) : Prop :=
  (blockRun σ ss).fst.isOk = Bool.true

noncomputable def stmtPostState (σ : LoopElimState) (s : Statement) : LoopElimState :=
  (stmtRun σ s).snd

noncomputable def blockPostState (σ : LoopElimState) (ss : Statements) : LoopElimState :=
  (blockRun σ ss).snd

mutual
/-- Extract the transformed statement, defined structurally on the AST.
    For non-loop cases this agrees with the monadic `removeLoopsM` result.
    For the loop case it delegates to `stmtRun`.
    When the transformation fails (loop with measure conflict), returns `default`. -/
noncomputable def stmtResult (σ : LoopElimState) (s : Statement) : Statement :=
  match s with
  | .cmd c => .cmd c
  | .exit l md => .exit l md
  | .funcDecl d md => .funcDecl d md
  | .typeDecl tc md => .typeDecl tc md
  | .block l bss md => .block l (blockResult σ bss) md
  | .ite c tss ess md => .ite c (blockResult σ tss) (blockResult (blockPostState σ tss) ess) md
  | .loop guard measure inv body md =>
      match (stmtRun σ (.loop guard measure inv body md)).fst with
      | .ok (_, s') => s'
      | .error _ => default

noncomputable def blockResult (σ : LoopElimState) (ss : Statements) : Statements :=
  match ss with
  | [] => []
  | s :: rest => stmtResult σ s :: blockResult (stmtPostState σ s) rest
end

/-! ## CanFail for statement lists (block bodies) -/

private def CanFailBlock (ss : Statements) (ρ₀ : Env Expression) : Prop :=
  ∃ cfg : CC, cfg.getEnv.hasFailure = Bool.true ∧ CoreStar π φ (.stmts ss ρ₀) cfg

/-! ## Identity lemmas -/

private theorem stmtResult_cmd (σ : LoopElimState) (c : Command) :
    stmtResult σ (.cmd c) = .cmd c := by
  simp [stmtResult]

private theorem stmtResult_exit (σ : LoopElimState) (l : String)
    (md : MetaData Expression) :
    stmtResult σ (.exit l md) = .exit l md := by
  simp [stmtResult]

private theorem stmtResult_funcDecl (σ : LoopElimState) (d : PureFunc Expression)
    (md : MetaData Expression) :
    stmtResult σ (.funcDecl d md) = .funcDecl d md := by
  simp [stmtResult]

private theorem stmtResult_typeDecl (σ : LoopElimState) (tc : TypeConstructor)
    (md : MetaData Expression) :
    stmtResult σ (.typeDecl tc md) = .typeDecl tc md := by
  simp [stmtResult]

private theorem stmtResult_block (σ : LoopElimState) (l : String)
    (bss : Statements) (md : MetaData Expression) :
    stmtResult σ (.block l bss md) = .block l (blockResult σ bss) md := by
  simp [stmtResult]

private theorem stmtResult_ite (σ : LoopElimState) (c : ExprOrNondet Expression)
    (tss ess : Statements) (md : MetaData Expression) :
    stmtResult σ (.ite c tss ess md) =
      .ite c (blockResult σ tss) (blockResult (blockPostState σ tss) ess) md := by
  simp [stmtResult]

private theorem blockResult_nil (σ : LoopElimState) :
    blockResult σ [] = [] := by
  simp [blockResult]

private theorem blockResult_cons (σ : LoopElimState) (s : Statement)
    (ss : Statements) :
    blockResult σ (s :: ss) =
      stmtResult σ s :: blockResult (stmtPostState σ s) ss := by
  simp [blockResult]

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
    CoreStar π φ (.stmt (.block l bss md) ρ₀)
      (.terminal { ρ' with store := projectStore ρ₀.store ρ'.store }) :=
  ReflTrans_Transitive _ _ _ _
    (step_block_enter Expression (EvalCommand π φ) (EvalPureFunc φ) l bss md ρ₀)
    (ReflTrans_Transitive _ _ _ _
      (block_inner_star Expression (EvalCommand π φ) (EvalPureFunc φ) _ _ (some l) ρ₀.store h)
      (.step _ _ _ .step_block_done (.refl _)))

private theorem block_wrap_exiting_mismatch
    (l : String) (bss : Statements) (md : MetaData Expression)
    (lv : String) (ρ₀ ρ' : Env Expression)
    (hne : lv ≠ l)
    (h : CoreStar π φ (.stmts bss ρ₀) (.exiting lv ρ')) :
    CoreStar π φ (.stmt (.block l bss md) ρ₀)
      (.exiting lv { ρ' with store := projectStore ρ₀.store ρ'.store }) :=
  ReflTrans_Transitive _ _ _ _
    (step_block_enter Expression (EvalCommand π φ) (EvalPureFunc φ) l bss md ρ₀)
    (ReflTrans_Transitive _ _ _ _
      (block_inner_star Expression (EvalCommand π φ) (EvalPureFunc φ) _ _ (some l) ρ₀.store h)
      (.step _ _ _ (.step_block_exit_mismatch (fun h => hne (Option.some.inj h).symm)) (.refl _)))

-- block_wrap_exiting_none removed: .exiting none is no longer reachable since
-- Stmt.exit takes a mandatory String label.

private theorem block_wrap_exiting_match
    (l : String) (bss : Statements) (md : MetaData Expression)
    (ρ₀ ρ' : Env Expression)
    (h : CoreStar π φ (.stmts bss ρ₀) (.exiting l ρ')) :
    CoreStar π φ (.stmt (.block l bss md) ρ₀)
      (.terminal { ρ' with store := projectStore ρ₀.store ρ'.store }) :=
  ReflTrans_Transitive _ _ _ _
    (step_block_enter Expression (EvalCommand π φ) (EvalPureFunc φ) l bss md ρ₀)
    (ReflTrans_Transitive _ _ _ _
      (block_inner_star Expression (EvalCommand π φ) (EvalPureFunc φ) _ _ (some l) ρ₀.store h)
      (.step _ _ _ (.step_block_exit_match rfl) (.refl _)))

private theorem block_reaches_terminal_refined
    {inner : CC} {l : String} {σ_parent : SemanticStore Expression} {ρ' : Env Expression}
    (hstar : CoreStar π φ (.block (some l) σ_parent inner) (.terminal ρ')) :
    ∃ ρ_inner, (CoreStar π φ inner (.terminal ρ_inner) ∨
      CoreStar π φ inner (.exiting l ρ_inner)) ∧
      ρ' = { ρ_inner with store := projectStore σ_parent ρ_inner.store } := by
  suffices ∀ src tgt, CoreStar π φ src tgt →
      ∀ inner σ_parent ρ', src = .block (some l) σ_parent inner → tgt = .terminal ρ' →
      ∃ ρ_inner, (CoreStar π φ inner (.terminal ρ_inner) ∨
        CoreStar π φ inner (.exiting l ρ_inner)) ∧
        ρ' = { ρ_inner with store := projectStore σ_parent ρ_inner.store } from
    this _ _ hstar _ _ _ rfl rfl
  intro src tgt hstar_g
  induction hstar_g with
  | refl => intro _ _ _ hsrc htgt; subst hsrc; cases htgt
  | step _ mid _ hstep hrest ih =>
    intro inner σ_parent ρ' hsrc htgt; subst hsrc
    cases hstep with
    | step_block_body h =>
      obtain ⟨ρ_inner, hinner, heq⟩ := ih _ _ _ rfl htgt
      exact ⟨ρ_inner, hinner.elim
        (fun hterm => .inl (.step _ _ _ h hterm))
        (fun hexit_match => .inr (.step _ _ _ h hexit_match)), heq⟩
    | step_block_done =>
      subst htgt; cases hrest with
      | refl => exact ⟨_, .inl (.refl _), rfl⟩
      | step _ _ _ h _ => cases h
    | step_block_exit_match heq =>
      subst htgt; cases heq; cases hrest with
      | refl => exact ⟨_, .inr (.refl _), rfl⟩
      | step _ _ _ h _ => cases h
    | step_block_exit_mismatch =>
      subst htgt; cases hrest with | step _ _ _ h _ => cases h

private theorem block_reaches_exiting_refined
    {inner : CC} {l : String} {σ_parent : SemanticStore Expression}
    {lbl : String} {ρ' : Env Expression}
    (hstar : CoreStar π φ (.block (some l) σ_parent inner) (.exiting lbl ρ')) :
    ∃ ρ_inner, lbl ≠ l ∧
      CoreStar π φ inner (.exiting lbl ρ_inner) ∧
      ρ' = { ρ_inner with store := projectStore σ_parent ρ_inner.store } := by
  suffices ∀ src tgt, CoreStar π φ src tgt →
      ∀ inner σ_parent lbl ρ', src = .block (some l) σ_parent inner → tgt = .exiting lbl ρ' →
      ∃ ρ_inner, lbl ≠ l ∧
        CoreStar π φ inner (.exiting lbl ρ_inner) ∧
        ρ' = { ρ_inner with store := projectStore σ_parent ρ_inner.store } from
    this _ _ hstar _ _ _ _ rfl rfl
  intro src tgt hstar_g
  induction hstar_g with
  | refl => intro _ _ _ _ hsrc htgt; subst hsrc; cases htgt
  | step _ mid _ hstep hrest ih =>
    intro inner σ_parent lbl ρ' hsrc htgt; subst hsrc
    cases hstep with
    | step_block_body h =>
      obtain ⟨ρ_inner, hne, hexit, hproj⟩ := ih _ _ _ _ rfl htgt
      exact ⟨ρ_inner, hne, .step _ _ _ h hexit, hproj⟩
    | step_block_done =>
      subst htgt; cases hrest with | step _ _ _ h _ => cases h
    | step_block_exit_match =>
      subst htgt; cases hrest with | step _ _ _ h _ => cases h
    | step_block_exit_mismatch hne =>
      subst htgt
      cases hrest with
      | refl => exact ⟨_, fun heq => hne (congrArg Option.some heq.symm), .refl _, rfl⟩
      | step _ _ _ h _ => cases h

private theorem canFailBlock_to_canFail_block
    (l : String) (bss : Statements) (md : MetaData Expression) (ρ₀ : Env Expression)
    (h : CanFailBlock π φ bss ρ₀) :
    Transform.CanFail (LangCore π φ) (.block l bss md) ρ₀ := by
  obtain ⟨cfg, hfail, hreach⟩ := h
  exact ⟨.block (.some l) ρ₀.store cfg, by show cfg.getEnv.hasFailure = Bool.true; exact hfail,
    ReflTrans_Transitive _ _ _ _
      (step_block_enter Expression (EvalCommand π φ) (EvalPureFunc φ) l bss md ρ₀)
      (block_inner_star Expression (EvalCommand π φ) (EvalPureFunc φ) _ _ (.some l) ρ₀.store hreach)⟩

private theorem stmts_cons_exiting
    (s : Statement) (ss : Statements) (lbl : String)
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

/-- Core evaluator: `HasFvar.getFvar (HasFvar.mkFvar x) = some x`. -/
private theorem core_getFvar_mkFvar (x : Expression.Ident) :
    HasFvar.getFvar (P := Expression) (HasFvar.mkFvar x) = .some x := by
  rfl

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

/-- Derive that a measure expression evaluates from the fact that
    `lt m zero` evaluates, using `WellFormedCoreEvalDefinedness.appdef`. -/
private theorem measure_eval_from_lt
    (δ : CoreEval) (σ : CoreStore) (m : Expression.Expr)
    (hwfc : WellFormedCoreEvalCong δ)
    (hmeas_lb : δ σ (HasIntOrder.lt m HasIntOrder.zero) = .some HasBool.ff) :
    ∃ v, δ σ m = .some v := by
  -- HasIntOrder.lt m zero = .app () (.app () Core.intLtOp m) (.intConst () 0)
  have hsome_outer : (δ σ (.app () (.app () Core.intLtOp m) (.intConst () 0))).isSome := by
    show (δ σ (HasIntOrder.lt m HasIntOrder.zero)).isSome
    rw [hmeas_lb]; simp
  have ⟨hinner, _⟩ := hwfc.definedness.appdef σ () (.app () Core.intLtOp m) (.intConst () 0) hsome_outer
  have ⟨_, hm⟩ := hwfc.definedness.appdef σ () Core.intLtOp m hinner
  exact Option.isSome_iff_exists.mp hm

/-- Convert from `eval me = some v ∧ eval (lt v zero) = ff` to `eval (lt me zero) = ff`
    using `WellFormedCoreEvalCong.appcongr` and `WellFormedSemanticEvalVal`. -/
private theorem measure_lt_congr
    (δ : CoreEval) (σ : CoreStore) (me v : Expression.Expr)
    (hwfc : WellFormedCoreEvalCong δ)
    (hwfv : WellFormedSemanticEvalVal δ)
    (heval_me : δ σ me = .some v)
    (hlt_v : δ σ (HasIntOrder.lt v HasIntOrder.zero) = .some HasBool.ff) :
    δ σ (HasIntOrder.lt me HasIntOrder.zero) = .some HasBool.ff := by
  -- HasIntOrder.lt e zero = .app () (.app () Core.intLtOp e) (.intConst () 0)
  -- We need: eval σ (app (app intLtOp me) zero) = eval σ (app (app intLtOp v) zero)
  -- By appcongr: need eval σ (app intLtOp me) = eval σ (app intLtOp v) and eval σ zero = eval σ zero
  -- By appcongr: need eval σ intLtOp = eval σ intLtOp and eval σ me = eval σ v
  -- eval σ me = some v, and eval σ v = some v (by WellFormedSemanticEvalVal, since v is a value output of eval)
  have hval_v : HasVal.value (P := Expression) v := hwfv.1 me v σ heval_me
  have heval_v : δ σ v = .some v := hwfv.2 v σ hval_v
  have hme_eq_v : δ σ me = δ σ v := by rw [heval_me, heval_v]
  have hinner_congr : δ σ (.app () Core.intLtOp me) = δ σ (.app () Core.intLtOp v) :=
    hwfc.appcongr σ σ () Core.intLtOp Core.intLtOp me v rfl hme_eq_v
  have houter_congr : δ σ (.app () (.app () Core.intLtOp me) (.intConst () 0)) =
      δ σ (.app () (.app () Core.intLtOp v) (.intConst () 0)) :=
    hwfc.appcongr σ σ () (.app () Core.intLtOp me) (.app () Core.intLtOp v)
      (.intConst () 0) (.intConst () 0) hinner_congr rfl
  show δ σ (.app () (.app () Core.intLtOp me) (.intConst () 0)) = .some HasBool.ff
  rw [houter_congr]; exact hlt_v

/-- The pre_termination stmts [init_m_old, assert_lb] terminate at some ρ_pf
    that agrees with ρ₀ on all variables except the fresh m_old.
    Derives measure evaluability from `hmeas_lb` using `WellFormedCoreEvalCong`,
    and proves the lt-congruence after init using `appcongr`. -/
private theorem pre_termination_stmts_terminal
    (loop_num : String) (m : Expression.Expr) (md : MetaData Expression)
    (ρ₀ : Env Expression)
    (hwfb : WellFormedSemanticEvalBool ρ₀.eval)
    (hwfvar : WellFormedSemanticEvalVar ρ₀.eval)
    (hnf : ρ₀.hasFailure = Bool.false)
    (hwfc : WellFormedCoreEvalCong ρ₀.eval)
    (hwfv : WellFormedSemanticEvalVal ρ₀.eval)
    (hmeas_lb : ρ₀.eval ρ₀.store (HasIntOrder.lt m HasIntOrder.zero) = .some HasBool.ff)
    (hm_old_fresh : ρ₀.store (HasIdent.ident (P := Expression)
      s!"$__loop_measure_{loop_num}") = none) :
    let m_old_ident := HasIdent.ident (P := Expression) s!"$__loop_measure_{loop_num}"
    let m_old_expr := HasFvar.mkFvar (P := Expression) m_old_ident
    let init_m_old := Stmt.cmd (HasInit.init m_old_ident HasIntOrder.intTy (.det m) md)
    let assert_lb := Stmt.cmd (HasPassiveCmds.assert
      s!"{loopElimAssertPrefix}{loop_num}_measure_lb"
      (HasNot.not (HasIntOrder.lt m_old_expr HasIntOrder.zero)) md)
    ∃ ρ_pf, CoreStar π φ (.stmts [init_m_old, assert_lb] ρ₀) (.terminal ρ_pf) ∧
      ρ_pf.eval = ρ₀.eval ∧ ρ_pf.hasFailure = ρ₀.hasFailure ∧
      (∀ n, n ≠ m_old_ident → ρ_pf.store n = ρ₀.store n) := by
  intro m_old_ident m_old_expr init_m_old assert_lb
  have hmeas_eval := measure_eval_from_lt ρ₀.eval ρ₀.store m hwfc hmeas_lb
  obtain ⟨v, hv⟩ := hmeas_eval
  -- Construct σ₁: store after init sets m_old_ident to v
  let σ₁ : CoreStore := fun x => if x = m_old_ident then .some v else ρ₀.store x
  have hinit_cmd : Imperative.EvalCmd (P := Expression) ρ₀.eval ρ₀.store
      (Imperative.Cmd.init m_old_ident HasIntOrder.intTy (.det m) md) σ₁ false := by
    cases h : ρ₀.store m_old_ident with
    | none =>
      exact .eval_init hv (.init h (by simp [σ₁]) (by intro y hy; simp [σ₁, Ne.symm hy])) hwfvar
    | some v' =>
      exact absurd (h.symm.trans hm_old_fresh) (by simp)
  -- After init: env is { ρ₀ with store := σ₁ }
  let ρ₁ : Env Expression := { ρ₀ with store := σ₁ }
  have hstep_init : CoreStar π φ
      (.stmt init_m_old ρ₀) (.terminal ρ₁) := by
    have h : CoreStar π φ (.stmt init_m_old ρ₀)
        (.terminal { ρ₀ with store := σ₁, hasFailure := ρ₀.hasFailure || false }) :=
      .step _ _ _ (.step_cmd (EvalCommand.cmd_sem hinit_cmd)) (.refl _)
    simp only [Bool.or_false] at h; exact h
  -- Now prove assert_lb passes at ρ₁.
  -- m_old_expr evaluates to v at ρ₁ (by WellFormedSemanticEvalVar + getFvar)
  have heval_m_old : ρ₁.eval ρ₁.store m_old_expr = .some v := by
    have hgf := core_getFvar_mkFvar m_old_ident
    have := hwfvar m_old_expr m_old_ident ρ₁.store hgf
    rw [this]; simp [ρ₁, σ₁]
  -- lt m_old_expr zero evaluates to ff at ρ₁
  -- By appcongr: eval σ₁ (lt m_old_expr zero) = eval ρ₀.store (lt m zero) = ff
  have hlt_ff : ρ₁.eval ρ₁.store (HasIntOrder.lt m_old_expr HasIntOrder.zero) = .some HasBool.ff := by
    -- ρ₁.eval = ρ₀.eval, so work with ρ₀.eval throughout
    -- Need: ρ₀.eval σ₁ (app (app intLtOp m_old_expr) zero) = some ff
    -- We show it equals ρ₀.eval ρ₀.store (app (app intLtOp m) zero) = hmeas_lb
    have hval_op : HasVal.value (P := Expression) Core.intLtOp := by
      show Value Core.intLtOp
      simp only [Core.intLtOp, Lambda.LFunc.opExpr]
      exact Value.op
    have hval_zero : HasVal.value (P := Expression) (HasIntOrder.zero (P := Expression)) := by
      show Value (.intConst () 0); unfold Lambda.LExpr.intConst; exact Value.const
    have heval_op_σ₁ : ρ₀.eval σ₁ Core.intLtOp = .some Core.intLtOp := hwfv.2 _ σ₁ hval_op
    have heval_op_σ₀ : ρ₀.eval ρ₀.store Core.intLtOp = .some Core.intLtOp := hwfv.2 _ ρ₀.store hval_op
    have heval_zero_σ₁ : ρ₀.eval σ₁ (HasIntOrder.zero (P := Expression)) =
        .some (HasIntOrder.zero (P := Expression)) := hwfv.2 _ σ₁ hval_zero
    have heval_zero_σ₀ : ρ₀.eval ρ₀.store (HasIntOrder.zero (P := Expression)) =
        .some (HasIntOrder.zero (P := Expression)) := hwfv.2 _ ρ₀.store hval_zero
    have hop_eq : ρ₀.eval σ₁ Core.intLtOp = ρ₀.eval ρ₀.store Core.intLtOp := by
      rw [heval_op_σ₁, heval_op_σ₀]
    have hme_eq : ρ₀.eval σ₁ m_old_expr = ρ₀.eval ρ₀.store m := by
      rw [heval_m_old, hv]
    have hzero_eq : ρ₀.eval σ₁ (HasIntOrder.zero (P := Expression)) =
        ρ₀.eval ρ₀.store (HasIntOrder.zero (P := Expression)) := by
      rw [heval_zero_σ₁, heval_zero_σ₀]
    have hinner : ρ₀.eval σ₁ (.app () Core.intLtOp m_old_expr) =
        ρ₀.eval ρ₀.store (.app () Core.intLtOp m) :=
      hwfc.appcongr σ₁ ρ₀.store () Core.intLtOp Core.intLtOp m_old_expr m hop_eq hme_eq
    have houter : ρ₀.eval σ₁ (.app () (.app () Core.intLtOp m_old_expr) (HasIntOrder.zero (P := Expression))) =
        ρ₀.eval ρ₀.store (.app () (.app () Core.intLtOp m) (HasIntOrder.zero (P := Expression))) :=
      hwfc.appcongr σ₁ ρ₀.store () (.app () Core.intLtOp m_old_expr) (.app () Core.intLtOp m)
        (HasIntOrder.zero (P := Expression)) (HasIntOrder.zero (P := Expression)) hinner hzero_eq
    show ρ₀.eval σ₁ (.app () (.app () Core.intLtOp m_old_expr) (HasIntOrder.zero (P := Expression))) = .some HasBool.ff
    rw [houter]; exact hmeas_lb
  have hnot_tt : ρ₁.eval ρ₁.store (HasNot.not (HasIntOrder.lt m_old_expr HasIntOrder.zero)) = .some HasBool.tt :=
    (hwfb ρ₁.store (HasIntOrder.lt m_old_expr HasIntOrder.zero)).2.1 hlt_ff
  have hstep_assert : CoreStar π φ (.stmt assert_lb ρ₁) (.terminal ρ₁) :=
    assert_pass_step π φ _ _ md ρ₁ hnot_tt hwfb
  -- Combine: stmts [init, assert] from ρ₀ terminates at ρ₁
  exact ⟨ρ₁,
    ReflTrans_Transitive _ _ _ _
      (.step _ _ _ .step_stmts_cons (.refl _))
      (ReflTrans_Transitive _ _ _ _
        (seq_inner_star Expression (EvalCommand π φ) (EvalPureFunc φ) _ _ _ hstep_init)
        (.step _ _ _ .step_seq_done
          (.step _ _ _ .step_stmts_cons
            (ReflTrans_Transitive _ _ _ _
              (seq_inner_star Expression (EvalCommand π φ) (EvalPureFunc φ) _ _ _ hstep_assert)
              (.step _ _ _ .step_seq_done
                (.step _ _ _ .step_stmts_nil (.refl _))))))),
    rfl, by simp [ρ₁, Bool.or_false, hnf],
    fun n hn => by simp [ρ₁, σ₁, hn]⟩

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
    (body : Statements) (md : MetaData Expression)
    (hok : stmtOk σ (.loop guard measure inv body md)) :
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
  change ∃ (loop_label first_iter_label : String) (first_iter_body then_branch : Statements),
    (match (stmtRun σ (.loop guard measure inv body md)).fst with
      | .ok (_, s') => s' | .error _ => default) =
    .block loop_label [.block first_iter_label first_iter_body {}, .ite guard then_branch [] {}] {} ∧
    first_iter_body =
      let loop_num := (StringGenState.gen "loop" σ.gen).fst
      let invSuffix : Nat → String → String := fun i lbl =>
        if lbl.isEmpty then toString i else s!"{i}_{lbl}"
      (inv.mapIdx fun i le => Stmt.cmd (HasPassiveCmds.assert
        s!"{loopElimAssertPrefix}{loop_num}_entry_invariant_{invSuffix i le.1}" le.2 md)) ++
      (inv.mapIdx fun i le => Stmt.cmd (HasPassiveCmds.assume
        s!"{loopElimAssumePrefix}{loop_num}_entry_invariant_{invSuffix i le.1}" le.2 md))
  have hok' := hok
  unfold stmtOk at hok'
  match h : (stmtRun σ (.loop guard measure inv body md)).fst with
  | .error e => simp [h, Except.isOk, Except.toBool] at hok'
  | .ok (b, s') =>
    simp only [h]
    simp only [stmtRun, StateT.run, ExceptT.run, Stmt.removeLoopsM,
      bind, pure, ExceptT.bind, ExceptT.pure, ExceptT.mk, ExceptT.bindCont,
      ExceptT.lift, StateT.bind,
      Functor.map, liftM, monadLift, MonadLift.monadLift,
      modify, MonadState.modifyGet, StateT.modifyGet, StateT.map,
      genLoopNum, bumpStat] at h
    repeat (first
      | (cases h; exact ⟨_, _, _, _, rfl, rfl⟩)
      | contradiction
      | (split at h; skip))
    all_goals (first | (cases h; exact ⟨_, _, _, _, rfl, rfl⟩) | contradiction)

/-- The then-branch of the transformed loop contains body_statements (= blockResult of body)
    sandwiched between prefix stmts (havoc + assumes + pre_termination) and suffix stmts
    (maintain_invariants + post_termination). -/
private theorem stmtResult_loop_then_branch_struct (σ : LoopElimState)
    (guard : ExprOrNondet Expression)
    (measure : Option Expression.Expr)
    (inv : List (String × Expression.Expr))
    (body : Statements) (md : MetaData Expression)
    (hok : stmtOk σ (.loop guard measure inv body md)) :
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
    body_statements = body ∧
    (maintain_invariants = inv.mapIdx fun i le =>
      Stmt.cmd (HasPassiveCmds.assert
        s!"{loopElimAssertPrefix}{(StringGenState.gen "loop" σ.gen).fst}_arbitrary_iter_maintain_invariant_{if le.1.isEmpty then toString i else s!"{i}_{le.1}"}" le.2 md)) ∧
    first_iter_body =
      let loop_num := (StringGenState.gen "loop" σ.gen).fst
      let invSuffix : Nat → String → String := fun i lbl =>
        if lbl.isEmpty then toString i else s!"{i}_{lbl}"
      (inv.mapIdx fun i le => Stmt.cmd (HasPassiveCmds.assert
        s!"{loopElimAssertPrefix}{loop_num}_entry_invariant_{invSuffix i le.1}" le.2 md)) ++
      (inv.mapIdx fun i le => Stmt.cmd (HasPassiveCmds.assume
        s!"{loopElimAssumePrefix}{loop_num}_entry_invariant_{invSuffix i le.1}" le.2 md)) := by
  change ∃ (loop_label first_iter_label arb_iter_label : String)
    (first_iter_body : Statements)
    (prefix_stmts suffix_stmts exit_state_stmts : Statements)
    (maintain_invariants : Statements)
    (body_statements : Statements),
    (match (stmtRun σ (.loop guard measure inv body md)).fst with
      | .ok (_, s') => s' | .error _ => default) =
    .block loop_label
      [.block first_iter_label first_iter_body {},
       .ite guard
         (.block arb_iter_label
           (prefix_stmts ++ body_statements ++ maintain_invariants ++ suffix_stmts) {}
          :: exit_state_stmts) [] {}] {} ∧
    body_statements = body ∧
    (maintain_invariants = inv.mapIdx fun i le =>
      Stmt.cmd (HasPassiveCmds.assert
        s!"{loopElimAssertPrefix}{(StringGenState.gen "loop" σ.gen).fst}_arbitrary_iter_maintain_invariant_{if le.1.isEmpty then toString i else s!"{i}_{le.1}"}" le.2 md)) ∧
    first_iter_body =
      let loop_num := (StringGenState.gen "loop" σ.gen).fst
      let invSuffix : Nat → String → String := fun i lbl =>
        if lbl.isEmpty then toString i else s!"{i}_{lbl}"
      (inv.mapIdx fun i le => Stmt.cmd (HasPassiveCmds.assert
        s!"{loopElimAssertPrefix}{loop_num}_entry_invariant_{invSuffix i le.1}" le.2 md)) ++
      (inv.mapIdx fun i le => Stmt.cmd (HasPassiveCmds.assume
        s!"{loopElimAssumePrefix}{loop_num}_entry_invariant_{invSuffix i le.1}" le.2 md))
  have hok' := hok
  unfold stmtOk at hok'
  match h : (stmtRun σ (.loop guard measure inv body md)).fst with
  | .error e => simp [h, Except.isOk, Except.toBool] at hok'
  | .ok (b, s') =>
    simp only [h]
    simp only [stmtRun, StateT.run, ExceptT.run, Stmt.removeLoopsM,
      bind, pure, ExceptT.bind, ExceptT.pure, ExceptT.mk, ExceptT.bindCont,
      ExceptT.lift, StateT.bind,
      Functor.map, liftM, monadLift, MonadLift.monadLift,
      modify, MonadState.modifyGet, StateT.modifyGet, StateT.map,
      genLoopNum, bumpStat] at h
    repeat (first
      | (cases h; exact ⟨_, _, _, _, _, _, _, _, _, rfl, rfl, rfl, rfl⟩)
      | contradiction
      | (split at h; skip))
    all_goals (first | (cases h; exact ⟨_, _, _, _, _, _, _, _, _, rfl, rfl, rfl, rfl⟩) | contradiction)

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

/-- Execute the havoc block (`.block label (vs.map havoc) md`) as identity. -/
private theorem havoc_block_identity
    (label : String) (vs : List Expression.Ident) (md : MetaData Expression)
    (ρ : Env Expression)
    (hdef : ∀ n ∈ vs, (ρ.store n).isSome)
    (hwfvar : WellFormedSemanticEvalVar ρ.eval)
    (hnf : ρ.hasFailure = Bool.false) :
    CoreStar π φ
      (.stmt (.block label (vs.map fun n => Stmt.cmd (HasHavoc.havoc n md)) md) ρ)
      (.terminal ρ) := by
  have h := block_wrap_terminal π φ label _ md ρ ρ
    (havocs_identity_stmts π φ vs md ρ hdef hwfvar hnf)
  show CoreStar π φ (.stmt (.block label (vs.map fun n => Stmt.cmd (HasHavoc.havoc n md)) md) ρ)
    (.terminal ρ)
  have : { ρ with store := projectStore ρ.store ρ.store } = ρ := by
    simp [projectStore_self]
  rw [this] at h
  exact h

/-- Variant of `havoc_block_identity` where the wrapping block uses `∅` (empty) metadata
    while the inner havoc commands use `md`.  This matches the form produced by
    `Stmt.removeLoopsM` for loop havoc blocks. -/
private theorem havoc_block_identity_empty_outer
    (label : String) (vs : List Expression.Ident) (md : MetaData Expression)
    (ρ : Env Expression)
    (hdef : ∀ n ∈ vs, (ρ.store n).isSome)
    (hwfvar : WellFormedSemanticEvalVar ρ.eval)
    (hnf : ρ.hasFailure = Bool.false) :
    CoreStar π φ
      (.stmt (.block label (vs.map fun n => Stmt.cmd (HasHavoc.havoc n md)) ∅) ρ)
      (.terminal ρ) := by
  have h := block_wrap_terminal π φ label _ ∅ ρ ρ
    (havocs_identity_stmts π φ vs md ρ hdef hwfvar hnf)
  show CoreStar π φ (.stmt (.block label (vs.map fun n => Stmt.cmd (HasHavoc.havoc n md)) ∅) ρ)
    (.terminal ρ)
  have : { ρ with store := projectStore ρ.store ρ.store } = ρ := by
    simp [projectStore_self]
  rw [this] at h
  exact h

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
      (.stmt (.block label (vars.map fun n => Stmt.cmd (HasHavoc.havoc n md)) md) ρ₀)
      (.terminal { ρ₀ with store := ρ_target.store }) := by
  have ⟨σ_out, hmatch, hother, hstar⟩ :=
    havocs_targeting_stmts π φ vars md ρ₀ ρ_target.store hwfvar hdef_src hdef_tgt hnf
  have h : projectStore ρ₀.store σ_out = ρ_target.store := by
    funext x
    simp [projectStore]
    split
    · rename_i hsome
      by_cases hx : x ∈ vars
      · exact hmatch x hx
      · rw [hother x hx, hagree x hx]
    · rename_i hnone
      simp at hnone
      by_cases hx : x ∈ vars
      · have := hdef_src x hx
        simp [hnone] at this
      · rw [← hnone, hagree x hx]
  have := block_wrap_terminal π φ label _ md ρ₀ { ρ₀ with store := σ_out } hstar
  show CoreStar π φ (.stmt (.block label (vars.map fun n => Stmt.cmd (HasHavoc.havoc n md)) md) ρ₀)
    (.terminal { ρ₀ with store := ρ_target.store })
  have heq : { { ρ₀ with store := σ_out } with store := projectStore ρ₀.store σ_out } =
    { ρ₀ with store := ρ_target.store } := by
    simp [h]
  rw [heq] at this
  exact this

/-- Variant of `havoc_block_to_target` where the wrapping block uses `∅` (empty) metadata
    while the inner havoc commands use `md`.  This matches the form produced by
    `Stmt.removeLoopsM` for loop havoc blocks. -/
private theorem havoc_block_to_target_empty_outer
    (label : String) (vars : List Expression.Ident) (md : MetaData Expression)
    (ρ₀ ρ_target : Env Expression)
    (hwfvar : WellFormedSemanticEvalVar ρ₀.eval)
    (hdef_src : ∀ x ∈ vars, (ρ₀.store x).isSome)
    (hdef_tgt : ∀ x ∈ vars, (ρ_target.store x).isSome)
    (hagree : ∀ x, x ∉ vars → ρ_target.store x = ρ₀.store x)
    (hnf : ρ₀.hasFailure = Bool.false) :
    CoreStar π φ
      (.stmt (.block label (vars.map fun n => Stmt.cmd (HasHavoc.havoc n md)) ∅) ρ₀)
      (.terminal { ρ₀ with store := ρ_target.store }) := by
  have ⟨σ_out, hmatch, hother, hstar⟩ :=
    havocs_targeting_stmts π φ vars md ρ₀ ρ_target.store hwfvar hdef_src hdef_tgt hnf
  have h : projectStore ρ₀.store σ_out = ρ_target.store := by
    funext x
    simp [projectStore]
    split
    · rename_i hsome
      by_cases hx : x ∈ vars
      · exact hmatch x hx
      · rw [hother x hx, hagree x hx]
    · rename_i hnone
      simp at hnone
      by_cases hx : x ∈ vars
      · have := hdef_src x hx
        simp [hnone] at this
      · rw [← hnone, hagree x hx]
  have := block_wrap_terminal π φ label _ ∅ ρ₀ { ρ₀ with store := σ_out } hstar
  show CoreStar π φ (.stmt (.block label (vars.map fun n => Stmt.cmd (HasHavoc.havoc n md)) ∅) ρ₀)
    (.terminal { ρ₀ with store := ρ_target.store })
  have heq : { { ρ₀ with store := σ_out } with store := projectStore ρ₀.store σ_out } =
    { ρ₀ with store := ρ_target.store } := by
    simp [h]
  rw [heq] at this
  exact this

/-! ## Store agreement outside modifiedVars -/

/-! ### Helper: Block.modifiedVars/definedVars append decomposition -/

private theorem block_modifiedVars_append (ss₁ ss₂ : Statements) :
    Block.modifiedVars (ss₁ ++ ss₂) = Block.modifiedVars ss₁ ++ Block.modifiedVars ss₂ := by
  induction ss₁ with
  | nil => simp [Block.modifiedVars]
  | cons s rest ih => simp [Block.modifiedVars, ih, List.append_assoc]

private theorem block_definedVars_append (ss₁ ss₂ : Statements) :
    Block.definedVars (ss₁ ++ ss₂) = Block.definedVars ss₁ ++ Block.definedVars ss₂ := by
  induction ss₁ with
  | nil => simp [Block.definedVars]
  | cons s rest ih => simp [Block.definedVars, ih, List.append_assoc]

/-! ### Helper: UpdateStates frame property -/

private theorem updateState_store_frame
    {σ σ' : CoreStore} {v : Expression.Ident} {e : Expression.Expr}
    (hup : UpdateState Expression σ v e σ')
    {y : Expression.Ident} (hne : v ≠ y) :
    σ' y = σ y := by
  cases hup with | update _ _ hframe => exact hframe y hne

private theorem updateStates_store_frame
    {σ σ' : CoreStore} {xs : List Expression.Ident} {vs : List Expression.Expr}
    (hups : UpdateStates σ xs vs σ')
    {y : Expression.Ident} (hy : y ∉ xs) :
    σ' y = σ y := by
  induction hups with
  | update_none => rfl
  | update_some hup _ ih =>
    have hne : _ ≠ y := fun h => hy (List.mem_cons.mpr (.inl h.symm))
    have htail : y ∉ _ := fun h => hy (List.mem_cons.mpr (.inr h))
    exact (ih htail).trans (updateState_store_frame hup hne)

private theorem initState_store_frame
    {σ σ' : CoreStore} {v : Expression.Ident} {e : Expression.Expr}
    (hinit : InitState Expression σ v e σ')
    {y : Expression.Ident} (hne : v ≠ y) :
    σ' y = σ y := by
  cases hinit with | init _ _ hframe => exact hframe y hne

private theorem initStates_store_frame
    {σ σ' : CoreStore} {xs : List Expression.Ident} {vs : List Expression.Expr}
    (hinits : InitStates σ xs vs σ')
    {y : Expression.Ident} (hy : y ∉ xs) :
    σ' y = σ y := by
  induction hinits with
  | init_none => rfl
  | init_some hinit _ ih =>
    have hne : _ ≠ y := fun h => hy (List.mem_cons.mpr (.inl h.symm))
    have htail : y ∉ _ := fun h => hy (List.mem_cons.mpr (.inr h))
    exact (ih htail).trans (initState_store_frame hinit hne)

/-! ### EvalCmd store frame -/

private theorem evalCmd_store_frame
    {δ : CoreEval} {σ σ' : CoreStore} {c : Cmd Expression} {f : Bool}
    (heval : EvalCmd (P := Expression) δ σ c σ' f)
    {x : Expression.Ident}
    (hmod : x ∉ Cmd.modifiedVars c)
    (hdef : x ∉ Cmd.definedVars c) :
    σ' x = σ x := by
  cases heval with
  | eval_init _ hinit _ =>
    exact initState_store_frame hinit
      (fun h => hdef (by simp [Cmd.definedVars]; exact h.symm))
  | eval_init_unconstrained hinit _ =>
    exact initState_store_frame hinit
      (fun h => hdef (by simp [Cmd.definedVars]; exact h.symm))
  | eval_set _ hup _ =>
    exact updateState_store_frame hup
      (fun h => hmod (by simp [Cmd.modifiedVars]; exact h.symm))
  | eval_set_nondet hup _ =>
    exact updateState_store_frame hup
      (fun h => hmod (by simp [Cmd.modifiedVars]; exact h.symm))
  | eval_assert_pass _ _ => rfl
  | eval_assert_fail _ _ => rfl
  | eval_assume _ _ => rfl
  | eval_cover _ => rfl

/-! ### EvalCommand store frame -/

/-! ### evalCommand store frame -/

/-- `EvalCommand` preserves the store at variables not in `Stmt.modifiedVars (.cmd c)`
    or `Stmt.definedVars (.cmd c)`.  Stated with `Stmt` wrappers so that the
    hypothesis types are stable under `@[expose]` opacity. -/
private theorem evalCommand_store_frame_stmt
    {ρ : Env Expression} {c : Command} {σ' : CoreStore} {f : Bool}
    (heval : EvalCommand π φ ρ.eval ρ.store c σ' f)
    {x : Expression.Ident}
    (hmod : x ∉ Stmt.modifiedVars (Stmt.cmd c))
    (hdef : x ∉ Stmt.definedVars (Stmt.cmd c)) :
    σ' x = ρ.store x := by
  cases heval with
  | cmd_sem hcmd =>
    -- hmod : x ∉ Stmt.modifiedVars (.cmd c), hdef : x ∉ Stmt.definedVars (.cmd c)
    -- After case split on hcmd, c is a specific Cmd constructor
    -- EvalCmd case split
    cases hcmd with
    | eval_init _ hinit _ =>
      apply initState_store_frame hinit
      intro heq; apply hdef
      show x ∈ [_]; exact List.mem_singleton.mpr heq.symm
    | eval_init_unconstrained hinit _ =>
      apply initState_store_frame hinit
      intro heq; apply hdef
      show x ∈ [_]; exact List.mem_singleton.mpr heq.symm
    | eval_set _ hup _ =>
      apply updateState_store_frame hup
      intro heq; apply hmod
      show x ∈ [_]; exact List.mem_singleton.mpr heq.symm
    | eval_set_nondet hup _ =>
      apply updateState_store_frame hup
      intro heq; apply hmod
      show x ∈ [_]; exact List.mem_singleton.mpr heq.symm
    | eval_assert_pass _ _ => rfl
    | eval_assert_fail _ _ => rfl
    | eval_assume _ _ => rfl
    | eval_cover _ => rfl
  | call_sem _ _ hlhs _ _ _ _ _ _ _ _ _ _ _ _ _ hups =>
    apply updateStates_store_frame hups
    intro hmem; apply hmod
    show x ∈ Stmt.modifiedVars (Stmt.cmd (CmdExt.call _ _ _))
    simp only [Stmt.modifiedVars, HasVarsImp.modifiedVars, Command.modifiedVars]
    rw [hlhs]; exact hmem

/-! ### Config-level touched vars -/

/-- The set of variables that a config can still modify or define during execution. -/
private def Config.touchedVarsSet : CC → List Expression.Ident
  | .stmt s _ => Stmt.modifiedVars s ++ Stmt.definedVars s
  | .stmts ss _ => Block.modifiedVars ss ++ Block.definedVars ss
  | .terminal _ => []
  | .exiting _ _ => []
  | .block _ _ inner => Config.touchedVarsSet inner
  | .seq inner ss => Config.touchedVarsSet inner ++ Block.modifiedVars ss ++ Block.definedVars ss

/-! ### Outer-store invariant for block scoping -/

/-- Command evaluation preserves store-isSome. -/
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

/-- projectStore preserves isSome for any variable defined in σ_parent and in σ_inner. -/
private theorem projectStore_isSome {σ_parent σ_inner : SemanticStore Expression}
    {n : Expression.Ident}
    (hp : (σ_parent n).isSome) (hi : (σ_inner n).isSome) :
    (projectStore σ_parent σ_inner n).isSome := by
  simp [projectStore, hp, hi]

/-- Block-scope invariant indexed by an outer store `σ_outer`: inside every nested
    `.block _ σ_parent inner`, `σ_parent` contains all vars defined in `σ_outer`,
    AND `inner.getEnv.store` also contains all vars defined in `σ_outer`.
    Trivially true for non-block configs. -/
private def outerInv (σ_outer : SemanticStore Expression) : CC → Prop
  | .stmt _ ρ => ∀ n, (σ_outer n).isSome → (ρ.store n).isSome
  | .stmts _ ρ => ∀ n, (σ_outer n).isSome → (ρ.store n).isSome
  | .terminal ρ => ∀ n, (σ_outer n).isSome → (ρ.store n).isSome
  | .exiting _ ρ => ∀ n, (σ_outer n).isSome → (ρ.store n).isSome
  | .block _ σ_parent inner =>
    (∀ n, (σ_outer n).isSome → (σ_parent n).isSome) ∧ outerInv σ_outer inner
  | .seq inner _ => outerInv σ_outer inner

/-- `outerInv σ_outer c` implies `∀ n, (σ_outer n).isSome → (c.getEnv.store n).isSome`. -/
private theorem outerInv_implies_getEnv_isSome (σ_outer : SemanticStore Expression) (c : CC)
    (hinv : outerInv σ_outer c) :
    ∀ n, (σ_outer n).isSome → (c.getEnv.store n).isSome := by
  match c with
  | .stmt _ _ => exact hinv
  | .stmts _ _ => exact hinv
  | .terminal _ => exact hinv
  | .exiting _ _ => exact hinv
  | .block _ _ inner =>
    obtain ⟨_, hinner⟩ := hinv
    simp [Config.getEnv]
    exact outerInv_implies_getEnv_isSome σ_outer inner hinner
  | .seq inner _ =>
    simp [Config.getEnv]
    exact outerInv_implies_getEnv_isSome σ_outer inner hinv

/-- Single-step preserves `outerInv σ_outer`. -/
private theorem step_preserves_outerInv
    {σ_outer : SemanticStore Expression} {a b : CC}
    (hstep : StepStmt Expression (EvalCommand π φ) (EvalPureFunc φ) a b)
    (hinv : outerInv σ_outer a) :
    outerInv σ_outer b := by
  induction hstep with
  | step_cmd heval =>
    intro n hout
    simp [outerInv] at hinv
    exact evalCommand_preserves_isSome (π := π) (φ := φ) heval (hinv n hout)
  | step_block => exact ⟨hinv, hinv⟩
  | step_ite_true _ _ => exact hinv
  | step_ite_false _ _ => exact hinv
  | step_ite_nondet_true => exact hinv
  | step_ite_nondet_false => exact hinv
  | step_loop_enter _ _ _ _ _ => exact ⟨hinv, hinv⟩
  | step_loop_exit _ _ _ _ => exact hinv
  | step_loop_nondet_enter _ _ => exact ⟨hinv, hinv⟩
  | step_loop_nondet_exit _ _ => exact hinv
  | step_exit => exact hinv
  | step_funcDecl => exact hinv
  | step_typeDecl => exact hinv
  | step_stmts_nil => exact hinv
  | step_stmts_cons => exact hinv
  | step_seq_inner _ ih => exact ih hinv
  | step_seq_done => exact hinv
  | step_seq_exit => exact hinv
  | step_block_body _ ih =>
    obtain ⟨hpar, hinner⟩ := hinv
    exact ⟨hpar, ih hinner⟩
  | step_block_done =>
    obtain ⟨hpar, hinner⟩ := hinv
    intro n hout
    exact projectStore_isSome (hpar n hout) (hinner n hout)
  | step_block_exit_match _ =>
    obtain ⟨hpar, hinner⟩ := hinv
    intro n hout
    exact projectStore_isSome (hpar n hout) (hinner n hout)
  | step_block_exit_mismatch _ =>
    obtain ⟨hpar, hinner⟩ := hinv
    intro n hout
    exact projectStore_isSome (hpar n hout) (hinner n hout)

/-- Star-step preserves `outerInv σ_outer`. -/
private theorem star_preserves_outerInv
    {σ_outer : SemanticStore Expression} {c₁ c₂ : CC}
    (hstar : CoreStar π φ c₁ c₂)
    (hinv : outerInv σ_outer c₁) :
    outerInv σ_outer c₂ := by
  induction hstar with
  | refl => exact hinv
  | step _ _ _ hstep _ ih => exact ih (step_preserves_outerInv π φ hstep hinv)

/-- Convenient wrapper: if a trace starts from `.stmt s ρ₀`, then variables in
    `ρ₀.store` remain defined throughout the trace. -/
private theorem stmt_star_preserves_isSome
    (s : Stmt Expression Command) (ρ₀ : Env Expression) (c₂ : CC)
    (hstar : CoreStar π φ (.stmt s ρ₀) c₂)
    (x : Expression.Ident) (hx : (ρ₀.store x).isSome) :
    (c₂.getEnv.store x).isSome := by
  have hinv₀ : outerInv ρ₀.store (.stmt s ρ₀) := fun _ h => h
  have hinv₂ := star_preserves_outerInv π φ hstar hinv₀
  exact outerInv_implies_getEnv_isSome ρ₀.store c₂ hinv₂ x hx

/-- Convenient wrapper: if a trace starts from `.stmts ss ρ₀`, then variables in
    `ρ₀.store` remain defined throughout the trace. -/
private theorem stmts_star_preserves_isSome
    (ss : Statements) (ρ₀ : Env Expression) (c₂ : CC)
    (hstar : CoreStar π φ (.stmts ss ρ₀) c₂)
    (x : Expression.Ident) (hx : (ρ₀.store x).isSome) :
    (c₂.getEnv.store x).isSome := by
  have hinv₀ : outerInv ρ₀.store (.stmts ss ρ₀) := fun _ h => h
  have hinv₂ := star_preserves_outerInv π φ hstar hinv₀
  exact outerInv_implies_getEnv_isSome ρ₀.store c₂ hinv₂ x hx

/-- Convenient wrapper: block-level trace from `.block .none σ_p inner`, combined
    with `(σ_outer x).isSome → (σ_p x).isSome`, preserves isSome. -/
private theorem block_none_star_preserves_isSome
    (σ_p : SemanticStore Expression) (inner : CC) (c₂ : CC)
    (hstar : CoreStar π φ (.block .none σ_p inner) c₂)
    (σ_outer : SemanticStore Expression)
    (hpar : ∀ n, (σ_outer n).isSome → (σ_p n).isSome)
    (hinner : outerInv σ_outer inner)
    (x : Expression.Ident) (hx : (σ_outer x).isSome) :
    (c₂.getEnv.store x).isSome := by
  have hinv₀ : outerInv σ_outer (.block .none σ_p inner) := ⟨hpar, hinner⟩
  have hinv₂ := star_preserves_outerInv π φ hstar hinv₀
  exact outerInv_implies_getEnv_isSome σ_outer c₂ hinv₂ x hx

/-! ### Equality of projected store for loop-elim body

    In the loop-elim context, the block's `σ_parent = ρ₀.store` and the body execution
    only touches vars that are already `isSome` in `ρ₀.store` (by `hswf`). Under these
    conditions, `projectStore ρ₀.store ρ_inner.store = ρ_inner.store`, i.e., the block
    projection is a no-op.

    The key insight: `init x` requires `(current.store x) = none`. But `x ∈ definedVars body`
    combined with `hswf` gives `(ρ₀.store x).isSome`, and by `outerInv` this propagates
    to `(current.store x).isSome`. So `init` commands for vars in `definedVars body` NEVER
    fire during execution, meaning no new vars are introduced. -/

/-- `projectStore_self_env` applied at an env with a different store. -/
private theorem env_projectStore_sub {ρ₀ : Env Expression} {σ : SemanticStore Expression}
    (hsub : ∀ x, (σ x).isSome → (ρ₀.store x).isSome) :
    ({ ρ₀ with store := projectStore ρ₀.store σ } : Env Expression) = { ρ₀ with store := σ } := by
  rw [projectStore_sub hsub]

/-- A config's stores have the same isSome domain as σ_outer.
    This is a strengthening of `outerInv`: not only does `σ_outer`'s domain fit in the
    config's store, but the config's store has exactly the same domain.

    Trivially true when σ_outer equals the current store. Preserved by non-init steps.
    For init steps, preserved when the init doesn't fire (which requires the init target
    to already be defined — guaranteed by σ_outer's domain equality). -/
private def sameDomInv (σ_outer : SemanticStore Expression) : CC → Prop
  | .stmt _ ρ => ∀ n, (ρ.store n).isSome ↔ (σ_outer n).isSome
  | .stmts _ ρ => ∀ n, (ρ.store n).isSome ↔ (σ_outer n).isSome
  | .terminal ρ => ∀ n, (ρ.store n).isSome ↔ (σ_outer n).isSome
  | .exiting _ ρ => ∀ n, (ρ.store n).isSome ↔ (σ_outer n).isSome
  | .block _ σ_parent inner =>
    (∀ n, (σ_parent n).isSome ↔ (σ_outer n).isSome) ∧ sameDomInv σ_outer inner
  | .seq inner _ => sameDomInv σ_outer inner

/-- `sameDomInv σ_outer c` implies `∀ n, (c.getEnv.store n).isSome ↔ (σ_outer n).isSome`. -/
private theorem sameDomInv_implies_getEnv_iff (σ_outer : SemanticStore Expression) (c : CC)
    (hinv : sameDomInv σ_outer c) :
    ∀ n, (c.getEnv.store n).isSome ↔ (σ_outer n).isSome := by
  match c with
  | .stmt _ _ => exact hinv
  | .stmts _ _ => exact hinv
  | .terminal _ => exact hinv
  | .exiting _ _ => exact hinv
  | .block _ _ inner =>
    obtain ⟨_, hinner⟩ := hinv
    exact sameDomInv_implies_getEnv_iff σ_outer inner hinner
  | .seq inner _ =>
    exact sameDomInv_implies_getEnv_iff σ_outer inner hinv

/-! ### Syntactic commands collection

    `Stmt.commands` and `Block.commands` collect all atomic commands appearing
    syntactically in a statement / block tree. Used to state and prove the
    trace-reachability invariant for `stmts_star_no_new_vars`. -/

mutual
private def Stmt.commandsIn (s : Stmt Expression Command) : List Command :=
  match s with
  | .cmd c => [c]
  | .block _ bss _ => Block.commandsIn bss
  | .ite _ tss ess _ => Block.commandsIn tss ++ Block.commandsIn ess
  | .loop _ _ _ body _ => Block.commandsIn body
  | _ => []

private def Block.commandsIn (ss : Statements) : List Command :=
  match ss with
  | [] => []
  | s :: rest => Stmt.commandsIn s ++ Block.commandsIn rest
end

mutual
/-- **Lemma 2 (syntactic)**, statement-level version: if a command `c` appears
    syntactically in a statement `s`, then `Cmd.definedVars c ⊆ Stmt.definedVars s`. -/
private theorem Stmt.definedVars_of_commandIn (s : Stmt Expression Command) (c : Command) :
    c ∈ Stmt.commandsIn s →
    ∀ x, x ∈ Imperative.HasVarsImp.definedVars c → x ∈ Stmt.definedVars s := by
  intro hs x hx
  match s with
  | .cmd c' =>
    simp [Stmt.commandsIn] at hs
    subst hs
    simpa [Stmt.definedVars] using hx
  | .block _ bss _ =>
    simp [Stmt.commandsIn] at hs
    have := Block.definedVars_of_commandIn bss c hs x hx
    simpa [Stmt.definedVars] using this
  | .ite _ tss ess _ =>
    simp [Stmt.commandsIn, List.mem_append] at hs
    rcases hs with htss | hess
    · have := Block.definedVars_of_commandIn tss c htss x hx
      simp [Stmt.definedVars]; exact Or.inl this
    · have := Block.definedVars_of_commandIn ess c hess x hx
      simp [Stmt.definedVars]; exact Or.inr this
  | .loop _ _ _ body _ =>
    simp [Stmt.commandsIn] at hs
    have := Block.definedVars_of_commandIn body c hs x hx
    simpa [Stmt.definedVars] using this
  | .exit _ _ => simp [Stmt.commandsIn] at hs
  | .funcDecl _ _ => simp [Stmt.commandsIn] at hs
  | .typeDecl _ _ => simp [Stmt.commandsIn] at hs

/-- **Lemma 2 (syntactic)**: if a command `c` appears syntactically in block `ss`,
    then `Cmd.definedVars c ⊆ Block.definedVars ss`. -/
private theorem Block.definedVars_of_commandIn (ss : Statements) (c : Command) :
    c ∈ Block.commandsIn ss →
    ∀ x, x ∈ Imperative.HasVarsImp.definedVars c → x ∈ Block.definedVars ss := by
  intro hmem x hx
  match ss with
  | [] => simp [Block.commandsIn] at hmem
  | s :: rest =>
    simp only [Block.commandsIn, List.mem_append] at hmem
    rcases hmem with hs | hrest
    · have := Stmt.definedVars_of_commandIn s c hs x hx
      simp [Block.definedVars]; exact Or.inl this
    · have := Block.definedVars_of_commandIn rest c hrest x hx
      simp [Block.definedVars]; exact Or.inr this
end

/-- Collect all commands syntactically present in a config's code structure.
    Does NOT include commands in the env — just the code being executed. -/
private def Config.cmdsIn : CC → List Command
  | .stmt s _ => Stmt.commandsIn s
  | .stmts ss _ => Block.commandsIn ss
  | .terminal _ => []
  | .exiting _ _ => []
  | .block _ _ inner => Config.cmdsIn inner
  | .seq inner ss => Config.cmdsIn inner ++ Block.commandsIn ss

/-- Helper: commands in `Block.commandsIn (ss ++ ss')` split as append. -/
private theorem Block.commandsIn_append (ss ss' : Statements) :
    Block.commandsIn (ss ++ ss') = Block.commandsIn ss ++ Block.commandsIn ss' := by
  induction ss with
  | nil => simp [Block.commandsIn]
  | cons s rest ih => simp [Block.commandsIn, ih, List.append_assoc]

/-- **Lemma 1 (trace reachability)**: if a step `a → b` fires, then all commands in `b`
    appeared in `a`'s syntactic command set. In particular, `step_cmd`'s active command
    was in `a`'s commandsIn. -/
private theorem step_cmdsIn_subset
    {a b : CC} (hstep : StepStmt Expression (EvalCommand π φ) (EvalPureFunc φ) a b) :
    ∀ c, c ∈ Config.cmdsIn b → c ∈ Config.cmdsIn a := by
  induction hstep with
  | step_cmd _ => intro c hc; simp [Config.cmdsIn] at hc
  | step_block => intro c hc; simpa [Config.cmdsIn, Stmt.commandsIn] using hc
  | step_ite_true _ _ =>
    intro c hc
    simp only [Config.cmdsIn, Stmt.commandsIn, List.mem_append]
    exact Or.inl (by simpa [Config.cmdsIn] using hc)
  | step_ite_false _ _ =>
    intro c hc
    simp only [Config.cmdsIn, Stmt.commandsIn, List.mem_append]
    exact Or.inr (by simpa [Config.cmdsIn] using hc)
  | step_ite_nondet_true =>
    intro c hc
    simp only [Config.cmdsIn, Stmt.commandsIn, List.mem_append]
    exact Or.inl (by simpa [Config.cmdsIn] using hc)
  | step_ite_nondet_false =>
    intro c hc
    simp only [Config.cmdsIn, Stmt.commandsIn, List.mem_append]
    exact Or.inr (by simpa [Config.cmdsIn] using hc)
  | step_loop_enter _ _ _ _ _ =>
    intro c hc
    -- b = .seq (.block .none _ (.stmts body _)) [loop]
    -- Config.cmdsIn b = Block.commandsIn body ++ Block.commandsIn [loop]
    --                 = Block.commandsIn body ++ Stmt.commandsIn loop
    --                 = Block.commandsIn body ++ Block.commandsIn body
    -- a = .stmt (.loop ..) ρ, Config.cmdsIn a = Stmt.commandsIn (.loop ..) = Block.commandsIn body
    simp only [Config.cmdsIn, Block.commandsIn, Stmt.commandsIn,
               List.append_nil, List.mem_append] at hc
    simp only [Config.cmdsIn, Stmt.commandsIn]
    rcases hc with h | h
    · exact h
    · exact h
  | step_loop_exit _ _ _ _ => intro c hc; simp [Config.cmdsIn] at hc
  | step_loop_nondet_enter _ _ =>
    intro c hc
    simp only [Config.cmdsIn, Block.commandsIn, Stmt.commandsIn,
               List.append_nil, List.mem_append] at hc
    simp only [Config.cmdsIn, Stmt.commandsIn]
    rcases hc with h | h
    · exact h
    · exact h
  | step_loop_nondet_exit _ _ => intro c hc; simp [Config.cmdsIn] at hc
  | step_exit => intro c hc; simp [Config.cmdsIn] at hc
  | step_funcDecl => intro c hc; simp [Config.cmdsIn] at hc
  | step_typeDecl => intro c hc; simp [Config.cmdsIn] at hc
  | step_stmts_nil => intro c hc; simp [Config.cmdsIn] at hc
  | step_stmts_cons =>
    intro c hc
    simp only [Config.cmdsIn, List.mem_append] at hc
    simp only [Config.cmdsIn, Block.commandsIn, List.mem_append]
    exact hc
  | step_seq_inner _ ih =>
    intro c hc
    simp only [Config.cmdsIn, List.mem_append] at hc
    simp only [Config.cmdsIn, List.mem_append]
    rcases hc with h | h
    · exact Or.inl (ih c h)
    · exact Or.inr h
  | step_seq_done => intro c hc; simpa [Config.cmdsIn] using hc
  | step_seq_exit => intro c hc; simp [Config.cmdsIn] at hc
  | step_block_body _ ih => intro c hc; simp [Config.cmdsIn] at hc ⊢; exact ih c hc
  | step_block_done => intro c hc; simp [Config.cmdsIn] at hc
  | step_block_exit_match _ => intro c hc; simp [Config.cmdsIn] at hc
  | step_block_exit_mismatch _ => intro c hc; simp [Config.cmdsIn] at hc

/-- Star version: commands only shrink along a trace. -/
private theorem star_cmdsIn_subset
    {a b : CC} (hstar : CoreStar π φ a b) :
    ∀ c, c ∈ Config.cmdsIn b → c ∈ Config.cmdsIn a := by
  induction hstar with
  | refl => exact fun _ h => h
  | step _ _ _ hstep _ ih => exact fun c hc => step_cmdsIn_subset π φ hstep c (ih c hc)

/-- A step that fires `step_cmd` has its command in the current config's `cmdsIn`. -/
private theorem step_cmd_in_cmdsIn
    {a b : CC} {c : Command} {σ' : CoreStore} {f : Bool}
    (hstep : StepStmt Expression (EvalCommand π φ) (EvalPureFunc φ) a b)
    (hform : ∃ ρ, a = .stmt (.cmd c) ρ) :
    c ∈ Config.cmdsIn a := by
  obtain ⟨ρ, rfl⟩ := hform
  simp [Config.cmdsIn, Stmt.commandsIn]

/-- `Stmt.definedVars s ⊆ Stmt.modifiedOrDefinedVars s` / `Block.definedVars ss ⊆
    Block.modifiedOrDefinedVars ss`. Purely syntactic. Proved by strong induction on
    the combined `Stmt.sizeOf`/`Block.sizeOf`. -/
private theorem definedVars_subset_modifiedOrDefinedVars (sz : Nat) :
    (∀ (s : Stmt Expression Command), Stmt.sizeOf s ≤ sz →
      ∀ x, x ∈ Stmt.definedVars s → x ∈ Stmt.modifiedOrDefinedVars s) ∧
    (∀ (ss : Statements), Block.sizeOf ss ≤ sz →
      ∀ x, x ∈ Block.definedVars ss → x ∈ Block.modifiedOrDefinedVars ss) := by
  induction sz with
  | zero =>
    refine ⟨?_, ?_⟩
    · intro s hsz; match s with
      | .cmd _ => exact absurd hsz (by simp [Stmt.sizeOf])
      | .block .. => exact absurd hsz (by simp [Stmt.sizeOf])
      | .ite .. => exact absurd hsz (by simp [Stmt.sizeOf])
      | .loop .. => exact absurd hsz (by simp [Stmt.sizeOf])
      | .exit .. => exact absurd hsz (by simp [Stmt.sizeOf])
      | .funcDecl .. => exact absurd hsz (by simp [Stmt.sizeOf])
      | .typeDecl .. => exact absurd hsz (by simp [Stmt.sizeOf])
    · intro ss hsz
      match ss with
      | [] => intro _ hx; simp [Block.definedVars] at hx
      | _ :: _ => exact absurd hsz (by simp [Block.sizeOf])
  | succ m ih =>
    refine ⟨?_, ?_⟩
    · intro s hsz x hx
      match s with
      | .cmd _ =>
        simp only [Stmt.modifiedOrDefinedVars, List.mem_append]
        exact Or.inl hx
      | .block _ bss _ =>
        simp only [Stmt.modifiedOrDefinedVars]
        have hsz_bss : Block.sizeOf bss ≤ m := by simp [Stmt.sizeOf] at hsz; omega
        exact ih.2 bss hsz_bss x (by simpa [Stmt.definedVars] using hx)
      | .ite _ tss ess _ =>
        simp only [Stmt.modifiedOrDefinedVars, List.mem_append]
        simp only [Stmt.definedVars, List.mem_append] at hx
        have hsz_tss : Block.sizeOf tss ≤ m := by simp [Stmt.sizeOf] at hsz; omega
        have hsz_ess : Block.sizeOf ess ≤ m := by simp [Stmt.sizeOf] at hsz; omega
        rcases hx with h | h
        · exact Or.inl (ih.2 tss hsz_tss x h)
        · exact Or.inr (ih.2 ess hsz_ess x h)
      | .loop _ _ _ _ _ =>
        simp only [Stmt.modifiedOrDefinedVars, List.mem_append]
        exact Or.inl hx
      | .exit _ _ =>
        simp only [Stmt.modifiedOrDefinedVars, List.mem_append]
        exact Or.inl hx
      | .funcDecl _ _ =>
        simp only [Stmt.modifiedOrDefinedVars, List.mem_append]
        exact Or.inl hx
      | .typeDecl _ _ =>
        simp only [Stmt.modifiedOrDefinedVars, List.mem_append]
        exact Or.inl hx
    · intro ss hsz x hx
      match ss with
      | [] => simp [Block.definedVars] at hx
      | s :: rest =>
        simp only [Block.definedVars, List.mem_append] at hx
        simp only [Block.modifiedOrDefinedVars, List.mem_append]
        have hsz_s : Stmt.sizeOf s ≤ m := by simp [Block.sizeOf] at hsz; omega
        have hsz_rest : Block.sizeOf rest ≤ m := by simp [Block.sizeOf] at hsz; omega
        rcases hx with h | h
        · exact Or.inl (ih.1 s hsz_s x h)
        · exact Or.inr (ih.2 rest hsz_rest x h)

/-! ### "No new variables" helpers for `stmts_star_no_new_vars` -/

/-- `UpdateState` preserves the store domain in the reverse direction as well:
    if `σ'` has variable `n` defined, so did `σ`. -/
private theorem updateState_no_new_vars
    {σ σ' : CoreStore} {x : Expression.Ident} {v : Expression.Expr}
    (hup : UpdateState Expression σ x v σ')
    {n : Expression.Ident}
    (hn : (σ' n).isSome) : (σ n).isSome := by
  cases hup with
  | update hold hnew hframe =>
    by_cases heq : x = n
    · subst heq; simp [hold]
    · have : σ' n = σ n := hframe n heq
      simp [this] at hn; exact hn

/-- `UpdateStates` preserves the store domain in the reverse direction. -/
private theorem updateStates_no_new_vars
    {σ σ' : CoreStore} {xs : List Expression.Ident} {vs : List Expression.Expr}
    (hups : UpdateStates σ xs vs σ')
    {n : Expression.Ident}
    (hn : (σ' n).isSome) : (σ n).isSome := by
  induction hups with
  | update_none => exact hn
  | update_some hup _ ih => exact updateState_no_new_vars hup (ih hn)

/-- `EvalCmd` preserves the store domain in the reverse direction, provided the
    command's `definedVars` are already defined in `σ` (which blocks `init` from firing
    for any new variable). -/
private theorem evalCmd_no_new_vars
    {δ : CoreEval} {σ σ' : CoreStore} {c : Cmd Expression} {f : Bool}
    (heval : EvalCmd (P := Expression) δ σ c σ' f)
    (hdef_old : ∀ y ∈ Cmd.definedVars c, (σ y).isSome)
    {n : Expression.Ident}
    (hn : (σ' n).isSome) : (σ n).isSome := by
  cases heval with
  | eval_init _ hinit _ =>
    -- InitState requires σ x = none, but x ∈ Cmd.definedVars (.init x ..) = [x],
    -- so hdef_old gives (σ x).isSome, a contradiction.
    cases hinit with
    | init hnone _ _ =>
      have hx := hdef_old _ (show _ ∈ [_] from List.mem_singleton.mpr rfl)
      rw [hnone] at hx; exact absurd hx (by simp)
  | eval_init_unconstrained hinit _ =>
    cases hinit with
    | init hnone _ _ =>
      have hx := hdef_old _ (show _ ∈ [_] from List.mem_singleton.mpr rfl)
      rw [hnone] at hx; exact absurd hx (by simp)
  | eval_set _ hup _ => exact updateState_no_new_vars hup hn
  | eval_set_nondet hup _ => exact updateState_no_new_vars hup hn
  | eval_assert_pass _ _ => exact hn
  | eval_assert_fail _ _ => exact hn
  | eval_assume _ _ => exact hn
  | eval_cover _ => exact hn

/-- `EvalCommand` preserves the store domain in the reverse direction, provided the
    command's `definedVars` are already defined in `ρ.store`. -/
private theorem evalCommand_no_new_vars
    {ρ : Env Expression} {c : Command} {σ' : CoreStore} {f : Bool}
    (heval : EvalCommand π φ ρ.eval ρ.store c σ' f)
    (hdef_old : ∀ y ∈ Imperative.HasVarsImp.definedVars c, (ρ.store y).isSome)
    {n : Expression.Ident}
    (hn : (σ' n).isSome) : (ρ.store n).isSome := by
  cases heval with
  | cmd_sem hcmd =>
    apply evalCmd_no_new_vars hcmd ?_ hn
    intro y hy
    apply hdef_old
    show y ∈ Command.definedVars (CmdExt.cmd _)
    simpa [Command.definedVars] using hy
  | call_sem _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hups =>
    exact updateStates_no_new_vars hups hn

/-- Single-step "no new vars" lemma under the `outerInv σ_outer` invariant.
    If `σ_outer` already contains all the command-definedVars reachable from the current
    config (as captured by `hdef_safe`), then a step cannot introduce new variables. -/
private theorem step_no_new_vars
    {σ_outer : SemanticStore Expression} {a b : CC}
    (hstep : StepStmt Expression (EvalCommand π φ) (EvalPureFunc φ) a b)
    (hinv : outerInv σ_outer a)
    (hdef_safe : ∀ c ∈ Config.cmdsIn a, ∀ y ∈ Imperative.HasVarsImp.definedVars c,
      (σ_outer y).isSome)
    {n : Expression.Ident}
    (hn : (b.getEnv.store n).isSome) : (a.getEnv.store n).isSome := by
  induction hstep with
  | step_cmd heval =>
    -- a = .stmt (.cmd cmd) ρ, b = .terminal { ρ with store := σ'', .. }
    simp only [Config.getEnv] at hn ⊢
    rename_i cmd σ'' f ρ
    have hc_in : cmd ∈ Config.cmdsIn (Config.stmt (Stmt.cmd cmd) ρ) := by
      simp [Config.cmdsIn, Stmt.commandsIn]
    have hdef_local : ∀ y ∈ Imperative.HasVarsImp.definedVars cmd,
        (ρ.store y).isSome := fun y hy => by
      have hout := hdef_safe cmd hc_in y hy
      simp only [outerInv] at hinv
      exact hinv y hout
    exact evalCommand_no_new_vars (π := π) (φ := φ) heval hdef_local hn
  | step_block => exact hn
  | step_ite_true _ _ => exact hn
  | step_ite_false _ _ => exact hn
  | step_ite_nondet_true => exact hn
  | step_ite_nondet_false => exact hn
  | step_loop_enter _ _ _ _ _ => exact hn
  | step_loop_exit _ _ _ _ => exact hn
  | step_loop_nondet_enter _ _ => exact hn
  | step_loop_nondet_exit _ _ => exact hn
  | step_exit => exact hn
  | step_funcDecl => simpa [Config.getEnv] using hn
  | step_typeDecl => exact hn
  | step_stmts_nil => exact hn
  | step_stmts_cons => exact hn
  | step_seq_inner hstep_inner ih =>
    -- a = .seq inner ss, b = .seq inner' ss
    -- hn : b.getEnv.store n isSome. Need a.getEnv.store n isSome.
    simp only [Config.getEnv] at hn ⊢
    apply ih hinv ?_ hn
    intro c hc y hy
    apply hdef_safe c ?_ y hy
    simp only [Config.cmdsIn, List.mem_append]; exact Or.inl hc
  | step_seq_done => exact hn
  | step_seq_exit => simpa [Config.getEnv] using hn
  | step_block_body _ ih =>
    -- a = .block l σ_parent inner, b = .block l σ_parent inner'
    simp only [Config.getEnv] at hn ⊢
    obtain ⟨_, hinner⟩ := hinv
    apply ih hinner ?_ hn
    intro c hc y hy
    apply hdef_safe c ?_ y hy
    simp only [Config.cmdsIn]; exact hc
  | step_block_done =>
    -- b.store = projectStore σ_parent ρ'.store
    -- a = .block .none σ_parent (.terminal ρ'), a.getEnv.store = σ_parent
    obtain ⟨_, _⟩ := hinv
    simp only [Config.getEnv] at hn ⊢
    simp only [projectStore] at hn
    split at hn
    · assumption
    · simp at hn
  | step_block_exit_match _ =>
    obtain ⟨_, _⟩ := hinv
    simp only [Config.getEnv] at hn ⊢
    simp only [projectStore] at hn
    split at hn
    · assumption
    · simp at hn
  | step_block_exit_mismatch _ =>
    obtain ⟨_, _⟩ := hinv
    simp only [Config.getEnv] at hn ⊢
    simp only [projectStore] at hn
    split at hn
    · assumption
    · simp at hn

/-- Star-step "no new vars" lemma. Follows by iterating `step_no_new_vars`. -/
private theorem star_no_new_vars
    {σ_outer : SemanticStore Expression} {a b : CC}
    (hstar : CoreStar π φ a b)
    (hinv : outerInv σ_outer a)
    (hdef_safe : ∀ c ∈ Config.cmdsIn a, ∀ y ∈ Imperative.HasVarsImp.definedVars c,
      (σ_outer y).isSome)
    {n : Expression.Ident}
    (hn : (b.getEnv.store n).isSome) : (a.getEnv.store n).isSome := by
  induction hstar with
  | refl => exact hn
  | step _ _ _ hstep _ ih =>
    apply step_no_new_vars (π := π) (φ := φ) hstep hinv hdef_safe
    apply ih (step_preserves_outerInv π φ hstep hinv)
    · intro c hc y hy
      exact hdef_safe c (step_cmdsIn_subset π φ hstep c hc) y hy
    · exact hn

/-- **Key lemma**: For a trace `.stmts ss ρ₀ →* .terminal ρ'`, if all
    `modifiedOrDefinedVars ss` are already isSome in `ρ₀.store` (`hswf`), then no new
    variables are introduced during execution. -/
private theorem stmts_star_no_new_vars
    (ss : Statements) (ρ₀ ρ' : Env Expression)
    (hstar : CoreStar π φ (.stmts ss ρ₀) (.terminal ρ'))
    (hswf : ∀ n ∈ Block.modifiedOrDefinedVars ss, (ρ₀.store n).isSome)
    (_hnofd : Block.noFuncDecl ss = Bool.true) :
    ∀ x, (ρ'.store x).isSome → (ρ₀.store x).isSome := by
  intro x hx
  -- outerInv ρ₀.store (.stmts ss ρ₀) holds trivially
  have hinv₀ : outerInv ρ₀.store (.stmts ss ρ₀) := fun _ h => h
  -- For any command appearing in ss, its definedVars ⊆ Block.definedVars ss
  -- ⊆ Block.modifiedOrDefinedVars ss ⊆ ρ₀.store (via hswf)
  have hdef_safe : ∀ c ∈ Config.cmdsIn (Config.stmts ss ρ₀),
      ∀ y ∈ Imperative.HasVarsImp.definedVars c, (ρ₀.store y).isSome := by
    intro c hc y hy
    have hy_block : y ∈ Block.definedVars ss := by
      simp only [Config.cmdsIn] at hc
      exact Block.definedVars_of_commandIn ss c hc y hy
    have hy_mod : y ∈ Block.modifiedOrDefinedVars ss := by
      have hsz : Block.sizeOf ss ≤ Block.sizeOf ss := Nat.le_refl _
      exact (definedVars_subset_modifiedOrDefinedVars (Block.sizeOf ss)).2 ss hsz y hy_block
    exact hswf y hy_mod
  -- Apply star_no_new_vars
  have := star_no_new_vars (π := π) (φ := φ) hstar hinv₀ hdef_safe (n := x)
  simp only [Config.getEnv] at this
  exact this hx

/-- Corollary: at a block exit in the loop-elim context, `projectStore` is the identity. -/
private theorem projectStore_body_exit_eq
    (body : Statements) (ρ₀ ρ_body : Env Expression)
    (hstar : CoreStar π φ (.stmts body ρ₀) (.terminal ρ_body))
    (hswf : ∀ n ∈ Block.modifiedOrDefinedVars body, (ρ₀.store n).isSome)
    (hnofd : Block.noFuncDecl body = Bool.true) :
    projectStore ρ₀.store ρ_body.store = ρ_body.store := by
  exact projectStore_sub (stmts_star_no_new_vars π φ body ρ₀ ρ_body hstar hswf hnofd)

/-- Analog of `stmts_star_no_new_vars` for `.exiting` targets. -/
private theorem stmts_star_exiting_no_new_vars
    (ss : Statements) (ρ₀ ρ' : Env Expression) (lbl : String)
    (hstar : CoreStar π φ (.stmts ss ρ₀) (.exiting lbl ρ'))
    (hswf : ∀ n ∈ Block.modifiedOrDefinedVars ss, (ρ₀.store n).isSome)
    (_hnofd : Block.noFuncDecl ss = Bool.true) :
    ∀ x, (ρ'.store x).isSome → (ρ₀.store x).isSome := by
  intro x hx
  have hinv₀ : outerInv ρ₀.store (.stmts ss ρ₀) := fun _ h => h
  have hdef_safe : ∀ c ∈ Config.cmdsIn (Config.stmts ss ρ₀),
      ∀ y ∈ Imperative.HasVarsImp.definedVars c, (ρ₀.store y).isSome := by
    intro c hc y hy
    have hy_block : y ∈ Block.definedVars ss := by
      simp only [Config.cmdsIn] at hc
      exact Block.definedVars_of_commandIn ss c hc y hy
    have hy_mod : y ∈ Block.modifiedOrDefinedVars ss := by
      have hsz : Block.sizeOf ss ≤ Block.sizeOf ss := Nat.le_refl _
      exact (definedVars_subset_modifiedOrDefinedVars (Block.sizeOf ss)).2 ss hsz y hy_block
    exact hswf y hy_mod
  have := star_no_new_vars (π := π) (φ := φ) hstar hinv₀ hdef_safe (n := x)
  simp only [Config.getEnv] at this
  exact this hx

/-- Corollary for exiting: `projectStore` is the identity when exiting a body. -/
private theorem projectStore_body_exiting_eq
    (body : Statements) (ρ₀ ρ_body : Env Expression) (lbl : String)
    (hstar : CoreStar π φ (.stmts body ρ₀) (.exiting lbl ρ_body))
    (hswf : ∀ n ∈ Block.modifiedOrDefinedVars body, (ρ₀.store n).isSome)
    (hnofd : Block.noFuncDecl body = Bool.true) :
    projectStore ρ₀.store ρ_body.store = ρ_body.store :=
  projectStore_sub (stmts_star_exiting_no_new_vars π φ body ρ₀ ρ_body lbl hstar hswf hnofd)

/-- `Block.noFuncDecl (body ++ [loop body]) = true` when `Block.noFuncDecl body = true`. -/
private theorem noFuncDecl_body_append_loop
    (guard : ExprOrNondet Expression) (measure : Option Expression.Expr)
    (inv : List (String × Expression.Expr))
    (body : Statements) (md : MetaData Expression)
    (hnofd : Block.noFuncDecl body = Bool.true) :
    Block.noFuncDecl (body ++ [.loop guard measure inv body md]) = Bool.true := by
  have h_append : ∀ (ss₁ ss₂ : Statements),
      Block.noFuncDecl ss₁ = Bool.true → Block.noFuncDecl ss₂ = Bool.true →
      Block.noFuncDecl (ss₁ ++ ss₂) = Bool.true := by
    intro ss₁; induction ss₁ with
    | nil => intro _ _ h; exact h
    | cons s ss ih =>
      intro ss₂ h₁ h₂
      simp only [Block.noFuncDecl] at h₁ ⊢
      cases hs : Stmt.noFuncDecl s
      · simp [hs] at h₁
      · simp_all [Block.noFuncDecl]
  exact h_append _ _ hnofd (by simp [Block.noFuncDecl, Stmt.noFuncDecl, hnofd])

/-- `Block.modifiedVars` is a subset of `Block.modifiedOrDefinedVars` (local version). -/
private theorem modifiedVars_subset_modifiedOrDefinedVars' (sz : Nat) :
    (∀ (s : Statement), Stmt.sizeOf s ≤ sz →
      ∀ n, n ∈ Stmt.modifiedVars s → n ∈ Stmt.modifiedOrDefinedVars s) ∧
    (∀ (ss : Statements), Block.sizeOf ss ≤ sz →
      ∀ n, n ∈ Block.modifiedVars ss → n ∈ Block.modifiedOrDefinedVars ss) := by
  induction sz with
  | zero =>
    constructor
    · intro s hsz; match s with
      | .cmd _ => exact absurd hsz (by simp [Stmt.sizeOf])
      | .block .. => exact absurd hsz (by simp [Stmt.sizeOf])
      | .ite .. => exact absurd hsz (by simp [Stmt.sizeOf])
      | .loop .. => exact absurd hsz (by simp [Stmt.sizeOf])
      | .exit .. => exact absurd hsz (by simp [Stmt.sizeOf])
      | .funcDecl .. => exact absurd hsz (by simp [Stmt.sizeOf])
      | .typeDecl .. => exact absurd hsz (by simp [Stmt.sizeOf])
    · intro ss hsz; match ss with
      | [] => intro n hn; exact hn
      | _ :: _ => exact absurd hsz (by simp [Block.sizeOf])
  | succ m ih =>
    refine ⟨?_, ?_⟩
    · intro s hsz n hn_mem
      match s with
      | .cmd _ =>
        simp only [Stmt.modifiedOrDefinedVars, Stmt.modifiedVars, List.mem_append] at hn_mem ⊢
        exact Or.inr hn_mem
      | .block _ bss _ =>
        simp only [Stmt.modifiedOrDefinedVars, Stmt.modifiedVars] at hn_mem ⊢
        have hsz_bss : Block.sizeOf bss ≤ m := by simp [Stmt.sizeOf] at hsz; omega
        exact ih.2 bss hsz_bss n hn_mem
      | .ite _ tss ess _ =>
        simp only [Stmt.modifiedOrDefinedVars, Stmt.modifiedVars, List.mem_append] at hn_mem ⊢
        have hsz_tss : Block.sizeOf tss ≤ m := by simp [Stmt.sizeOf] at hsz; omega
        have hsz_ess : Block.sizeOf ess ≤ m := by simp [Stmt.sizeOf] at hsz; omega
        rcases hn_mem with h | h
        · exact Or.inl (ih.2 tss hsz_tss n h)
        · exact Or.inr (ih.2 ess hsz_ess n h)
      | .loop _ _ _ bss _ =>
        simp only [Stmt.modifiedOrDefinedVars, Stmt.definedVars, Stmt.modifiedVars,
          List.mem_append] at hn_mem ⊢
        exact Or.inr hn_mem
      | .exit _ _ =>
        simp only [Stmt.modifiedOrDefinedVars, Stmt.modifiedVars, Stmt.definedVars,
          List.mem_append] at hn_mem ⊢
        exact absurd hn_mem (by simp)
      | .funcDecl _ _ =>
        simp only [Stmt.modifiedOrDefinedVars, Stmt.modifiedVars, List.mem_append] at hn_mem ⊢
        exact Or.inr hn_mem
      | .typeDecl _ _ =>
        simp only [Stmt.modifiedOrDefinedVars, Stmt.modifiedVars, List.mem_append] at hn_mem ⊢
        exact Or.inr hn_mem
    · intro ss hsz x hx
      match ss with
      | [] => simp [Block.modifiedVars] at hx
      | s :: rest =>
        simp only [Block.modifiedVars, List.mem_append] at hx
        simp only [Block.modifiedOrDefinedVars, List.mem_append]
        have hsz_s : Stmt.sizeOf s ≤ m := by simp [Block.sizeOf] at hsz; omega
        have hsz_rest : Block.sizeOf rest ≤ m := by simp [Block.sizeOf] at hsz; omega
        rcases hx with h | h
        · exact Or.inl (ih.1 s hsz_s x h)
        · exact Or.inr (ih.2 rest hsz_rest x h)

/-- `Block.modifiedOrDefinedVars` distributes over append. -/
private theorem Block_modifiedOrDefinedVars_append (ss₁ ss₂ : Statements) :
    Block.modifiedOrDefinedVars (ss₁ ++ ss₂) =
      Block.modifiedOrDefinedVars ss₁ ++ Block.modifiedOrDefinedVars ss₂ := by
  induction ss₁ with
  | nil => simp [Block.modifiedOrDefinedVars]
  | cons s rest ih =>
    simp only [List.cons_append, Block.modifiedOrDefinedVars, ih, List.append_assoc]

/-- If `n ∈ Block.modifiedOrDefinedVars (body ++ [loop body])`, then
    `n ∈ Block.modifiedOrDefinedVars body`. -/
private theorem mem_mod_def_body_append_loop
    {guard : ExprOrNondet Expression} {measure : Option Expression.Expr}
    {inv : List (String × Expression.Expr)}
    {body : Statements} {md : MetaData Expression}
    {n : Expression.Ident}
    (hmem : n ∈ Block.modifiedOrDefinedVars
      (body ++ [.loop guard measure inv body md])) :
    n ∈ Block.modifiedOrDefinedVars body := by
  rw [Block_modifiedOrDefinedVars_append] at hmem
  rcases List.mem_append.mp hmem with h | h
  · exact h
  · simp only [Block.modifiedOrDefinedVars, Stmt.modifiedOrDefinedVars,
               Stmt.definedVars, Stmt.modifiedVars, List.append_nil] at h
    rcases List.mem_append.mp h with hdef | hmod
    · have hsz : Block.sizeOf body ≤ Block.sizeOf body := Nat.le_refl _
      exact (definedVars_subset_modifiedOrDefinedVars (Block.sizeOf body)).2 body hsz n hdef
    · have hsz : Block.sizeOf body ≤ Block.sizeOf body := Nat.le_refl _
      exact (modifiedVars_subset_modifiedOrDefinedVars' (Block.sizeOf body)).2 body hsz n hmod


/-! ### Single step preserves store outside touched vars

    The unrestricted version (`c₂.getEnv.store x = c₁.getEnv.store x` assuming only
    `x ∉ Config.touchedVarsSet c₁`) is NOT provable after the `projectStore` semantics
    change: on block-exit steps the projection can silently drop variables that were
    defined inside the block. We instead provide a version strengthened with an
    `outerInv σ_outer c₁` hypothesis plus `(σ_outer x).isSome`, under which all block
    cases hold via `projectStore_isSome`. -/

/-- Single-step version of store preservation outside touchedVars, strengthened with
    `outerInv σ_outer c₁` and `(σ_outer x).isSome`. Under these hypotheses, the
    block-exit cases become provable because `σ_parent` contains `σ_outer`. -/
private theorem step_preserves_store_outside_touchedVars_outerInv
    (σ_outer : SemanticStore Expression)
    (c₁ c₂ : CC)
    (hstep : StepStmt Expression (EvalCommand π φ) (EvalPureFunc φ) c₁ c₂)
    (hinv : outerInv σ_outer c₁)
    (x : Expression.Ident)
    (hout : (σ_outer x).isSome)
    (hx : x ∉ Config.touchedVarsSet c₁) :
    c₂.getEnv.store x = c₁.getEnv.store x := by
  induction hstep with
  | step_cmd heval =>
    have hmod : x ∉ Stmt.modifiedVars (Stmt.cmd ‹Command›) :=
      fun hmem => hx (show x ∈ Config.touchedVarsSet _ by
        simp only [Config.touchedVarsSet]; exact List.mem_append_left _ hmem)
    have hdef : x ∉ Stmt.definedVars (Stmt.cmd ‹Command›) :=
      fun hmem => hx (show x ∈ Config.touchedVarsSet _ by
        simp only [Config.touchedVarsSet]; exact List.mem_append_right _ hmem)
    exact evalCommand_store_frame_stmt (π := π) (φ := φ) heval hmod hdef
  | step_block => rfl
  | step_ite_true _ _ => rfl
  | step_ite_false _ _ => rfl
  | step_ite_nondet_true => rfl
  | step_ite_nondet_false => rfl
  | step_loop_enter _ _ _ _ _ => rfl
  | step_loop_exit _ _ _ _ => rfl
  | step_loop_nondet_enter _ _ => rfl
  | step_loop_nondet_exit _ _ => rfl
  | step_exit => rfl
  | step_funcDecl => simp [Config.getEnv]
  | step_typeDecl => rfl
  | step_stmts_nil => rfl
  | step_stmts_cons => rfl
  | step_seq_inner _ ih =>
    exact ih hinv (fun hmem => hx (by
      simp only [Config.touchedVarsSet, List.mem_append]
      left; left; exact hmem))
  | step_seq_done => rfl
  | step_seq_exit => rfl
  | step_block_body _ ih =>
    simp only [Config.getEnv, Config.touchedVarsSet] at hx ⊢
    obtain ⟨_, hinner⟩ := hinv
    exact ih hinner hx
  | step_block_done =>
    -- c₁ = .block l σ_parent (.terminal ρ'), c₂.store x = projectStore σ_parent ρ'.store x
    -- From hinv, σ_outer ⊆ σ_parent domain-wise, so (σ_parent x).isSome holds.
    obtain ⟨hpar, _⟩ := hinv
    simp only [Config.getEnv]
    have hp : (σ_outer x).isSome → _ := hpar x
    simp [projectStore, hpar x hout]
  | step_block_exit_match _ =>
    obtain ⟨hpar, _⟩ := hinv
    simp only [Config.getEnv]
    simp [projectStore, hpar x hout]
  | step_block_exit_mismatch _ =>
    obtain ⟨hpar, _⟩ := hinv
    simp only [Config.getEnv]
    simp [projectStore, hpar x hout]

/-! ### Step monotonicity: touched vars of c₂ ⊆ touched vars of c₁ -/

private theorem step_touchedVars_subset
    (c₁ c₂ : CC)
    (hstep : StepStmt Expression (EvalCommand π φ) (EvalPureFunc φ) c₁ c₂) :
    ∀ x, x ∈ Config.touchedVarsSet c₂ → x ∈ Config.touchedVarsSet c₁ := by
  intro x hx
  induction hstep with
  | step_cmd _ => simp [Config.touchedVarsSet] at hx
  | step_block =>
    -- c₁ = .stmt (.block l ss md) ρ, c₂ = .block (.some l) (.stmts ss ρ)
    -- touchedVarsSet c₁ = Stmt.modifiedVars (.block l ss md) ++ Stmt.definedVars (.block l ss md)
    --                    = Block.modifiedVars ss ++ Block.definedVars ss
    -- touchedVarsSet c₂ = Config.touchedVarsSet (.stmts ss ρ)
    --                    = Block.modifiedVars ss ++ Block.definedVars ss
    simp only [Config.touchedVarsSet, Stmt.modifiedVars, Stmt.definedVars] at hx ⊢
    exact hx
  | step_ite_true _ _ =>
    simp only [Config.touchedVarsSet, Stmt.modifiedVars, Stmt.definedVars,
      List.mem_append] at hx ⊢
    cases hx with
    | inl h => left; left; exact h
    | inr h => right; left; exact h
  | step_ite_false _ _ =>
    simp only [Config.touchedVarsSet, Stmt.modifiedVars, Stmt.definedVars,
      List.mem_append] at hx ⊢
    cases hx with
    | inl h => left; right; exact h
    | inr h => right; right; exact h
  | step_ite_nondet_true =>
    simp only [Config.touchedVarsSet, Stmt.modifiedVars, Stmt.definedVars,
      List.mem_append] at hx ⊢
    cases hx with
    | inl h => left; left; exact h
    | inr h => right; left; exact h
  | step_ite_nondet_false =>
    simp only [Config.touchedVarsSet, Stmt.modifiedVars, Stmt.definedVars,
      List.mem_append] at hx ⊢
    cases hx with
    | inl h => left; right; exact h
    | inr h => right; right; exact h
  | step_loop_enter _ _ _ _ _ =>
    -- c₁ = .stmt (.loop g m inv body md) ρ
    -- c₂ = .seq (.block .none _ (.stmts body ρ')) [.loop g m inv body md]
    -- touchedVarsSet c₁ = Block.modifiedVars body ++ Block.definedVars body
    -- touchedVarsSet c₂ = (Block.modifiedVars body ++ Block.definedVars body)
    --                    ++ Block.modifiedVars [loop] ++ Block.definedVars [loop]
    --   where Block.modifiedVars [loop] = Block.modifiedVars body, similarly for defs
    simp only [Config.touchedVarsSet, Stmt.modifiedVars, Stmt.definedVars,
               Block.modifiedVars, Block.definedVars,
               List.append_nil, List.mem_append] at hx ⊢
    rcases hx with ((h | h) | h) | h
    · exact .inl h
    · exact .inr h
    · exact .inl h
    · exact .inr h
  | step_loop_exit _ _ _ _ => simp [Config.touchedVarsSet] at hx
  | step_loop_nondet_enter _ _ =>
    simp only [Config.touchedVarsSet, Stmt.modifiedVars, Stmt.definedVars,
               Block.modifiedVars, Block.definedVars,
               List.append_nil, List.mem_append] at hx ⊢
    rcases hx with ((h | h) | h) | h
    · exact .inl h
    · exact .inr h
    · exact .inl h
    · exact .inr h
  | step_loop_nondet_exit _ _ => simp [Config.touchedVarsSet] at hx
  | step_exit => simp [Config.touchedVarsSet] at hx
  | step_funcDecl => simp [Config.touchedVarsSet] at hx
  | step_typeDecl => simp [Config.touchedVarsSet] at hx
  | step_stmts_nil => simp [Config.touchedVarsSet] at hx
  | step_stmts_cons =>
    -- c₁ = .stmts (s :: ss) ρ, c₂ = .seq (.stmt s ρ) ss
    -- touchedVarsSet c₁ = Block.modifiedVars (s :: ss) ++ Block.definedVars (s :: ss)
    --   = (Stmt.modifiedVars s ++ Block.modifiedVars ss) ++ (Stmt.definedVars s ++ Block.definedVars ss)
    -- touchedVarsSet c₂ = touchedVarsSet (.stmt s ρ) ++ Block.modifiedVars ss ++ Block.definedVars ss
    --   = (Stmt.modifiedVars s ++ Stmt.definedVars s) ++ Block.modifiedVars ss ++ Block.definedVars ss
    simp only [Config.touchedVarsSet, Block.modifiedVars, Block.definedVars, List.mem_append] at hx ⊢
    -- Both contain exactly Stmt.modifiedVars s, Stmt.definedVars s, Block.modifiedVars ss, Block.definedVars ss
    rcases hx with ((h | h) | h) | h
    · left; left; exact h
    · right; left; exact h
    · left; right; exact h
    · right; right; exact h
  | step_seq_inner _ ih =>
    -- c₂ = .seq inner' ss, c₁ = .seq inner ss
    -- touchedVarsSet = touchedVarsSet inner_x ++ Block.modifiedVars ss ++ Block.definedVars ss
    -- x is in c₂'s touched vars. Show it's in c₁'s touched vars.
    -- Strategy: if x is in inner' part, use ih. Otherwise pass through.
    simp only [Config.touchedVarsSet] at hx ⊢
    -- hx : x ∈ (Config.touchedVarsSet inner' ++ Block.modifiedVars ss ++ Block.definedVars ss)
    -- goal : x ∈ (Config.touchedVarsSet inner ++ Block.modifiedVars ss ++ Block.definedVars ss)
    have hmem := List.mem_append.mp hx
    cases hmem with
    | inl h =>
      have hmem2 := List.mem_append.mp h
      cases hmem2 with
      | inl h2 =>
        exact List.mem_append.mpr (.inl (List.mem_append.mpr (.inl (ih h2))))
      | inr h2 =>
        exact List.mem_append.mpr (.inl (List.mem_append.mpr (.inr h2)))
    | inr h =>
      exact List.mem_append.mpr (.inr h)
  | step_seq_done =>
    simp only [Config.touchedVarsSet, List.mem_append, List.not_mem_nil, false_or] at hx ⊢
    exact hx
  | step_seq_exit =>
    simp [Config.touchedVarsSet] at hx
  | step_block_body _ ih =>
    simp only [Config.touchedVarsSet] at hx ⊢
    exact ih hx
  | step_block_done => simp [Config.touchedVarsSet] at hx
  | step_block_exit_match _ => simp [Config.touchedVarsSet] at hx
  | step_block_exit_mismatch _ => simp [Config.touchedVarsSet] at hx

/-! ### Multi-step store preservation (outerInv-based, block-exit-safe) -/

/-- Star version of store preservation outside touchedVars under outerInv hypothesis.
    Handles block exits correctly using the `outerInv`/projectStore_isSome lemmas. -/
private theorem star_preserves_store_outside_touchedVars_outerInv
    (σ_outer : SemanticStore Expression)
    (c₁ c₂ : CC)
    (hstar : CoreStar π φ c₁ c₂)
    (hinv : outerInv σ_outer c₁)
    (x : Expression.Ident)
    (hout : (σ_outer x).isSome)
    (hx : x ∉ Config.touchedVarsSet c₁) :
    c₂.getEnv.store x = c₁.getEnv.store x := by
  induction hstar with
  | refl => rfl
  | step _ mid _ hstep _ ih =>
    have hx_mid : x ∉ Config.touchedVarsSet mid :=
      fun hmem => hx (step_touchedVars_subset π φ _ _ hstep x hmem)
    have hinv_mid : outerInv σ_outer mid := step_preserves_outerInv π φ hstep hinv
    rw [ih hinv_mid hx_mid]
    exact step_preserves_store_outside_touchedVars_outerInv π φ σ_outer _ _ hstep hinv x hout hx

-- NOTE: The theorem `loop_iterations_store_agreement` was removed here.
-- It was private and had no callers. Its body required a semantic argument
-- that init-on-already-isSome vars is a no-op — provable but unused.

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
  have h := block_wrap_terminal π φ label
    ([Stmt.cmd (HasPassiveCmds.assume guard_label g md)] ++
     inv.mapIdx fun i le => Stmt.cmd (HasPassiveCmds.assume (mkInvLabel i le.1) le.2 md))
    md ρ ρ
    (stmts_passive_all_pass π φ _ ρ hwfb (by
      intro s hs
      simp only [List.cons_append, List.nil_append, List.mem_cons] at hs
      rcases hs with rfl | hs
      · exact assume_pass_step π φ _ g md ρ hguard_tt hwfb
      · rw [List.mem_mapIdx] at hs
        obtain ⟨i, hi, rfl⟩ := hs
        exact assume_pass_step π φ _ _ md ρ (hall_tt _ (List.getElem_mem hi)) hwfb))
  rw [projectStore_self_env] at h; exact h

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
  have h := block_wrap_terminal π φ label _ md ρ ρ
    (stmts_mapIdx_assume_terminal π φ inv ρ md mkInvLabel hwfb hall_tt)
  rw [projectStore_self_env] at h; exact h

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
    the inner reached `.terminal ρ_inner`.  (Under the new semantics where
    `.exiting .none` is unreachable, the previous "break" disjunct is empty.) -/
private theorem blockT_none_reaches_terminal
    {inner : CC} {σ_parent : SemanticStore Expression} {ρ' : Env Expression}
    (hstar : ReflTransT (StepStmt Expression (EvalCommand π φ) (EvalPureFunc φ))
      (.block .none σ_parent inner) (.terminal ρ')) :
    ∃ ρ_inner,
    (∃ (h : ReflTransT (StepStmt Expression (EvalCommand π φ) (EvalPureFunc φ))
          inner (.terminal ρ_inner)), h.len < hstar.len) ∧
    ρ' = { ρ_inner with store := projectStore σ_parent ρ_inner.store } := by
  match hstar with
  | .step _ (.block _ _ inner₁) _ (.step_block_body h) hrest =>
    have ⟨ρ_inner, ⟨hh, hlen⟩, heq⟩ := blockT_none_reaches_terminal hrest
    exact ⟨ρ_inner, ⟨.step _ _ _ h hh, by simp [ReflTransT.len]; omega⟩, heq⟩
  | .step _ _ _ .step_block_done hrest =>
    match hrest with
    | .refl _ => exact ⟨_, ⟨.refl _, by simp [ReflTransT.len]⟩, rfl⟩
    | .step _ _ _ h _ => exact nomatch h
  | .step _ _ _ (.step_block_exit_match heq) _ => cases heq
  | .step _ _ _ (.step_block_exit_mismatch _) hrest =>
    match hrest with
    | .step _ _ _ h _ => exact nomatch h
  termination_by hstar.len

/-- If `.block .none inner` reaches `.exiting l ρ'` in `ReflTransT`,
    the inner reaches `.exiting l ρ_inner` with strictly shorter trace,
    and `ρ' = { ρ_inner with store := projectStore σ_parent ρ_inner.store }`. -/
private theorem blockT_none_reaches_exiting_some
    {inner : CC} {σ_parent : SemanticStore Expression} {l : String} {ρ' : Env Expression}
    (hstar : ReflTransT (StepStmt Expression (EvalCommand π φ) (EvalPureFunc φ))
      (.block .none σ_parent inner) (.exiting l ρ')) :
    ∃ (ρ_inner : Env Expression),
      ∃ (h : ReflTransT (StepStmt Expression (EvalCommand π φ) (EvalPureFunc φ))
          inner (.exiting l ρ_inner)),
      h.len < hstar.len ∧
      ρ' = { ρ_inner with store := projectStore σ_parent ρ_inner.store } := by
  match hstar with
  | .step _ (.block _ _ inner₁) _ (.step_block_body h) hrest =>
    have ⟨ρ_inner, hh, hlen, heq⟩ := blockT_none_reaches_exiting_some hrest
    exact ⟨ρ_inner, .step _ _ _ h hh, by simp [ReflTransT.len]; omega, heq⟩
  | .step _ _ _ .step_block_done hrest =>
    match hrest with
    | .step _ _ _ h _ => exact nomatch h
  | .step _ _ _ (.step_block_exit_match heq) _ => cases heq
  | .step _ _ _ (.step_block_exit_mismatch _) hrest =>
    match hrest with
    | .refl _ => exact ⟨_, .refl _, by simp [ReflTransT.len], rfl⟩
    | .step _ _ _ h _ => exact nomatch h
  termination_by hstar.len

/-- Invert a `.seq` execution reaching `.exiting` in `ReflTransT`:
    either the inner exited (with length bound), or the inner terminated
    and the tail stmts exited (with combined length bound). -/
private theorem seqT_reaches_exiting
    {inner : CC} {ss : Statements} {lbl : String} {ρ' : Env Expression}
    (hstar : ReflTransT (StepStmt Expression (EvalCommand π φ) (EvalPureFunc φ))
      (.seq inner ss) (.exiting lbl ρ')) :
    (∃ (h : ReflTransT (StepStmt Expression (EvalCommand π φ) (EvalPureFunc φ))
          inner (.exiting lbl ρ')), h.len < hstar.len) ∨
    (∃ (ρ₁ : Env Expression),
      ∃ (h1 : ReflTransT (StepStmt Expression (EvalCommand π φ) (EvalPureFunc φ))
          inner (.terminal ρ₁)),
      ∃ (h2 : ReflTransT (StepStmt Expression (EvalCommand π φ) (EvalPureFunc φ))
          (.stmts ss ρ₁) (.exiting lbl ρ')),
        h1.len + h2.len < hstar.len) := by
  match hstar with
  | .step _ _ _ (.step_seq_inner h) hrest =>
    match seqT_reaches_exiting hrest with
    | .inl ⟨h_inner, hlen⟩ =>
      exact .inl ⟨.step _ _ _ h h_inner, by simp [ReflTransT.len]; omega⟩
    | .inr ⟨ρ₁, h1, h2, hlen⟩ =>
      exact .inr ⟨ρ₁, .step _ _ _ h h1, h2, by simp [ReflTransT.len]; omega⟩
  | .step _ _ _ .step_seq_done hrest =>
    exact .inr ⟨_, .refl _, hrest, by show 0 + hrest.len < 1 + hrest.len; omega⟩
  | .step _ _ _ .step_seq_exit hrest =>
    exact .inl ⟨hrest, by simp [ReflTransT.len]⟩

/-- Invert `.stmts (s :: rest)` reaching `.exiting` in `ReflTransT`. -/
private theorem stmtsT_cons_reaches_exiting
    {s : Statement} {rest : Statements} {lbl : String} {ρ₀ ρ' : Env Expression}
    (hstar : ReflTransT (StepStmt Expression (EvalCommand π φ) (EvalPureFunc φ))
      (.stmts (s :: rest) ρ₀) (.exiting lbl ρ')) :
    (∃ (h : ReflTransT (StepStmt Expression (EvalCommand π φ) (EvalPureFunc φ))
          (.stmt s ρ₀) (.exiting lbl ρ')), h.len + 2 ≤ hstar.len) ∨
    (∃ (ρ₁ : Env Expression),
      CoreStar π φ (.stmt s ρ₀) (.terminal ρ₁) ∧
      ∃ (h2 : ReflTransT (StepStmt Expression (EvalCommand π φ) (EvalPureFunc φ))
          (.stmts rest ρ₁) (.exiting lbl ρ')),
        h2.len + 2 ≤ hstar.len) := by
  match hstar with
  | .step _ _ _ .step_stmts_cons hrest =>
    match seqT_reaches_exiting (π := π) (φ := φ) hrest with
    | .inl ⟨h_inner, hlen⟩ =>
      exact .inl ⟨h_inner, by simp [ReflTransT.len]; omega⟩
    | .inr ⟨ρ₁, h1, h2, hlen⟩ =>
      exact .inr ⟨ρ₁, reflTransT_to_prop h1, h2, by simp [ReflTransT.len]; omega⟩

/-- Decompose `stmts (ss₁ ++ [s])` reaching `.exiting lbl ρ'` in `ReflTransT`:
    either `stmts ss₁` exits (as `CoreStar`), or `stmts ss₁` terminates at ρ₁
    and `stmt s ρ₁` exits with a strictly shorter `ReflTransT` trace. -/
private theorem stmtsT_append_reaches_exiting
    (ss₁ : Statements) (s : Statement) (lbl : String)
    (ρ₀ ρ' : Env Expression)
    (hstar : ReflTransT (StepStmt Expression (EvalCommand π φ) (EvalPureFunc φ))
      (.stmts (ss₁ ++ [s]) ρ₀) (.exiting lbl ρ')) :
    CoreStar π φ (.stmts ss₁ ρ₀) (.exiting lbl ρ') ∨
    ∃ ρ₁,
      CoreStar π φ (.stmts ss₁ ρ₀) (.terminal ρ₁) ∧
      ∃ (hs : ReflTransT (StepStmt Expression (EvalCommand π φ) (EvalPureFunc φ))
          (.stmt s ρ₁) (.exiting lbl ρ')),
        hs.len < hstar.len := by
  induction ss₁ generalizing ρ₀ with
  | nil =>
    match hstar with
    | .step _ _ _ .step_stmts_cons hrest =>
      match seqT_reaches_exiting (π := π) (φ := φ) hrest with
      | .inl ⟨h_inner, hlen⟩ =>
        exact .inr ⟨ρ₀, .step _ _ _ .step_stmts_nil (.refl _), h_inner,
          by simp [ReflTransT.len]; omega⟩
      | .inr ⟨ρ₁, _, h2, hlen⟩ =>
        -- stmts [] ρ₁ exits: impossible
        match h2 with
        | .step _ _ _ .step_stmts_nil hrest_nil =>
          match hrest_nil with
          | .step _ _ _ h _ => cases h
  | cons s' rest' ih =>
    match stmtsT_cons_reaches_exiting (π := π) (φ := φ) hstar with
    | .inl ⟨h_exit, _⟩ =>
      exact .inl (stmts_cons_exiting π φ s' rest' lbl ρ₀ ρ' (reflTransT_to_prop h_exit))
    | .inr ⟨ρ_mid, hstmt_term, h_tail, hlen_tail⟩ =>
      match ih ρ_mid h_tail with
      | .inl hrest_exits =>
        exact .inl (ReflTrans_Transitive _ _ _ _
          (stmts_cons_step Expression (EvalCommand π φ) (EvalPureFunc φ)
            s' rest' ρ₀ ρ_mid hstmt_term) hrest_exits)
      | .inr ⟨ρ₁, hrest_term, hs_exit, hlen_s⟩ =>
        -- hlen_s : hs_exit.len < h_tail.len
        -- hlen_tail : h_tail.len + 2 ≤ hstar.len
        have h_tail_le : h_tail.len ≤ hstar.len := Nat.le_of_add_right_le hlen_tail
        have hbound : hs_exit.len < hstar.len :=
          Nat.lt_of_lt_of_le hlen_s h_tail_le
        exact .inr ⟨ρ₁, ReflTrans_Transitive _ _ _ _
          (stmts_cons_step Expression (EvalCommand π φ) (EvalPureFunc φ)
            s' rest' ρ₀ ρ_mid hstmt_term) hrest_term, hs_exit, hbound⟩

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
    (bss : Statements) (ρ ρ' : Env Expression) (lbl : String)
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

/-- If `.block .none inner` reaches `.exiting l ρ'`, then `inner` reaches
    `.exiting l ρ_inner` and the store is projected through the parent store. -/
private theorem block_none_reaches_exiting_some
    {inner : CC} {σ_parent : SemanticStore Expression} {l : String} {ρ' : Env Expression}
    (hstar : CoreStar π φ (.block .none σ_parent inner) (.exiting l ρ')) :
    ∃ (ρ_inner : Env Expression),
      CoreStar π φ inner (.exiting l ρ_inner) ∧
      ρ' = { ρ_inner with store := projectStore σ_parent ρ_inner.store } := by
  suffices ∀ src tgt, CoreStar π φ src tgt →
      ∀ inner σ_parent l ρ', src = .block (none : Option String) σ_parent inner → tgt = .exiting l ρ' →
      ∃ (ρ_inner : Env Expression),
        CoreStar π φ inner (.exiting l ρ_inner) ∧
        ρ' = { ρ_inner with store := projectStore σ_parent ρ_inner.store } from
    this _ _ hstar _ _ _ _ rfl rfl
  intro src tgt hstar_g
  induction hstar_g with
  | refl => intro _ _ _ _ hsrc htgt; subst hsrc; cases htgt
  | step _ mid _ hstep hrest ih =>
    intro inner σ_parent l ρ' hsrc htgt; subst hsrc
    cases hstep with
    | step_block_body h =>
      have ⟨ρ_inner, hexit, hproj⟩ := ih _ _ _ _ rfl htgt
      exact ⟨ρ_inner, .step _ _ _ h hexit, hproj⟩
    | step_block_done =>
      subst htgt; cases hrest with | step _ _ _ h _ => cases h
    | step_block_exit_match heq => cases heq
    | step_block_exit_mismatch hne =>
      subst htgt
      cases hrest with
      | refl => exact ⟨_, .refl _, rfl⟩
      | step _ _ _ h _ => cases h

/-- Decompose `stmts (s :: ss) ρ₀` reaching `.exiting lbl ρ'`:
    either `s` exits, or `s` terminates at some `ρ₁` and `stmts ss ρ₁` exits. -/
private theorem stmts_cons_reaches_exiting
    (s : Statement) (ss : Statements) (lbl : String)
    (ρ₀ ρ' : Env Expression)
    (hstar : CoreStar π φ (.stmts (s :: ss) ρ₀) (.exiting lbl ρ')) :
    CoreStar π φ (.stmt s ρ₀) (.exiting lbl ρ') ∨
    ∃ ρ₁, CoreStar π φ (.stmt s ρ₀) (.terminal ρ₁) ∧
      CoreStar π φ (.stmts ss ρ₁) (.exiting lbl ρ') := by
  match hstar with
  | .step _ _ _ .step_stmts_cons hrest =>
    match seq_reaches_exiting Expression (EvalCommand π φ) (EvalPureFunc φ) hrest with
    | .inl hexit => exact .inl hexit
    | .inr ⟨ρ₁, hterm, htail⟩ => exact .inr ⟨ρ₁, hterm, htail⟩

/-- Decompose `stmts (ss₁ ++ [s]) ρ₀` reaching `.exiting lbl ρ'`:
    either `stmts ss₁` exits, or `stmts ss₁` terminates and `stmt s` exits. -/
private theorem stmts_append_reaches_exiting
    (ss₁ : Statements) (s : Statement) (lbl : String)
    (ρ₀ ρ' : Env Expression)
    (hstar : CoreStar π φ (.stmts (ss₁ ++ [s]) ρ₀) (.exiting lbl ρ')) :
    CoreStar π φ (.stmts ss₁ ρ₀) (.exiting lbl ρ') ∨
    ∃ ρ₁, CoreStar π φ (.stmts ss₁ ρ₀) (.terminal ρ₁) ∧
      CoreStar π φ (.stmt s ρ₁) (.exiting lbl ρ') := by
  induction ss₁ generalizing ρ₀ with
  | nil =>
    match hstar with
    | .step _ _ _ .step_stmts_cons hrest =>
      match seq_reaches_exiting Expression (EvalCommand π φ) (EvalPureFunc φ) hrest with
      | .inl hexit =>
        exact .inr ⟨ρ₀, .step _ _ _ .step_stmts_nil (.refl _), hexit⟩
      | .inr ⟨ρ₁, hterm, htail_exit⟩ =>
        -- stmts [] ρ₁ exits: impossible
        match htail_exit with
        | .step _ _ _ .step_stmts_nil hrest_nil =>
          match hrest_nil with
          | .step _ _ _ h _ => cases h
  | cons s' rest' ih =>
    have h_eq : (s' :: rest') ++ [s] = s' :: (rest' ++ [s]) := rfl
    rw [h_eq] at hstar
    match hstar with
    | .step _ _ _ .step_stmts_cons hrest =>
      match seq_reaches_exiting Expression (EvalCommand π φ) (EvalPureFunc φ) hrest with
      | .inl hstmt_exit =>
        exact .inl (stmts_cons_exiting π φ s' rest' lbl ρ₀ ρ' hstmt_exit)
      | .inr ⟨ρ_mid, hstmt_term, hrest_exit⟩ =>
        match ih ρ_mid hrest_exit with
        | .inl hrest_exits =>
          exact .inl (ReflTrans_Transitive _ _ _ _
            (stmts_cons_step Expression (EvalCommand π φ) (EvalPureFunc φ)
              s' rest' ρ₀ ρ_mid hstmt_term) hrest_exits)
        | .inr ⟨ρ₁, hrest_term, hs_exit⟩ =>
          exact .inr ⟨ρ₁, ReflTrans_Transitive _ _ _ _
            (stmts_cons_step Expression (EvalCommand π φ) (EvalPureFunc φ)
              s' rest' ρ₀ ρ_mid hstmt_term) hrest_term, hs_exit⟩

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
    (hwfc : WellFormedCoreEvalCong ρ₀.eval)
    (hnofd : Block.noFuncDecl body = Bool.true)
    (hswf : ∀ n ∈ Block.modifiedOrDefinedVars body, (ρ₀.store n).isSome)
    (hnf : ρ'.hasFailure = Bool.false)
    (hloop : CoreStar π φ (.stmt (.loop (.det g) measure inv body md) ρ₀) (.terminal ρ')) :
    -- Success: last iteration body terminates, all invs tt at ρ'
    ∃ ρ_last,
      ρ_last.eval ρ_last.store g = some HasBool.tt ∧
      (∀ le ∈ inv, ρ_last.eval ρ_last.store le.2 = some HasBool.tt) ∧
      WellFormedSemanticEvalBool ρ_last.eval ∧
      WellFormedSemanticEvalVal ρ_last.eval ∧
      WellFormedSemanticEvalVar ρ_last.eval ∧
      ρ_last.hasFailure = Bool.false ∧
      CoreStar π φ (.stmts body ρ_last) (.terminal ρ') ∧
      (∀ le ∈ inv, ρ'.eval ρ'.store le.2 = some HasBool.tt) ∧
      ρ'.eval ρ'.store g = some HasBool.ff ∧
      (∀ n ∈ Block.modifiedOrDefinedVars body, (ρ_last.store n).isSome) ∧
      (∀ x, x ∉ Block.modifiedVars body → x ∉ Block.definedVars body → ρ_last.store x = ρ₀.store x) ∧
      ρ_last.eval = ρ₀.eval ∧
      (∀ me, measure = .some me →
        ρ_last.eval ρ_last.store (HasIntOrder.lt me HasIntOrder.zero) = .some HasBool.ff) := by
  -- Convert to ReflTransT and use strong induction on trace length, generalized over ρ₀ and measure.
  have hloopT := reflTrans_to_T hloop
  suffices ∀ (n : Nat) (ρ₀ : Env Expression) (measure : Option Expression.Expr),
      ρ₀.eval ρ₀.store g = some HasBool.tt →
      (∀ le ∈ inv, ρ₀.eval ρ₀.store le.2 = some HasBool.tt) →
      WellFormedSemanticEvalBool ρ₀.eval →
      WellFormedSemanticEvalVal ρ₀.eval →
      WellFormedSemanticEvalVar ρ₀.eval →
      WellFormedCoreEvalCong ρ₀.eval →
      (∀ n ∈ Block.modifiedOrDefinedVars body, (ρ₀.store n).isSome) →
      ∀ (hstarT : ReflTransT (StepStmt Expression (EvalCommand π φ) (EvalPureFunc φ))
          (.stmt (.loop (.det g) measure inv body md) ρ₀) (.terminal ρ')),
        hstarT.len ≤ n →
      ∃ ρ_last,
        ρ_last.eval ρ_last.store g = some HasBool.tt ∧
        (∀ le ∈ inv, ρ_last.eval ρ_last.store le.2 = some HasBool.tt) ∧
        WellFormedSemanticEvalBool ρ_last.eval ∧
        WellFormedSemanticEvalVal ρ_last.eval ∧
        WellFormedSemanticEvalVar ρ_last.eval ∧
        ρ_last.hasFailure = Bool.false ∧
        CoreStar π φ (.stmts body ρ_last) (.terminal ρ') ∧
        (∀ le ∈ inv, ρ'.eval ρ'.store le.2 = some HasBool.tt) ∧
        ρ'.eval ρ'.store g = some HasBool.ff ∧
        (∀ n ∈ Block.modifiedOrDefinedVars body, (ρ_last.store n).isSome) ∧
        (∀ x, x ∉ Block.modifiedVars body → x ∉ Block.definedVars body →
              ρ_last.store x = ρ₀.store x) ∧
        ρ_last.eval = ρ₀.eval ∧
        (∀ me, measure = .some me →
          ρ_last.eval ρ_last.store (HasIntOrder.lt me HasIntOrder.zero) = .some HasBool.ff) by
    exact this hloopT.len ρ₀ measure hguard_tt hall_tt hwfb hwfv hwfvar hwfc hswf hloopT
      (Nat.le_refl _)
  intro n
  induction n with
  | zero =>
    intro ρ₀ measure _ _ _ _ _ _ _ hstarT hlen
    -- Trace must take at least one step (LHS is .stmt loop, RHS is .terminal),
    -- so hstarT.len ≥ 1, contradiction with hlen ≤ 0.
    match hstarT, hlen with
    | .step _ _ _ _ _, hlen => simp [ReflTransT.len] at hlen
  | succ n ih =>
    intro ρ₀ measure hguard_tt₀ hall_tt₀ hwfb₀ hwfv₀ hwfvar₀ hwfc₀ hswf₀ hstarT hlen
    -- Invert the first step of the trace.
    match hstarT, hlen with
    | .step _ _ _ (@StepStmt.step_loop_exit _ _ _ _ _ _ _ _ _ _ _ _ _
        _ hg_ff _ _ _) _, _ =>
      -- step_loop_exit: requires guard ff at ρ₀, contradicting hguard_tt₀.
      exfalso; rw [hguard_tt₀] at hg_ff; cases hg_ff
    | .step _ _ _ (@StepStmt.step_loop_enter _ _ _ _ _ _ _ _ _ _ _ _ _
        hasInvFailure _ hinv_bool hff_iff _ hmeas_lb₀) hrest, hlen =>
      -- step_loop_enter case.  The successor config is
      --   .seq (.block .none ρ₀.store (.stmts body ρ₀')) [loop]
      -- where ρ₀' = { ρ₀ with hasFailure := ρ₀.hasFailure || hasInvFailure }.
      --
      -- First, derive ρ₀.hasFailure = false and hasInvFailure = false from hnf.
      have hrest_prop := reflTransT_to_prop hrest
      have hnf_start : (ρ₀.hasFailure || hasInvFailure) = Bool.false := by
        -- The starting env after step_loop_enter is .seq (.block .none ρ₀.store
        -- (.stmts body ρ₀')) [loop], whose getEnv is the outer seq's inner block.
        -- block_none.getEnv = inner.getEnv, and getEnv of .stmts is ρ₀'.
        -- So the seq's getEnv hasFailure is ρ₀.hasFailure || hasInvFailure.
        have h := hasFailure_false_backwards (π := π) (φ := φ) hrest_prop hnf
        simpa [Config.getEnv] using h
      have hnf₀ : ρ₀.hasFailure = Bool.false := by
        cases h : ρ₀.hasFailure
        · rfl
        · simp [h, Bool.true_or] at hnf_start
      have hnif : hasInvFailure = Bool.false :=
        loop_step_hasInvFailure_false_of_or hnf_start
      subst hnif
      -- Identify ρ₀' = ρ₀ (since hasInvFailure is false).
      have hρ₀_eq :
          ({ ρ₀ with hasFailure := ρ₀.hasFailure || Bool.false } : Env Expression) = ρ₀ := by
        cases ρ₀; simp [Bool.or_false]
      -- Now decompose .seq: block reaches some ρ₁, then [loop] reaches ρ'.
      obtain ⟨ρ₁, h_block, h_tail, hlen_seq⟩ :=
        seqT_reaches_terminal (extendEval := EvalPureFunc φ) hrest
      -- Decompose the block: inner reaches terminal ρ_inner with strict length decrease.
      obtain ⟨ρ_inner, ⟨hbodyT, hlen_block⟩, hρ₁_eq⟩ :=
        blockT_none_reaches_terminal (π := π) (φ := φ) h_block
      -- The body trace as a CoreStar from ρ₀.
      have hbody_ρ₀' : CoreStar π φ (.stmts body
          ({ ρ₀ with hasFailure := ρ₀.hasFailure || Bool.false } : Env Expression))
          (.terminal ρ_inner) := reflTransT_to_prop hbodyT
      have hbody : CoreStar π φ (.stmts body ρ₀) (.terminal ρ_inner) :=
        hρ₀_eq ▸ hbody_ρ₀'
      -- projectStore is identity, so the seq's mid env ρ₁ equals ρ_inner.
      have hproj : projectStore ρ₀.store ρ_inner.store = ρ_inner.store :=
        projectStore_body_exit_eq π φ body ρ₀ ρ_inner hbody hswf₀ hnofd
      -- Reversed equality so `subst` eliminates ρ₁ (not ρ_inner).
      have hρ_eq : ρ_inner = ρ₁ := by rw [hρ₁_eq, hproj]
      subst hρ_eq
      -- Now decompose the tail: .stmts [loop] ρ_inner →T .terminal ρ'.
      obtain ⟨ρ_loop_term, h_loop_raw, h_nil, hlen_tail⟩ :=
        stmtsT_cons_terminal (extendEval := EvalPureFunc φ) h_tail
      -- h_nil : ReflTransT _ (.stmts [] ρ_loop_term) (.terminal ρ').
      -- This is forced to step_stmts_nil; refl, so ρ_loop_term = ρ'.
      have hρlt : ρ' = ρ_loop_term := by
        match h_nil with
        | .step _ _ _ .step_stmts_nil hrest_nil =>
          match hrest_nil with
          | .refl _ => rfl
      subst hρlt
      -- Now h_loop_raw : .stmt loop ρ_inner →T .terminal ρ' directly.
      let h_loop := h_loop_raw
      -- The body did not change the eval, so ρ_inner.eval = ρ₀.eval.
      have heval_inner : ρ_inner.eval = ρ₀.eval :=
        smallStep_noFuncDecl_preserves_eval_block Expression
          (EvalCommand π φ) (EvalPureFunc φ) body ρ₀ ρ_inner hnofd hbody
      -- WF properties at ρ_inner.
      have hwfb₁ : WellFormedSemanticEvalBool ρ_inner.eval := heval_inner ▸ hwfb₀
      have hwfv₁ : WellFormedSemanticEvalVal ρ_inner.eval := heval_inner ▸ hwfv₀
      have hwfvar₁ : WellFormedSemanticEvalVar ρ_inner.eval := heval_inner ▸ hwfvar₀
      have hwfc₁ : WellFormedCoreEvalCong ρ_inner.eval := heval_inner ▸ hwfc₀
      -- hasFailure at ρ_inner is false (backwards from ρ').
      have hnf_inner : ρ_inner.hasFailure = Bool.false := by
        have hloop_prop : CoreStar π φ (.stmt (.loop (.det g) measure inv body md) ρ_inner)
            (.terminal ρ') := reflTransT_to_prop h_loop
        exact hasFailure_false_backwards (π := π) (φ := φ) hloop_prop hnf
      -- isSome propagates from ρ₀ to ρ_inner.
      have hswf_inner : ∀ x ∈ Block.modifiedOrDefinedVars body, (ρ_inner.store x).isSome := by
        intro x hx
        have := stmts_star_preserves_isSome (π := π) (φ := φ) body ρ₀ _ hbody x (hswf₀ x hx)
        simpa [Config.getEnv] using this
      -- Bridge for store agreement: ρ_inner.store x = ρ₀.store x when x is outside body's
      -- touched vars.  We split on whether (ρ₀.store x).isSome.
      have hstore_bridge : ∀ x, x ∉ Block.modifiedVars body → x ∉ Block.definedVars body →
          ρ_inner.store x = ρ₀.store x := by
        intro x hmod hdef
        by_cases hsome : (ρ₀.store x).isSome
        · -- Use star_preserves_store_outside_touchedVars_outerInv with σ_outer = ρ₀.store.
          have hinv₀ : outerInv ρ₀.store (.stmts body ρ₀) := fun _ h => h
          have hxnot : x ∉ Config.touchedVarsSet (.stmts body ρ₀) := by
            simp only [Config.touchedVarsSet, List.mem_append]
            exact fun h => h.elim hmod hdef
          have h := star_preserves_store_outside_touchedVars_outerInv
            (π := π) (φ := φ) ρ₀.store _ _ hbody hinv₀ x hsome hxnot
          simpa [Config.getEnv] using h
        · -- (ρ₀.store x) = none.  By stmts_star_no_new_vars, ρ_inner.store x is also none.
          have hnone : ρ₀.store x = none := Option.not_isSome_iff_eq_none.mp hsome
          have hno_new := stmts_star_no_new_vars (π := π) (φ := φ) body ρ₀ ρ_inner hbody hswf₀ hnofd
          have : ¬ (ρ_inner.store x).isSome := fun h => hsome (hno_new x h)
          rw [hnone, Option.not_isSome_iff_eq_none.mp this]
      -- Build the loop_stmtT (.stmt loop ρ_inner →T .terminal ρ') with length bound.
      -- After the outer match destructured hstarT, hlen has type
      --   (.step _ _ _ _ hrest).len ≤ n + 1, i.e., 1 + hrest.len ≤ n + 1.
      have hrest_len : hrest.len ≤ n := by
        have hh : 1 + hrest.len ≤ n + 1 := hlen
        omega
      have hloop_len : h_loop.len ≤ n := by
        -- h_loop = h_loop_raw, hlen_tail : h_loop_raw.len + h_nil.len + 2 ≤ h_tail.len
        -- hlen_seq : h_block.len + h_tail.len < hrest.len
        have h1 : h_loop_raw.len ≤ h_tail.len := by
          have : h_loop_raw.len + h_nil.len + 2 ≤ h_tail.len := hlen_tail
          omega
        have h2 : h_tail.len ≤ hrest.len := by
          have : h_block.len + h_tail.len < hrest.len := hlen_seq
          omega
        show h_loop_raw.len ≤ n
        omega
      -- Case split on the loop trace's first step at ρ_inner.
      match h_loop, hloop_len with
      | .step _ _ _ (@StepStmt.step_loop_exit _ _ _ _ _ _ _ _ _ _ _ _ _
          hasInvFailure₁ hg_ff₁ hinv_bool₁ hff_iff₁ _) hrest₁, _ =>
        -- Last iteration: guard is ff at ρ_inner.
        -- The successor is .terminal { ρ_inner with hasFailure := ... }; trace must end here.
        have hρ'_eq_raw :
            ρ' = { ρ_inner with hasFailure := ρ_inner.hasFailure || hasInvFailure₁ } := by
          match hrest₁ with
          | .refl _ => rfl
          | .step _ _ _ h _ => cases h
        have hnf_or₁ : (ρ_inner.hasFailure || hasInvFailure₁) = Bool.false := by
          have hh : ρ'.hasFailure = (ρ_inner.hasFailure || hasInvFailure₁) := by
            rw [hρ'_eq_raw]
          rw [← hh]; exact hnf
        have hnif₁ : hasInvFailure₁ = Bool.false :=
          loop_step_hasInvFailure_false_of_or hnf_or₁
        have hall_tt₁ := all_inv_tt_of_hasInvFailure_false hinv_bool₁ hff_iff₁ hnif₁
        subst hnif₁
        have hρ'_eq : ρ' = ρ_inner := by
          rw [hρ'_eq_raw]; cases ρ_inner; simp [Bool.or_false]
        subst hρ'_eq
        -- ρ_last := ρ₀.
        refine ⟨ρ₀, hguard_tt₀, hall_tt₀, hwfb₀, hwfv₀, hwfvar₀, hnf₀,
          hbody, hall_tt₁, hg_ff₁, hswf₀, fun _ _ _ => rfl, rfl, ?_⟩
        -- Measure conjunct: instantiate hmeas_lb₀ with v := me.
        -- hmeas_lb₀ : ∀ me v, measure = .some me →
        --   ρ₀.eval ρ₀.store me = some v ∧ ρ₀.eval ρ₀.store (lt v zero) = ff
        -- With v := me, the second conjunct yields the goal.
        intro me hme
        exact (hmeas_lb₀ me me hme).2
      | .step _ _ _ (@StepStmt.step_loop_enter _ _ _ _ _ _ _ _ _ _ _ _ _
          hasInvFailure₁ hg_tt₁ hinv_bool₁ hff_iff₁ _ _) hrest₁, hloop_len =>
        -- Recursive case: more iterations needed.
        -- All-tt invariants at ρ_inner.
        let hloop_full : ReflTransT (StepStmt Expression (EvalCommand π φ) (EvalPureFunc φ))
            (.stmt (.loop (.det g) measure inv body md) ρ_inner) (.terminal ρ') :=
          .step _ _ _ (.step_loop_enter hg_tt₁ hinv_bool₁ hff_iff₁ ‹_› ‹_›) hrest₁
        have hloop_full_len : hloop_full.len ≤ n := by
          -- hloop_full = .step _ _ _ _ hrest₁, so its len = 1 + hrest₁.len
          show 1 + hrest₁.len ≤ n
          -- hloop_len after destructuring: ((.step _ _ _ _ hrest₁).len ≤ n)
          -- which unfolds to 1 + hrest₁.len ≤ n
          have : (1 + hrest₁.len) ≤ n := hloop_len
          omega
        have hnf_start₁ : (ρ_inner.hasFailure || hasInvFailure₁) = Bool.false := by
          have hh := hasFailure_false_backwards (π := π) (φ := φ)
            (reflTransT_to_prop hrest₁) hnf
          simpa [Config.getEnv] using hh
        have hnif₁ : hasInvFailure₁ = Bool.false :=
          loop_step_hasInvFailure_false_of_or hnf_start₁
        have hall_tt₁ := all_inv_tt_of_hasInvFailure_false hinv_bool₁ hff_iff₁ hnif₁
        -- Apply IH at ρ_inner.
        have ih_result := ih ρ_inner measure hg_tt₁ hall_tt₁ hwfb₁ hwfv₁ hwfvar₁ hwfc₁
          hswf_inner hloop_full hloop_full_len
        obtain ⟨ρ_last, h1, h2, h3, h4, h5, h6, h7, h8inv, h8g, h9swf, h9store, h9eval,
          h9meas⟩ := ih_result
        -- Compose: store agreement: ρ_last.store x = ρ_inner.store x = ρ₀.store x.
        refine ⟨ρ_last, h1, h2, h3, h4, h5, h6, h7, h8inv, h8g, h9swf,
          fun x hmod hdef => (h9store x hmod hdef).trans (hstore_bridge x hmod hdef),
          h9eval.trans heval_inner, ?_⟩
        -- Measure: use h9meas (with ρ_last.eval, which now equals ρ₀.eval transitively).
        intro me hme
        -- h9meas gives this directly with ρ_last.eval evaluating at ρ_last.store.
        exact h9meas me hme

/-- Nondet version of `loop_invariant_dichotomy_det`.

    The hypothesis `hbody_then_loop` captures the trace *after* the first
    `step_loop_nondet_enter` has fired: `.seq (.block .none ρ₀.store
    (.stmts body ρ₀)) [loop] →* .terminal ρ'`.  Note that with
    `hasInvFailure = false` (which we derive from `hnf`), the post-enter
    body env is just `ρ₀`.  This shape rules out the spurious
    "0-iteration" case where `step_loop_nondet_exit` fires immediately,
    which would not give us a body trace. -/
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
    (hnf₀ : ρ₀.hasFailure = Bool.false)
    (hswf : ∀ n ∈ Block.modifiedOrDefinedVars body, (ρ₀.store n).isSome)
    (hnf : ρ'.hasFailure = Bool.false)
    -- Post-enter trace: the loop has entered at least once.
    (hbody_then_loop : CoreStar π φ
      (.seq (.block .none ρ₀.store (.stmts body ρ₀))
            [.loop .nondet measure inv body md])
      (.terminal ρ')) :
    -- Success: last iteration body terminates, all invs tt at ρ'
    ∃ ρ_last,
      (∀ le ∈ inv, ρ_last.eval ρ_last.store le.2 = some HasBool.tt) ∧
      WellFormedSemanticEvalBool ρ_last.eval ∧
      WellFormedSemanticEvalVal ρ_last.eval ∧
      WellFormedSemanticEvalVar ρ_last.eval ∧
      ρ_last.hasFailure = Bool.false ∧
      CoreStar π φ (.stmts body ρ_last) (.terminal ρ') ∧
      (∀ le ∈ inv, ρ'.eval ρ'.store le.2 = some HasBool.tt) ∧
      (∀ n ∈ Block.modifiedOrDefinedVars body, (ρ_last.store n).isSome) ∧
      (∀ x, x ∉ Block.modifiedVars body → x ∉ Block.definedVars body → ρ_last.store x = ρ₀.store x) ∧
      ρ_last.eval = ρ₀.eval := by
  -- Convert to ReflTransT and use strong induction on trace length,
  -- generalized over ρ₀ and measure.
  have hstartT := reflTrans_to_T hbody_then_loop
  suffices ∀ (n : Nat) (ρ₀ : Env Expression) (measure : Option Expression.Expr),
      (∀ le ∈ inv, ρ₀.eval ρ₀.store le.2 = some HasBool.tt) →
      WellFormedSemanticEvalBool ρ₀.eval →
      WellFormedSemanticEvalVal ρ₀.eval →
      WellFormedSemanticEvalVar ρ₀.eval →
      ρ₀.hasFailure = Bool.false →
      (∀ n ∈ Block.modifiedOrDefinedVars body, (ρ₀.store n).isSome) →
      ∀ (hstartT : ReflTransT (StepStmt Expression (EvalCommand π φ) (EvalPureFunc φ))
          (.seq (.block .none ρ₀.store (.stmts body ρ₀))
                [.loop .nondet measure inv body md])
          (.terminal ρ')),
        hstartT.len ≤ n →
      ∃ ρ_last,
        (∀ le ∈ inv, ρ_last.eval ρ_last.store le.2 = some HasBool.tt) ∧
        WellFormedSemanticEvalBool ρ_last.eval ∧
        WellFormedSemanticEvalVal ρ_last.eval ∧
        WellFormedSemanticEvalVar ρ_last.eval ∧
        ρ_last.hasFailure = Bool.false ∧
        CoreStar π φ (.stmts body ρ_last) (.terminal ρ') ∧
        (∀ le ∈ inv, ρ'.eval ρ'.store le.2 = some HasBool.tt) ∧
        (∀ n ∈ Block.modifiedOrDefinedVars body, (ρ_last.store n).isSome) ∧
        (∀ x, x ∉ Block.modifiedVars body → x ∉ Block.definedVars body →
              ρ_last.store x = ρ₀.store x) ∧
        ρ_last.eval = ρ₀.eval by
    exact this hstartT.len ρ₀ measure hall_tt hwfb hwfv hwfvar hnf₀ hswf hstartT (Nat.le_refl _)
  intro n
  induction n with
  | zero =>
    intro ρ₀ measure _ _ _ _ _ _ hstartT hlen
    -- Trace must take at least one step (LHS is .seq ..., RHS is .terminal),
    -- so hstartT.len ≥ 1, contradiction with hlen ≤ 0.
    match hstartT, hlen with
    | .step _ _ _ _ _, hlen => simp [ReflTransT.len] at hlen
  | succ n ih =>
    intro ρ₀ measure hall_tt₀ hwfb₀ hwfv₀ hwfvar₀ hnf₀ hswf₀ hstartT hlen
    -- Decompose .seq: block reaches some ρ₁, then [loop] reaches ρ'.
    obtain ⟨ρ₁, h_block, h_tail, hlen_seq⟩ :=
      seqT_reaches_terminal (extendEval := EvalPureFunc φ) hstartT
    -- Decompose the block: inner reaches terminal ρ_inner with strict length decrease.
    obtain ⟨ρ_inner, ⟨hbodyT, hlen_block⟩, hρ₁_eq⟩ :=
      blockT_none_reaches_terminal (π := π) (φ := φ) h_block
    -- The body trace as a CoreStar from ρ₀.
    have hbody : CoreStar π φ (.stmts body ρ₀) (.terminal ρ_inner) :=
      reflTransT_to_prop hbodyT
    -- projectStore is identity, so the seq's mid env ρ₁ equals ρ_inner.
    have hproj : projectStore ρ₀.store ρ_inner.store = ρ_inner.store :=
      projectStore_body_exit_eq π φ body ρ₀ ρ_inner hbody hswf₀ hnofd
    have hρ_eq : ρ_inner = ρ₁ := by rw [hρ₁_eq, hproj]
    subst hρ_eq
    -- Now decompose the tail: .stmts [loop] ρ_inner →T .terminal ρ'.
    obtain ⟨ρ_loop_term, h_loop_raw, h_nil, hlen_tail⟩ :=
      stmtsT_cons_terminal (extendEval := EvalPureFunc φ) h_tail
    -- h_nil : ReflTransT _ (.stmts [] ρ_loop_term) (.terminal ρ').
    -- This is forced to step_stmts_nil; refl, so ρ_loop_term = ρ'.
    have hρlt : ρ' = ρ_loop_term := by
      match h_nil with
      | .step _ _ _ .step_stmts_nil hrest_nil =>
        match hrest_nil with
        | .refl _ => rfl
    subst hρlt
    -- Now h_loop_raw : .stmt loop ρ_inner →T .terminal ρ' directly.
    let h_loop := h_loop_raw
    -- The body did not change the eval, so ρ_inner.eval = ρ₀.eval.
    have heval_inner : ρ_inner.eval = ρ₀.eval :=
      smallStep_noFuncDecl_preserves_eval_block Expression
        (EvalCommand π φ) (EvalPureFunc φ) body ρ₀ ρ_inner hnofd hbody
    -- WF properties at ρ_inner.
    have hwfb₁ : WellFormedSemanticEvalBool ρ_inner.eval := heval_inner ▸ hwfb₀
    have hwfv₁ : WellFormedSemanticEvalVal ρ_inner.eval := heval_inner ▸ hwfv₀
    have hwfvar₁ : WellFormedSemanticEvalVar ρ_inner.eval := heval_inner ▸ hwfvar₀
    -- hasFailure at ρ_inner is false (backwards from ρ').
    have hnf_inner : ρ_inner.hasFailure = Bool.false := by
      have hloop_prop : CoreStar π φ (.stmt (.loop .nondet measure inv body md) ρ_inner)
          (.terminal ρ') := reflTransT_to_prop h_loop
      exact hasFailure_false_backwards (π := π) (φ := φ) hloop_prop hnf
    -- isSome propagates from ρ₀ to ρ_inner.
    have hswf_inner : ∀ x ∈ Block.modifiedOrDefinedVars body, (ρ_inner.store x).isSome := by
      intro x hx
      have := stmts_star_preserves_isSome (π := π) (φ := φ) body ρ₀ _ hbody x (hswf₀ x hx)
      simpa [Config.getEnv] using this
    -- Bridge for store agreement: ρ_inner.store x = ρ₀.store x when x is outside body's
    -- touched vars.  We split on whether (ρ₀.store x).isSome.
    have hstore_bridge : ∀ x, x ∉ Block.modifiedVars body → x ∉ Block.definedVars body →
        ρ_inner.store x = ρ₀.store x := by
      intro x hmod hdef
      by_cases hsome : (ρ₀.store x).isSome
      · -- Use star_preserves_store_outside_touchedVars_outerInv with σ_outer = ρ₀.store.
        have hinv₀ : outerInv ρ₀.store (.stmts body ρ₀) := fun _ h => h
        have hxnot : x ∉ Config.touchedVarsSet (.stmts body ρ₀) := by
          simp only [Config.touchedVarsSet, List.mem_append]
          exact fun h => h.elim hmod hdef
        have h := star_preserves_store_outside_touchedVars_outerInv
          (π := π) (φ := φ) ρ₀.store _ _ hbody hinv₀ x hsome hxnot
        simpa [Config.getEnv] using h
      · -- (ρ₀.store x) = none.  By stmts_star_no_new_vars, ρ_inner.store x is also none.
        have hnone : ρ₀.store x = none := Option.not_isSome_iff_eq_none.mp hsome
        have hno_new := stmts_star_no_new_vars (π := π) (φ := φ) body ρ₀ ρ_inner hbody hswf₀ hnofd
        have : ¬ (ρ_inner.store x).isSome := fun h => hsome (hno_new x h)
        rw [hnone, Option.not_isSome_iff_eq_none.mp this]
    -- Build a length bound for h_loop relative to n.
    -- hstartT = .step _ _ _ _ hrest where hrest is the rest of the start trace.
    -- Actually, we have hlen : hstartT.len ≤ n + 1 and hstartT was destructured
    -- via seqT_reaches_terminal to give hlen_seq : h_block.len + h_tail.len < hstartT.len,
    -- and hlen_tail : h_loop_raw.len + h_nil.len + 2 ≤ h_tail.len.
    have hloop_len : h_loop.len ≤ n := by
      have h1 : h_loop_raw.len ≤ h_tail.len := by
        have : h_loop_raw.len + h_nil.len + 2 ≤ h_tail.len := hlen_tail
        omega
      have h2 : h_tail.len < hstartT.len := by
        have : h_block.len + h_tail.len < hstartT.len := hlen_seq
        omega
      show h_loop_raw.len ≤ n
      omega
    -- Case split on the loop trace's first step at ρ_inner.
    match h_loop, hloop_len with
    | .step _ _ _ (@StepStmt.step_loop_nondet_exit _ _ _ _ _ _ _ _ _ _ _
        hasInvFailure₁ hinv_bool₁ hff_iff₁) hrest₁, _ =>
      -- Last iteration: loop chose to exit.
      -- The successor is .terminal { ρ_inner with hasFailure := ... }; trace must end here.
      have hρ'_eq_raw :
          ρ' = { ρ_inner with hasFailure := ρ_inner.hasFailure || hasInvFailure₁ } := by
        match hrest₁ with
        | .refl _ => rfl
        | .step _ _ _ h _ => cases h
      have hnf_or₁ : (ρ_inner.hasFailure || hasInvFailure₁) = Bool.false := by
        have hh : ρ'.hasFailure = (ρ_inner.hasFailure || hasInvFailure₁) := by
          rw [hρ'_eq_raw]
        rw [← hh]; exact hnf
      have hnif₁ : hasInvFailure₁ = Bool.false :=
        loop_step_hasInvFailure_false_of_or hnf_or₁
      have hall_tt₁ := all_inv_tt_of_hasInvFailure_false hinv_bool₁ hff_iff₁ hnif₁
      subst hnif₁
      have hρ'_eq : ρ' = ρ_inner := by
        rw [hρ'_eq_raw]; cases ρ_inner; simp [Bool.or_false]
      subst hρ'_eq
      -- ρ_last := ρ₀.
      exact ⟨ρ₀, hall_tt₀, hwfb₀, hwfv₀, hwfvar₀, hnf₀,
        hbody, hall_tt₁, hswf₀, fun _ _ _ => rfl, rfl⟩
    | .step _ _ _ (@StepStmt.step_loop_nondet_enter _ _ _ _ _ _ _ _ _ _ _ _
        hasInvFailure₁ hinv_bool₁ hff_iff₁) hrest₁, hloop_len =>
      -- Recursive case: another iteration was performed.
      -- The successor of step_loop_nondet_enter is
      --   .seq (.block .none ρ_inner.store (.stmts body ρ_inner')) [loop]
      -- where ρ_inner' = { ρ_inner with hasFailure := ρ_inner.hasFailure || hasInvFailure₁ }.
      have hrest₁_prop := reflTransT_to_prop hrest₁
      have hnf_start₁ : (ρ_inner.hasFailure || hasInvFailure₁) = Bool.false := by
        have hh := hasFailure_false_backwards (π := π) (φ := φ) hrest₁_prop hnf
        simpa [Config.getEnv] using hh
      have hnif₁ : hasInvFailure₁ = Bool.false :=
        loop_step_hasInvFailure_false_of_or hnf_start₁
      have hall_tt₁ := all_inv_tt_of_hasInvFailure_false hinv_bool₁ hff_iff₁ hnif₁
      subst hnif₁
      -- Apply IH at ρ_inner, using `Eq.mpr` of a structural equality.
      -- We construct the post-enter hypothesis at ρ_inner by carrying over hrest₁.
      -- Since `hnf_inner : ρ_inner.hasFailure = false`, the env after enter equals ρ_inner.
      have hsame :
          ({ ρ_inner with hasFailure := ρ_inner.hasFailure || Bool.false } : Env Expression)
            = ρ_inner := by
        rcases ρ_inner with ⟨_, _, _⟩
        simp [Bool.or_false]
      -- Cast `hrest₁` to the right type and prove the length bound.  The cast is
      -- via congruence of the type expression; the underlying term is unchanged.
      have hrest₁_len : hrest₁.len ≤ n := by
        have hh : (1 + hrest₁.len) ≤ n := hloop_len
        omega
      -- Apply IH using a generic helper that abstracts the env.
      -- Use a helper function defined by recursion on the env equality.
      have helper : ∀ (ρ_arg : Env Expression),
          ρ_arg = ρ_inner →
          ∀ (h : ReflTransT (StepStmt Expression (EvalCommand π φ) (EvalPureFunc φ))
              (.seq (.block .none ρ_inner.store (.stmts body ρ_arg))
                    [.loop .nondet measure inv body md])
              (.terminal ρ')),
          h.len ≤ n →
          ∃ ρ_last,
            (∀ le ∈ inv, ρ_last.eval ρ_last.store le.2 = some HasBool.tt) ∧
            WellFormedSemanticEvalBool ρ_last.eval ∧
            WellFormedSemanticEvalVal ρ_last.eval ∧
            WellFormedSemanticEvalVar ρ_last.eval ∧
            ρ_last.hasFailure = Bool.false ∧
            CoreStar π φ (.stmts body ρ_last) (.terminal ρ') ∧
            (∀ le ∈ inv, ρ'.eval ρ'.store le.2 = some HasBool.tt) ∧
            (∀ n ∈ Block.modifiedOrDefinedVars body, (ρ_last.store n).isSome) ∧
            (∀ x, x ∉ Block.modifiedVars body → x ∉ Block.definedVars body →
                  ρ_last.store x = ρ_inner.store x) ∧
            ρ_last.eval = ρ_inner.eval := fun ρ_arg heq h hlen' => by
        cases heq
        exact ih ρ_inner measure hall_tt₁ hwfb₁ hwfv₁ hwfvar₁ hnf_inner
          hswf_inner h hlen'
      have ih_result := helper _ hsame hrest₁ hrest₁_len
      obtain ⟨ρ_last, h1, h2, h3, h4, h5, h6, h7, h8, h9store, h9eval⟩ := ih_result
      -- Compose: store agreement: ρ_last.store x = ρ_inner.store x = ρ₀.store x.
      exact ⟨ρ_last, h1, h2, h3, h4, h5, h6, h7, h8,
        fun x hmod hdef => (h9store x hmod hdef).trans (hstore_bridge x hmod hdef),
        h9eval.trans heval_inner⟩

/-- When a det loop from ρ₀ reaches `.exiting (some l) ρ'` with guard tt, all
    invs tt, hasFailure false at ρ₀, and ρ'.hasFailure false, there exists
    ρ_last with invs tt, eval = ρ₀.eval, and body from ρ_last exits.
    Uses strong induction on `ReflTransT.len`. -/
private theorem loop_det_exiting_body_exit
    (hwf_ext : WFEvalExtension φ)
    (g : Expression.Expr) (measure : Option Expression.Expr)
    (inv : List (String × Expression.Expr))
    (body : Statements) (md : MetaData Expression)
    (ρ₀ ρ' : Env Expression) (l : String)
    (hguard_tt : ρ₀.eval ρ₀.store g = some HasBool.tt)
    (hall_tt : ∀ le ∈ inv, ρ₀.eval ρ₀.store le.2 = some HasBool.tt)
    (hwfb : WellFormedSemanticEvalBool ρ₀.eval)
    (hwfv : WellFormedSemanticEvalVal ρ₀.eval)
    (hwfvar : WellFormedSemanticEvalVar ρ₀.eval)
    (hnofd : Block.noFuncDecl body = Bool.true)
    (hswf : ∀ n ∈ Block.modifiedOrDefinedVars body, (ρ₀.store n).isSome)
    (hnf : ρ'.hasFailure = Bool.false)
    (hloop : CoreStar π φ
      (.stmt (.loop (.det g) measure inv body md) ρ₀) (.exiting l ρ')) :
    ∃ ρ_last,
      ρ_last.eval ρ_last.store g = some HasBool.tt ∧
      (∀ le ∈ inv, ρ_last.eval ρ_last.store le.2 = some HasBool.tt) ∧
      WellFormedSemanticEvalBool ρ_last.eval ∧
      WellFormedSemanticEvalVal ρ_last.eval ∧
      WellFormedSemanticEvalVar ρ_last.eval ∧
      ρ_last.hasFailure = Bool.false ∧
      CoreStar π φ (.stmts body ρ_last) (.exiting l ρ') ∧
      ρ_last.eval = ρ₀.eval := by
  -- Convert to ReflTransT and use strong induction on trace length, generalized over ρ₀.
  have hloopT := reflTrans_to_T hloop
  suffices ∀ (n : Nat) (ρ₀ : Env Expression) (measure : Option Expression.Expr),
      ρ₀.eval ρ₀.store g = some HasBool.tt →
      (∀ le ∈ inv, ρ₀.eval ρ₀.store le.2 = some HasBool.tt) →
      WellFormedSemanticEvalBool ρ₀.eval →
      WellFormedSemanticEvalVal ρ₀.eval →
      WellFormedSemanticEvalVar ρ₀.eval →
      (∀ n ∈ Block.modifiedOrDefinedVars body, (ρ₀.store n).isSome) →
      ∀ (hstarT : ReflTransT (StepStmt Expression (EvalCommand π φ) (EvalPureFunc φ))
          (.stmt (.loop (.det g) measure inv body md) ρ₀) (.exiting l ρ')),
        hstarT.len ≤ n →
      ∃ ρ_last,
        ρ_last.eval ρ_last.store g = some HasBool.tt ∧
        (∀ le ∈ inv, ρ_last.eval ρ_last.store le.2 = some HasBool.tt) ∧
        WellFormedSemanticEvalBool ρ_last.eval ∧
        WellFormedSemanticEvalVal ρ_last.eval ∧
        WellFormedSemanticEvalVar ρ_last.eval ∧
        ρ_last.hasFailure = Bool.false ∧
        CoreStar π φ (.stmts body ρ_last) (.exiting l ρ') ∧
        ρ_last.eval = ρ₀.eval by
    exact this hloopT.len ρ₀ measure hguard_tt hall_tt hwfb hwfv hwfvar hswf hloopT
      (Nat.le_refl _)
  intro n
  induction n with
  | zero =>
    intro ρ₀ measure _ _ _ _ _ _ hstarT hlen
    -- Trace must take at least one step (LHS is .stmt loop, RHS is .exiting),
    -- so hstarT.len ≥ 1, contradiction with hlen ≤ 0.
    match hstarT, hlen with
    | .step _ _ _ _ _, hlen => simp [ReflTransT.len] at hlen
  | succ n ih =>
    intro ρ₀ measure hguard_tt₀ hall_tt₀ hwfb₀ hwfv₀ hwfvar₀ hswf₀ hstarT hlen
    -- Invert the first step of the trace.
    match hstarT, hlen with
    | .step _ _ _ (@StepStmt.step_loop_exit _ _ _ _ _ _ _ _ _ _ _ _ _
        _ hg_ff _ _ _) hrest, _ =>
      -- step_loop_exit produces .terminal, which cannot reach .exiting.
      -- Also requires guard ff at ρ₀, contradicting hguard_tt₀.
      exfalso; rw [hguard_tt₀] at hg_ff; cases hg_ff
    | .step _ _ _ (@StepStmt.step_loop_enter _ _ _ _ _ _ _ _ _ _ _ _ _
        hasInvFailure _ hinv_bool hff_iff _ hmeas_lb₀) hrest, hlen =>
      -- step_loop_enter case.  The successor config is
      --   .seq (.block .none ρ₀.store (.stmts body ρ₀')) [loop]
      -- where ρ₀' = { ρ₀ with hasFailure := ρ₀.hasFailure || hasInvFailure }.
      have hrest_prop := reflTransT_to_prop hrest
      -- Derive ρ'.hasFailure conditions.  We have hnf : ρ'.hasFailure = false.
      -- The starting env after step_loop_enter has hasFailure = ρ₀.hasFailure || hasInvFailure.
      have hnf_start : (ρ₀.hasFailure || hasInvFailure) = Bool.false := by
        have h := hasFailure_false_backwards (π := π) (φ := φ) hrest_prop hnf
        simpa [Config.getEnv] using h
      have hnf₀ : ρ₀.hasFailure = Bool.false := by
        cases h : ρ₀.hasFailure
        · rfl
        · simp [h, Bool.true_or] at hnf_start
      have hnif : hasInvFailure = Bool.false :=
        loop_step_hasInvFailure_false_of_or hnf_start
      subst hnif
      -- Identify ρ₀' = ρ₀.
      have hρ₀_eq :
          ({ ρ₀ with hasFailure := ρ₀.hasFailure || Bool.false } : Env Expression) = ρ₀ := by
        cases ρ₀; simp [Bool.or_false]
      -- Now decompose .seq via seqT_reaches_exiting.
      match seqT_reaches_exiting (π := π) (φ := φ) hrest with
      | .inl ⟨h_block, hlen_block_outer⟩ =>
        -- Inner block exited with l: body itself exits with l.
        -- Use blockT_none_reaches_exiting_some to extract body trace.
        obtain ⟨ρ_inner, hbodyT, hlen_body, hρ'_eq⟩ :=
          blockT_none_reaches_exiting_some (π := π) (φ := φ) h_block
        -- The body trace as a CoreStar from the post-enter env.
        have hbody_ρ₀' : CoreStar π φ
            (.stmts body
              ({ ρ₀ with hasFailure := ρ₀.hasFailure || Bool.false } : Env Expression))
            (.exiting l ρ_inner) := reflTransT_to_prop hbodyT
        have hbody : CoreStar π φ (.stmts body ρ₀) (.exiting l ρ_inner) :=
          hρ₀_eq ▸ hbody_ρ₀'
        -- projectStore is identity, so ρ' = ρ_inner.
        have hproj : projectStore ρ₀.store ρ_inner.store = ρ_inner.store :=
          projectStore_body_exiting_eq π φ body ρ₀ ρ_inner l hbody hswf₀ hnofd
        have hρ'_eq' : ρ' = ρ_inner := by
          rw [hρ'_eq]
          cases ρ_inner; simp [hproj]
        subst hρ'_eq'
        -- Witness: ρ_last := ρ₀.
        exact ⟨ρ₀, hguard_tt₀, hall_tt₀, hwfb₀, hwfv₀, hwfvar₀, hnf₀, hbody, rfl⟩
      | .inr ⟨ρ₁, h_block, h_tail, hlen_seq⟩ =>
        -- Block terminates at ρ₁, then tail [loop] exits with l.
        -- Decompose the block: body reaches terminal ρ_inner with strict length decrease.
        obtain ⟨ρ_inner, ⟨hbodyT, hlen_block⟩, hρ₁_eq⟩ :=
          blockT_none_reaches_terminal (π := π) (φ := φ) h_block
        -- The body trace as a CoreStar from ρ₀.
        have hbody_ρ₀' : CoreStar π φ (.stmts body
            ({ ρ₀ with hasFailure := ρ₀.hasFailure || Bool.false } : Env Expression))
            (.terminal ρ_inner) := reflTransT_to_prop hbodyT
        have hbody : CoreStar π φ (.stmts body ρ₀) (.terminal ρ_inner) :=
          hρ₀_eq ▸ hbody_ρ₀'
        -- projectStore is identity, so the seq's mid env ρ₁ equals ρ_inner.
        have hproj : projectStore ρ₀.store ρ_inner.store = ρ_inner.store :=
          projectStore_body_exit_eq π φ body ρ₀ ρ_inner hbody hswf₀ hnofd
        have hρ_eq : ρ_inner = ρ₁ := by rw [hρ₁_eq, hproj]
        subst hρ_eq
        -- Decompose the tail: .stmts [loop] ρ_inner →T .exiting l ρ'.
        -- Use stmtsT_cons_reaches_exiting: either .stmt loop ρ_inner exits,
        -- or .stmt loop ρ_inner terminates and .stmts [] _ exits (impossible).
        match stmtsT_cons_reaches_exiting (π := π) (φ := φ) h_tail with
        | .inl ⟨h_loop, hlen_loop_outer⟩ =>
          -- .stmt loop ρ_inner →T .exiting l ρ' directly.
          -- The body did not change the eval, so ρ_inner.eval = ρ₀.eval.
          have heval_inner : ρ_inner.eval = ρ₀.eval :=
            smallStep_noFuncDecl_preserves_eval_block Expression
              (EvalCommand π φ) (EvalPureFunc φ) body ρ₀ ρ_inner hnofd hbody
          -- WF properties at ρ_inner.
          have hwfb₁ : WellFormedSemanticEvalBool ρ_inner.eval := heval_inner ▸ hwfb₀
          have hwfv₁ : WellFormedSemanticEvalVal ρ_inner.eval := heval_inner ▸ hwfv₀
          have hwfvar₁ : WellFormedSemanticEvalVar ρ_inner.eval := heval_inner ▸ hwfvar₀
          -- isSome propagates from ρ₀ to ρ_inner.
          have hswf_inner : ∀ x ∈ Block.modifiedOrDefinedVars body, (ρ_inner.store x).isSome := by
            intro x hx
            have := stmts_star_preserves_isSome (π := π) (φ := φ) body ρ₀ _ hbody x (hswf₀ x hx)
            simpa [Config.getEnv] using this
          -- Length bound for h_loop ≤ n (computed BEFORE match, so it gets rewritten).
          -- hlen : 1 + hrest.len ≤ n + 1.
          -- hlen_seq : h_block.len + h_tail.len < hrest.len.
          -- hlen_loop_outer : h_loop.len + 2 ≤ h_tail.len.
          have hloop_len : h_loop.len ≤ n := by
            have h1 : h_loop.len ≤ h_tail.len := by
              have : h_loop.len + 2 ≤ h_tail.len := hlen_loop_outer
              omega
            have h2 : h_tail.len ≤ hrest.len := by
              have : h_block.len + h_tail.len < hrest.len := hlen_seq
              omega
            have h3 : hrest.len ≤ n := by
              have hh : 1 + hrest.len ≤ n + 1 := hlen
              omega
            omega
          -- For the IH we need guard tt at ρ_inner.  Case-split on the loop trace's first step.
          match h_loop, hloop_len with
          | .step _ _ _ (@StepStmt.step_loop_exit _ _ _ _ _ _ _ _ _ _ _ _ _
              _ _ _ _ _) hrest_x, _ =>
            -- step_loop_exit produces .terminal, which cannot reach .exiting.
            exfalso
            match hrest_x with
            | .step _ _ _ h _ => cases h
          | .step _ _ _ (@StepStmt.step_loop_enter _ _ _ _ _ _ _ _ _ _ _ _ _
              hasInvFailure₁ hg_tt₁ hinv_bool₁ hff_iff₁ _ _) hrest₁, hloop_full_len =>
            -- Recursive case: more iterations needed.
            -- hloop_full_len : (.step _ _ _ _ hrest₁).len ≤ n, i.e., 1 + hrest₁.len ≤ n.
            let h_loop_full : ReflTransT (StepStmt Expression (EvalCommand π φ) (EvalPureFunc φ))
                (.stmt (.loop (.det g) measure inv body md) ρ_inner) (.exiting l ρ') :=
              .step _ _ _ (.step_loop_enter hg_tt₁ hinv_bool₁ hff_iff₁ ‹_› ‹_›) hrest₁
            have h_loop_full_len : h_loop_full.len ≤ n := by
              show 1 + hrest₁.len ≤ n
              have : (1 + hrest₁.len) ≤ n := hloop_full_len
              omega
            -- Apply IH at ρ_inner.
            have ih_result := ih ρ_inner measure hg_tt₁
              (by
                -- All-tt invariants at ρ_inner from hinv_bool₁ and hff_iff₁ + (need
                -- hasInvFailure₁ = false, derived from ρ'.hasFailure = false).
                have hnf_start₁ : (ρ_inner.hasFailure || hasInvFailure₁) = Bool.false := by
                  have hh := hasFailure_false_backwards (π := π) (φ := φ)
                    (reflTransT_to_prop hrest₁) hnf
                  simpa [Config.getEnv] using hh
                have hnif₁ : hasInvFailure₁ = Bool.false :=
                  loop_step_hasInvFailure_false_of_or hnf_start₁
                exact all_inv_tt_of_hasInvFailure_false hinv_bool₁ hff_iff₁ hnif₁)
              hwfb₁ hwfv₁ hwfvar₁ hswf_inner h_loop_full h_loop_full_len
            obtain ⟨ρ_last, h1, h2, h3, h4, h5, h6, h7, h8eval⟩ := ih_result
            exact ⟨ρ_last, h1, h2, h3, h4, h5, h6, h7, h8eval.trans heval_inner⟩
        | .inr ⟨ρ_mid, h_loop_term, h_tail_nil_exit, _⟩ =>
          -- .stmts [] ρ_mid exits: impossible.
          exfalso
          match h_tail_nil_exit with
          | .step _ _ _ .step_stmts_nil hrest_nil =>
            match hrest_nil with
            | .step _ _ _ h _ => cases h

/-- When a nondet loop from ρ₀ reaches `.exiting l ρ'` (having entered),
    with all invs tt, hasFailure false, and ρ'.hasFailure false, there exists
    ρ_last with invs tt, eval = ρ₀.eval, and body from ρ_last exits. -/
private theorem loop_nondet_exiting_body_exit
    (hwf_ext : WFEvalExtension φ)
    (measure : Option Expression.Expr)
    (inv : List (String × Expression.Expr))
    (body : Statements) (md : MetaData Expression)
    (ρ₀ ρ' : Env Expression) (l : String)
    (hall_tt : ∀ le ∈ inv, ρ₀.eval ρ₀.store le.2 = some HasBool.tt)
    (hwfb : WellFormedSemanticEvalBool ρ₀.eval)
    (hwfv : WellFormedSemanticEvalVal ρ₀.eval)
    (hwfvar : WellFormedSemanticEvalVar ρ₀.eval)
    (hnofd : Block.noFuncDecl body = Bool.true)
    (hswf : ∀ n ∈ Block.modifiedOrDefinedVars body, (ρ₀.store n).isSome)
    (hnf : ρ'.hasFailure = Bool.false)
    (henter : CoreStar π φ
      (.seq (.block .none ρ₀.store (.stmts body ρ₀))
            [.loop .nondet measure inv body md])
      (.exiting l ρ'))
    (hnf₀ : ρ₀.hasFailure = Bool.false) :
    ∃ ρ_last,
      (∀ le ∈ inv, ρ_last.eval ρ_last.store le.2 = some HasBool.tt) ∧
      WellFormedSemanticEvalBool ρ_last.eval ∧
      WellFormedSemanticEvalVal ρ_last.eval ∧
      WellFormedSemanticEvalVar ρ_last.eval ∧
      ρ_last.hasFailure = Bool.false ∧
      CoreStar π φ (.stmts body ρ_last) (.exiting l ρ') ∧
      ρ_last.eval = ρ₀.eval := by
  -- Convert to ReflTransT and use strong induction on trace length, generalized over ρ₀.
  have hstartT := reflTrans_to_T henter
  suffices ∀ (n : Nat) (ρ₀ : Env Expression) (measure : Option Expression.Expr),
      (∀ le ∈ inv, ρ₀.eval ρ₀.store le.2 = some HasBool.tt) →
      WellFormedSemanticEvalBool ρ₀.eval →
      WellFormedSemanticEvalVal ρ₀.eval →
      WellFormedSemanticEvalVar ρ₀.eval →
      ρ₀.hasFailure = Bool.false →
      (∀ n ∈ Block.modifiedOrDefinedVars body, (ρ₀.store n).isSome) →
      ∀ (hstartT : ReflTransT (StepStmt Expression (EvalCommand π φ) (EvalPureFunc φ))
          (.seq (.block .none ρ₀.store (.stmts body ρ₀))
                [.loop .nondet measure inv body md])
          (.exiting l ρ')),
        hstartT.len ≤ n →
      ∃ ρ_last,
        (∀ le ∈ inv, ρ_last.eval ρ_last.store le.2 = some HasBool.tt) ∧
        WellFormedSemanticEvalBool ρ_last.eval ∧
        WellFormedSemanticEvalVal ρ_last.eval ∧
        WellFormedSemanticEvalVar ρ_last.eval ∧
        ρ_last.hasFailure = Bool.false ∧
        CoreStar π φ (.stmts body ρ_last) (.exiting l ρ') ∧
        ρ_last.eval = ρ₀.eval by
    exact this hstartT.len ρ₀ measure hall_tt hwfb hwfv hwfvar hnf₀ hswf hstartT
      (Nat.le_refl _)
  intro n
  induction n with
  | zero =>
    intro ρ₀ measure _ _ _ _ _ _ hstartT hlen
    -- Trace must take at least one step (LHS is .seq, RHS is .exiting),
    -- so hstartT.len ≥ 1, contradiction with hlen ≤ 0.
    match hstartT, hlen with
    | .step _ _ _ _ _, hlen => simp [ReflTransT.len] at hlen
  | succ n ih =>
    intro ρ₀ measure hall_tt₀ hwfb₀ hwfv₀ hwfvar₀ hnf₀ hswf₀ hstartT hlen
    -- Decompose .seq via seqT_reaches_exiting.
    match seqT_reaches_exiting (π := π) (φ := φ) hstartT with
    | .inl ⟨h_block, hlen_block_outer⟩ =>
      -- Inner block exited with l: body itself exits with l.
      obtain ⟨ρ_inner, hbodyT, hlen_body, hρ'_eq⟩ :=
        blockT_none_reaches_exiting_some (π := π) (φ := φ) h_block
      have hbody : CoreStar π φ (.stmts body ρ₀) (.exiting l ρ_inner) :=
        reflTransT_to_prop hbodyT
      -- projectStore is identity, so ρ' = ρ_inner.
      have hproj : projectStore ρ₀.store ρ_inner.store = ρ_inner.store :=
        projectStore_body_exiting_eq π φ body ρ₀ ρ_inner l hbody hswf₀ hnofd
      have hρ'_eq' : ρ' = ρ_inner := by
        rw [hρ'_eq]
        cases ρ_inner; simp [hproj]
      subst hρ'_eq'
      -- Witness: ρ_last := ρ₀.
      exact ⟨ρ₀, hall_tt₀, hwfb₀, hwfv₀, hwfvar₀, hnf₀, hbody, rfl⟩
    | .inr ⟨ρ₁, h_block, h_tail, hlen_seq⟩ =>
      -- Block terminates at ρ₁, then tail [loop] exits with l.
      obtain ⟨ρ_inner, ⟨hbodyT, hlen_block⟩, hρ₁_eq⟩ :=
        blockT_none_reaches_terminal (π := π) (φ := φ) h_block
      have hbody : CoreStar π φ (.stmts body ρ₀) (.terminal ρ_inner) :=
        reflTransT_to_prop hbodyT
      -- projectStore is identity, so the seq's mid env ρ₁ equals ρ_inner.
      have hproj : projectStore ρ₀.store ρ_inner.store = ρ_inner.store :=
        projectStore_body_exit_eq π φ body ρ₀ ρ_inner hbody hswf₀ hnofd
      have hρ_eq : ρ_inner = ρ₁ := by rw [hρ₁_eq, hproj]
      subst hρ_eq
      -- Decompose tail: .stmts [loop] ρ_inner →T .exiting l ρ'.
      match stmtsT_cons_reaches_exiting (π := π) (φ := φ) h_tail with
      | .inl ⟨h_loop, hlen_loop_outer⟩ =>
        -- .stmt loop ρ_inner →T .exiting l ρ' directly.
        -- The body did not change the eval, so ρ_inner.eval = ρ₀.eval.
        have heval_inner : ρ_inner.eval = ρ₀.eval :=
          smallStep_noFuncDecl_preserves_eval_block Expression
            (EvalCommand π φ) (EvalPureFunc φ) body ρ₀ ρ_inner hnofd hbody
        have hwfb₁ : WellFormedSemanticEvalBool ρ_inner.eval := heval_inner ▸ hwfb₀
        have hwfv₁ : WellFormedSemanticEvalVal ρ_inner.eval := heval_inner ▸ hwfv₀
        have hwfvar₁ : WellFormedSemanticEvalVar ρ_inner.eval := heval_inner ▸ hwfvar₀
        -- isSome propagates from ρ₀ to ρ_inner.
        have hswf_inner : ∀ x ∈ Block.modifiedOrDefinedVars body, (ρ_inner.store x).isSome := by
          intro x hx
          have := stmts_star_preserves_isSome (π := π) (φ := φ) body ρ₀ _ hbody x (hswf₀ x hx)
          simpa [Config.getEnv] using this
        -- hasFailure at ρ_inner is false (backwards from ρ').
        have hnf_inner : ρ_inner.hasFailure = Bool.false := by
          have hloop_prop : CoreStar π φ
              (.stmt (.loop .nondet measure inv body md) ρ_inner) (.exiting l ρ') :=
            reflTransT_to_prop h_loop
          exact hasFailure_false_backwards (π := π) (φ := φ) hloop_prop hnf
        -- Length bound for h_loop ≤ n.
        have hloop_len : h_loop.len ≤ n := by
          have h1 : h_loop.len ≤ h_tail.len := by
            have : h_loop.len + 2 ≤ h_tail.len := hlen_loop_outer
            omega
          have h2 : h_tail.len ≤ hstartT.len := by
            have : h_block.len + h_tail.len < hstartT.len := hlen_seq
            omega
          have h3 : hstartT.len ≤ n + 1 := hlen
          omega
        -- Case split on the loop's first step at ρ_inner.
        match h_loop, hloop_len with
        | .step _ _ _ (@StepStmt.step_loop_nondet_exit _ _ _ _ _ _ _ _ _ _ _
            _ _ _) hrest_x, _ =>
          -- step_loop_nondet_exit produces .terminal, which cannot reach .exiting.
          exfalso
          match hrest_x with
          | .step _ _ _ h _ => cases h
        | .step _ _ _ (@StepStmt.step_loop_nondet_enter _ _ _ _ _ _ _ _ _ _ _ _
            hasInvFailure₁ hinv_bool₁ hff_iff₁) hrest₁, hloop_full_len =>
          -- Recursive case: another iteration was performed.
          -- The successor of step_loop_nondet_enter is
          --   .seq (.block .none ρ_inner.store (.stmts body ρ_inner')) [loop]
          -- where ρ_inner' = { ρ_inner with hasFailure := ρ_inner.hasFailure || hasInvFailure₁ }.
          have hrest₁_prop := reflTransT_to_prop hrest₁
          have hnf_start₁ : (ρ_inner.hasFailure || hasInvFailure₁) = Bool.false := by
            have hh := hasFailure_false_backwards (π := π) (φ := φ) hrest₁_prop hnf
            simpa [Config.getEnv] using hh
          have hnif₁ : hasInvFailure₁ = Bool.false :=
            loop_step_hasInvFailure_false_of_or hnf_start₁
          have hall_tt₁ := all_inv_tt_of_hasInvFailure_false hinv_bool₁ hff_iff₁ hnif₁
          subst hnif₁
          have hsame :
              ({ ρ_inner with hasFailure := ρ_inner.hasFailure || Bool.false } : Env Expression)
                = ρ_inner := by
            rcases ρ_inner with ⟨_, _, _⟩
            simp [Bool.or_false]
          have hrest₁_len : hrest₁.len ≤ n := by
            have hh : (1 + hrest₁.len) ≤ n := hloop_full_len
            omega
          -- Apply IH using a generic helper that abstracts the env.
          have helper : ∀ (ρ_arg : Env Expression),
              ρ_arg = ρ_inner →
              ∀ (h : ReflTransT (StepStmt Expression (EvalCommand π φ) (EvalPureFunc φ))
                  (.seq (.block .none ρ_inner.store (.stmts body ρ_arg))
                        [.loop .nondet measure inv body md])
                  (.exiting l ρ')),
              h.len ≤ n →
              ∃ ρ_last,
                (∀ le ∈ inv, ρ_last.eval ρ_last.store le.2 = some HasBool.tt) ∧
                WellFormedSemanticEvalBool ρ_last.eval ∧
                WellFormedSemanticEvalVal ρ_last.eval ∧
                WellFormedSemanticEvalVar ρ_last.eval ∧
                ρ_last.hasFailure = Bool.false ∧
                CoreStar π φ (.stmts body ρ_last) (.exiting l ρ') ∧
                ρ_last.eval = ρ_inner.eval := fun ρ_arg heq h hlen' => by
            cases heq
            exact ih ρ_inner measure hall_tt₁ hwfb₁ hwfv₁ hwfvar₁ hnf_inner
              hswf_inner h hlen'
          have ih_result := helper _ hsame hrest₁ hrest₁_len
          obtain ⟨ρ_last, h1, h2, h3, h4, h5, h6, h7eval⟩ := ih_result
          exact ⟨ρ_last, h1, h2, h3, h4, h5, h6, h7eval.trans heval_inner⟩
      | .inr ⟨ρ_mid, h_loop_term, h_tail_nil_exit, _⟩ =>
        -- .stmts [] ρ_mid exits: impossible.
        exfalso
        match h_tail_nil_exit with
        | .step _ _ _ .step_stmts_nil hrest_nil =>
          match hrest_nil with
          | .step _ _ _ h _ => cases h


/-! ## TouchedVars subset lemmas -/

/-- `Block.modifiedOrDefinedVars ss ⊆ Block.definedVars ss ++ Block.modifiedVars ss`. -/
private theorem modifiedOrDefinedVars_subset (sz : Nat) :
    (∀ (s : Statement), Stmt.sizeOf s ≤ sz →
      ∀ n, n ∈ Stmt.modifiedOrDefinedVars s → n ∈ Stmt.definedVars s ++ Stmt.modifiedVars s) ∧
    (∀ (ss : Statements), Block.sizeOf ss ≤ sz →
      ∀ n, n ∈ Block.modifiedOrDefinedVars ss → n ∈ Block.definedVars ss ++ Block.modifiedVars ss) := by
  induction sz with
  | zero =>
    constructor
    · intro s hsz; match s with
      | .cmd _ => exact absurd hsz (by simp [Stmt.sizeOf])
      | .block .. => exact absurd hsz (by simp [Stmt.sizeOf])
      | .ite .. => exact absurd hsz (by simp [Stmt.sizeOf])
      | .loop .. => exact absurd hsz (by simp [Stmt.sizeOf])
      | .exit .. => exact absurd hsz (by simp [Stmt.sizeOf])
      | .funcDecl .. => exact absurd hsz (by simp [Stmt.sizeOf])
      | .typeDecl .. => exact absurd hsz (by simp [Stmt.sizeOf])
    · intro ss hsz; match ss with
      | [] => intro n hn; exact hn
      | _ :: _ => exact absurd hsz (by simp [Block.sizeOf])
  | succ m ih =>
    constructor
    · intro s hsz n hn_mem
      match s with
      | .block _ bss _ =>
        simp only [Stmt.modifiedOrDefinedVars, Stmt.definedVars, Stmt.modifiedVars] at hn_mem ⊢
        have hsz_bss : Block.sizeOf bss ≤ m := by simp [Stmt.sizeOf] at hsz; omega
        have := ih.2 bss hsz_bss n hn_mem
        cases List.mem_append.mp this with
        | inl hd => exact List.mem_append_left _ hd
        | inr hm => exact List.mem_append_right _ hm
      | .ite _ tss ess _ =>
        simp only [Stmt.modifiedOrDefinedVars] at hn_mem
        simp only [Stmt.definedVars, Stmt.modifiedVars]
        have hsz_tss : Block.sizeOf tss ≤ m := by simp [Stmt.sizeOf] at hsz; omega
        have hsz_ess : Block.sizeOf ess ≤ m := by simp [Stmt.sizeOf] at hsz; omega
        cases List.mem_append.mp hn_mem with
        | inl h =>
          have := ih.2 tss hsz_tss n h
          cases List.mem_append.mp this with
          | inl hd => exact List.mem_append_left _ (List.mem_append_left _ hd)
          | inr hm => exact List.mem_append_right _ (List.mem_append_left _ hm)
        | inr h =>
          have := ih.2 ess hsz_ess n h
          cases List.mem_append.mp this with
          | inl hd => exact List.mem_append_left _ (List.mem_append_right _ hd)
          | inr hm => exact List.mem_append_right _ (List.mem_append_right _ hm)
      | .cmd _ | .exit _ _ | .loop _ _ _ _ _ | .funcDecl _ _ | .typeDecl _ _ =>
        exact hn_mem
    · intro ss hsz n hn_mem
      match ss with
      | [] => exact hn_mem
      | s :: rest =>
        simp only [Block.modifiedOrDefinedVars] at hn_mem
        simp only [Block.definedVars, Block.modifiedVars]
        have hsz_s : Stmt.sizeOf s ≤ m := by simp [Block.sizeOf] at hsz; omega
        have hsz_rest : Block.sizeOf rest ≤ m := by simp [Block.sizeOf] at hsz; omega
        cases List.mem_append.mp hn_mem with
        | inl h =>
          have := ih.1 s hsz_s n h
          cases List.mem_append.mp this with
          | inl hd => exact List.mem_append_left _ (List.mem_append_left _ hd)
          | inr hm => exact List.mem_append_right _ (List.mem_append_left _ hm)
        | inr h =>
          have := ih.2 rest hsz_rest n h
          cases List.mem_append.mp this with
          | inl hd => exact List.mem_append_left _ (List.mem_append_right _ hd)
          | inr hm => exact List.mem_append_right _ (List.mem_append_right _ hm)

private theorem loop_modifiedOrDefinedVars_implies_body_modifiedOrDefinedVars
    {guard : ExprOrNondet Expression}
    {measure : Option Expression.Expr}
    {inv : List (String × Expression.Expr)}
    {body : Statements} {md : MetaData Expression}
    {ρ₀ : Env Expression}
    (hswf : ∀ n ∈ Stmt.modifiedOrDefinedVars (.loop guard measure inv body md), (ρ₀.store n).isSome) :
    ∀ n ∈ Block.modifiedOrDefinedVars body, (ρ₀.store n).isSome := by
  intro n hn
  apply hswf
  show n ∈ Stmt.definedVars (.loop guard measure inv body md) ++
           Stmt.modifiedVars (.loop guard measure inv body md)
  have := (modifiedOrDefinedVars_subset (Block.sizeOf body)).2 body (Nat.le_refl _) n hn
  simp only [Stmt.definedVars, Stmt.modifiedVars]
  exact this

/-- `Block.modifiedVars` is a subset of `Block.modifiedOrDefinedVars`. -/
private theorem modifiedVars_subset_modifiedOrDefinedVars (sz : Nat) :
    (∀ (s : Statement), Stmt.sizeOf s ≤ sz →
      ∀ n, n ∈ Stmt.modifiedVars s → n ∈ Stmt.modifiedOrDefinedVars s) ∧
    (∀ (ss : Statements), Block.sizeOf ss ≤ sz →
      ∀ n, n ∈ Block.modifiedVars ss → n ∈ Block.modifiedOrDefinedVars ss) := by
  induction sz with
  | zero =>
    constructor
    · intro s hsz; match s with
      | .cmd _ => exact absurd hsz (by simp [Stmt.sizeOf])
      | .block .. => exact absurd hsz (by simp [Stmt.sizeOf])
      | .ite .. => exact absurd hsz (by simp [Stmt.sizeOf])
      | .loop .. => exact absurd hsz (by simp [Stmt.sizeOf])
      | .exit .. => exact absurd hsz (by simp [Stmt.sizeOf])
      | .funcDecl .. => exact absurd hsz (by simp [Stmt.sizeOf])
      | .typeDecl .. => exact absurd hsz (by simp [Stmt.sizeOf])
    · intro ss hsz; match ss with
      | [] => intro n hn; exact hn
      | _ :: _ => exact absurd hsz (by simp [Block.sizeOf])
  | succ m ih =>
    constructor
    · intro s hsz n hn_mem
      match s with
      | .block _ bss _ =>
        simp only [Stmt.modifiedOrDefinedVars, Stmt.modifiedVars] at hn_mem ⊢
        have hsz_bss : Block.sizeOf bss ≤ m := by simp [Stmt.sizeOf] at hsz; omega
        exact ih.2 bss hsz_bss n hn_mem
      | .ite _ tss ess _ =>
        simp only [Stmt.modifiedOrDefinedVars, Stmt.modifiedVars] at hn_mem ⊢
        have hsz_tss : Block.sizeOf tss ≤ m := by simp [Stmt.sizeOf] at hsz; omega
        have hsz_ess : Block.sizeOf ess ≤ m := by simp [Stmt.sizeOf] at hsz; omega
        cases List.mem_append.mp hn_mem with
        | inl h => exact List.mem_append_left _ (ih.2 tss hsz_tss n h)
        | inr h => exact List.mem_append_right _ (ih.2 ess hsz_ess n h)
      | .cmd _ | .exit _ _ | .loop _ _ _ _ _ | .funcDecl _ _ | .typeDecl _ _ =>
        simp only [Stmt.modifiedOrDefinedVars]
        exact List.mem_append_right _ hn_mem
    · intro ss hsz n hn_mem
      match ss with
      | [] => exact hn_mem
      | s :: rest =>
        simp only [Block.modifiedOrDefinedVars, Block.modifiedVars] at hn_mem ⊢
        have hsz_s : Stmt.sizeOf s ≤ m := by simp [Block.sizeOf] at hsz; omega
        have hsz_rest : Block.sizeOf rest ≤ m := by simp [Block.sizeOf] at hsz; omega
        cases List.mem_append.mp hn_mem with
        | inl h => exact List.mem_append_left _ (ih.1 s hsz_s n h)
        | inr h => exact List.mem_append_right _ (ih.2 rest hsz_rest n h)

/-- The prefix_stmts from the loop transformation terminate at ρ₀ when
    guard+invs are tt and all body-touched vars are defined.
    Returns the same structural decomposition as `stmtResult_loop_then_branch_struct`
    plus a prefix termination proof. -/
private theorem stmtResult_loop_with_prefix_term (σ : LoopElimState)
    (guard : ExprOrNondet Expression)
    (measure : Option Expression.Expr)
    (inv : List (String × Expression.Expr))
    (body : Statements) (md : MetaData Expression)
    (ρ₀ : Env Expression)
    (hwfb : WellFormedSemanticEvalBool ρ₀.eval)
    (hwfvar : WellFormedSemanticEvalVar ρ₀.eval)
    (hnf : ρ₀.hasFailure = Bool.false)
    (hwfc : WellFormedCoreEvalCong ρ₀.eval)
    (hwfv : WellFormedSemanticEvalVal ρ₀.eval)
    (hall_tt : ∀ le ∈ inv, ρ₀.eval ρ₀.store le.2 = .some HasBool.tt)
    (hguard_ok : match guard with
      | .det g => ρ₀.eval ρ₀.store g = some HasBool.tt | .nondet => True)
    (hswf_body : ∀ n ∈ Block.modifiedOrDefinedVars body, (ρ₀.store n).isSome)
    (hmeas_wf : ∀ me, measure = .some me →
      ρ₀.eval ρ₀.store (HasIntOrder.lt me HasIntOrder.zero) = .some HasBool.ff)
    (hm_old_fresh : ρ₀.store (HasIdent.ident (P := Expression)
      s!"$__loop_measure_{(StringGenState.gen "loop" σ.gen).fst}") = none)
    (hok : stmtOk σ (.loop guard measure inv body md)) :
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
    body_statements = body ∧
    (maintain_invariants = inv.mapIdx fun i le =>
      Stmt.cmd (HasPassiveCmds.assert
        s!"{loopElimAssertPrefix}{(StringGenState.gen "loop" σ.gen).fst}_arbitrary_iter_maintain_invariant_{if le.1.isEmpty then toString i else s!"{i}_{le.1}"}" le.2 md)) ∧
    (first_iter_body =
      let loop_num := (StringGenState.gen "loop" σ.gen).fst
      let invSuffix : Nat → String → String := fun i lbl =>
        if lbl.isEmpty then toString i else s!"{i}_{lbl}"
      (inv.mapIdx fun i le => Stmt.cmd (HasPassiveCmds.assert
        s!"{loopElimAssertPrefix}{loop_num}_entry_invariant_{invSuffix i le.1}" le.2 md)) ++
      (inv.mapIdx fun i le => Stmt.cmd (HasPassiveCmds.assume
        s!"{loopElimAssumePrefix}{loop_num}_entry_invariant_{invSuffix i le.1}" le.2 md))) ∧
    (∃ ρ_pf, CoreStar π φ (.stmts prefix_stmts ρ₀) (.terminal ρ_pf) ∧
      ρ_pf.eval = ρ₀.eval ∧ ρ_pf.hasFailure = ρ₀.hasFailure ∧
      (∀ n ∈ Block.touchedVars body, ρ_pf.store n = ρ₀.store n)) := by
  -- Common infrastructure for the semantic part
  let loop_num := (StringGenState.gen "loop" σ.gen).fst
  let assigned_vars := (Block.modifiedVars body).filter (fun v => v ∉ Block.definedVars body)
  have hdef_assigned : ∀ n ∈ assigned_vars, (ρ₀.store n).isSome := by
    intro n hn
    simp only [assigned_vars, List.mem_filter] at hn
    exact hswf_body n
      ((modifiedVars_subset_modifiedOrDefinedVars (Block.sizeOf body)).2 body (Nat.le_refl _) n hn.1)
  -- Havoc identity: the havoc block terminates at ρ₀.  The loop-elim transform
  -- wraps the havoc commands in a block with empty metadata `∅`, so we use
  -- `havoc_block_identity_empty_outer` (matching the run output).
  have hhavoc_id := havoc_block_identity_empty_outer π φ
    s!"{loopElimBlockPrefix}loop_havoc_{loop_num}" assigned_vars md ρ₀
    hdef_assigned hwfvar hnf
  -- Full unfolding to get concrete prefix_stmts and prove termination
  change ∃ (loop_label first_iter_label arb_iter_label : String)
    (first_iter_body : Statements)
    (prefix_stmts suffix_stmts exit_state_stmts : Statements)
    (maintain_invariants : Statements)
    (body_statements : Statements),
    (match (stmtRun σ (.loop guard measure inv body md)).fst with
      | .ok (_, s') => s' | .error _ => default) =
    .block loop_label
      [.block first_iter_label first_iter_body {},
       .ite guard
         (.block arb_iter_label
           (prefix_stmts ++ body_statements ++ maintain_invariants ++ suffix_stmts) {}
          :: exit_state_stmts) [] {}] {} ∧
    body_statements = body ∧
    (maintain_invariants = inv.mapIdx fun i le =>
      Stmt.cmd (HasPassiveCmds.assert
        s!"{loopElimAssertPrefix}{(StringGenState.gen "loop" σ.gen).fst}_arbitrary_iter_maintain_invariant_{if le.1.isEmpty then toString i else s!"{i}_{le.1}"}" le.2 md)) ∧
    (first_iter_body =
      let loop_num := (StringGenState.gen "loop" σ.gen).fst
      let invSuffix : Nat → String → String := fun i lbl =>
        if lbl.isEmpty then toString i else s!"{i}_{lbl}"
      (inv.mapIdx fun i le => Stmt.cmd (HasPassiveCmds.assert
        s!"{loopElimAssertPrefix}{loop_num}_entry_invariant_{invSuffix i le.1}" le.2 md)) ++
      (inv.mapIdx fun i le => Stmt.cmd (HasPassiveCmds.assume
        s!"{loopElimAssumePrefix}{loop_num}_entry_invariant_{invSuffix i le.1}" le.2 md))) ∧
    (∃ ρ_pf, CoreStar π φ (.stmts prefix_stmts ρ₀) (.terminal ρ_pf) ∧
      ρ_pf.eval = ρ₀.eval ∧ ρ_pf.hasFailure = ρ₀.hasFailure ∧
      (∀ n ∈ Block.touchedVars body, ρ_pf.store n = ρ₀.store n))
  have hok' := hok
  unfold stmtOk at hok'
  match h : (stmtRun σ (.loop guard measure inv body md)).fst with
  | .error e => simp [h, Except.isOk, Except.toBool] at hok'
  | .ok (b, s') =>
    simp only [h]
    simp only [stmtRun, StateT.run, ExceptT.run, Stmt.removeLoopsM,
      bind, pure, ExceptT.bind, ExceptT.pure, ExceptT.mk, ExceptT.bindCont,
      ExceptT.lift, StateT.bind,
      Functor.map, liftM, monadLift, MonadLift.monadLift,
      modify, MonadState.modifyGet, StateT.modifyGet, StateT.map,
      genLoopNum, bumpStat] at h
    -- We need to handle the freshness check. Extract that `m_old_ident ∉ modifiedOrDefinedVars` from the
    -- successful stmtRun (the else branch of the if check).
    -- Use a helper that provides semantic proofs alongside structural witnesses.
    -- After simp + repeated split, we get goals where h is a Prod.mk equality.
    repeat (first
      | (cases h
         refine ⟨_, _, _, _, _, _, _, _, _, rfl, rfl, rfl, rfl, ?_⟩
         first
           -- Nondet case: prefix = [havocd, assumes_block_nondet], terminates at ρ₀
           | exact ⟨ρ₀, stmts_pair_terminal π φ _ _ ρ₀ ρ₀ ρ₀ hhavoc_id
               (assume_block_step_nondet π φ
                 s!"{loopElimBlockPrefix}arbitrary_iter_assumes_{loop_num}"
                 inv md
                 (fun i lbl => s!"{loopElimAssumePrefix}{loop_num}_invariant_{if lbl.isEmpty then toString i else s!"{i}_{lbl}"}")
                 ρ₀ hall_tt hwfb),
               rfl, rfl, fun _ _ => rfl⟩
           -- Det+none case: prefix = [havocd, assumes_block_det], terminates at ρ₀
           | exact ⟨ρ₀, stmts_pair_terminal π φ _ _ ρ₀ ρ₀ ρ₀ hhavoc_id
               (assume_block_step_det π φ
                 s!"{loopElimBlockPrefix}arbitrary_iter_assumes_{loop_num}"
                 _ s!"{loopElimAssumePrefix}{loop_num}_guard"
                 inv md
                 (fun i lbl => s!"{loopElimAssumePrefix}{loop_num}_invariant_{if lbl.isEmpty then toString i else s!"{i}_{lbl}"}")
                 ρ₀ hguard_ok hall_tt hwfb),
               rfl, rfl, fun _ _ => rfl⟩
           -- Det+some case: prefix = [havocd, assumes_block_det, init_m_old, assert_lb]
           | (have hmeas_lb := hmeas_wf _ rfl
              obtain ⟨ρ_pf, hpf_star, hpf_eval, hpf_fail, hpf_agree⟩ :=
                pre_termination_stmts_terminal π φ loop_num _ md ρ₀ hwfb hwfvar hnf hwfc hwfv hmeas_lb
                  hm_old_fresh
              exact ⟨ρ_pf,
                stmts_concat_terminal π φ _ _ ρ₀ ρ₀ ρ_pf
                  (stmts_pair_terminal π φ _ _ ρ₀ ρ₀ ρ₀ hhavoc_id
                    (assume_block_step_det π φ
                      s!"{loopElimBlockPrefix}arbitrary_iter_assumes_{loop_num}"
                      _ s!"{loopElimAssumePrefix}{loop_num}_guard"
                      inv md
                      (fun i lbl => s!"{loopElimAssumePrefix}{loop_num}_invariant_{if lbl.isEmpty then toString i else s!"{i}_{lbl}"}")
                      ρ₀ hguard_ok hall_tt hwfb))
                  hpf_star,
                hpf_eval, hpf_fail,
                fun n hn => hpf_agree n (by
                  intro heq; rename_i hfresh
                  exact absurd (heq ▸ hn) hfresh)⟩))
      | (simp [stmtRun, StateT.run, ExceptT.run, Stmt.removeLoopsM,
              bind, pure, ExceptT.bind, ExceptT.pure, ExceptT.mk, ExceptT.bindCont,
              ExceptT.lift, StateT.bind, Functor.map, liftM, monadLift, MonadLift.monadLift,
              modify, MonadState.modifyGet, StateT.modifyGet, StateT.map,
              genLoopNum, bumpStat, Except.isOk, Except.toBool,
              StateT.pure] at hok'; contradiction)
      | contradiction
      | (split at h; skip))
    all_goals (first
      | (cases h
         refine ⟨_, _, _, _, _, _, _, _, _, rfl, rfl, rfl, rfl, ?_⟩
         first
           | exact ⟨ρ₀, stmts_pair_terminal π φ _ _ ρ₀ ρ₀ ρ₀ hhavoc_id
               (assume_block_step_nondet π φ
                 s!"{loopElimBlockPrefix}arbitrary_iter_assumes_{loop_num}"
                 inv md
                 (fun i lbl => s!"{loopElimAssumePrefix}{loop_num}_invariant_{if lbl.isEmpty then toString i else s!"{i}_{lbl}"}")
                 ρ₀ hall_tt hwfb),
               rfl, rfl, fun _ _ => rfl⟩
           | exact ⟨ρ₀, stmts_pair_terminal π φ _ _ ρ₀ ρ₀ ρ₀ hhavoc_id
               (assume_block_step_det π φ
                 s!"{loopElimBlockPrefix}arbitrary_iter_assumes_{loop_num}"
                 _ s!"{loopElimAssumePrefix}{loop_num}_guard"
                 inv md
                 (fun i lbl => s!"{loopElimAssumePrefix}{loop_num}_invariant_{if lbl.isEmpty then toString i else s!"{i}_{lbl}"}")
                 ρ₀ hguard_ok hall_tt hwfb),
               rfl, rfl, fun _ _ => rfl⟩
           | (have hmeas_lb := hmeas_wf _ rfl
              obtain ⟨ρ_pf, hpf_star, hpf_eval, hpf_fail, hpf_agree⟩ :=
                pre_termination_stmts_terminal π φ loop_num _ md ρ₀ hwfb hwfvar hnf hwfc hwfv hmeas_lb
                  hm_old_fresh
              exact ⟨ρ_pf,
                stmts_concat_terminal π φ _ _ ρ₀ ρ₀ ρ_pf
                  (stmts_pair_terminal π φ _ _ ρ₀ ρ₀ ρ₀ hhavoc_id
                    (assume_block_step_det π φ
                      s!"{loopElimBlockPrefix}arbitrary_iter_assumes_{loop_num}"
                      _ s!"{loopElimAssumePrefix}{loop_num}_guard"
                      inv md
                      (fun i lbl => s!"{loopElimAssumePrefix}{loop_num}_invariant_{if lbl.isEmpty then toString i else s!"{i}_{lbl}"}")
                      ρ₀ hguard_ok hall_tt hwfb))
                  hpf_star,
                hpf_eval, hpf_fail,
                fun n hn => hpf_agree n (by
                  intro heq; rename_i hfresh
                  exact absurd (heq ▸ hn) hfresh)⟩))
      | (simp [stmtRun, StateT.run, ExceptT.run, Stmt.removeLoopsM,
              bind, pure, ExceptT.bind, ExceptT.pure, ExceptT.mk, ExceptT.bindCont,
              ExceptT.lift, StateT.bind, Functor.map, liftM, monadLift, MonadLift.monadLift,
              modify, MonadState.modifyGet, StateT.modifyGet, StateT.map,
              genLoopNum, bumpStat, Except.isOk, Except.toBool,
              StateT.pure] at hok'; contradiction))

/-- When `ρ_target` has the same `eval` and `hasFailure` as `ρ₀`, updating
    `ρ₀.store` to `ρ_target.store` gives `ρ_target`. -/
private theorem env_with_store_eq (ρ₀ ρ_target : Env Expression)
    (heval : ρ_target.eval = ρ₀.eval)
    (hfail : ρ_target.hasFailure = ρ₀.hasFailure) :
    { ρ₀ with store := ρ_target.store } = ρ_target := by
  cases ρ₀; cases ρ_target; subst_vars; rfl

/-- Prefix targeting: the prefix_stmts from the loop transformation can reach
    `ρ_target` from `ρ₀` when:
    - assigned_vars at `ρ₀` and `ρ_target` are all defined
    - `ρ_target` agrees with `ρ₀` on store outside `assigned_vars`
    - guard + invs are tt at `ρ_target`
    - `ρ_target.eval = ρ₀.eval` and same `hasFailure`

    Returns the same structural decomposition plus the targeting proof. -/
private theorem stmtResult_loop_with_prefix_targeting_det (σ : LoopElimState)
    (g : Expression.Expr)
    (measure : Option Expression.Expr)
    (inv : List (String × Expression.Expr))
    (body : Statements) (md : MetaData Expression)
    (ρ₀ ρ_target : Env Expression)
    (hwfb : WellFormedSemanticEvalBool ρ₀.eval)
    (hwfvar : WellFormedSemanticEvalVar ρ₀.eval)
    (hnf : ρ₀.hasFailure = Bool.false)
    (hwfc : WellFormedCoreEvalCong ρ₀.eval)
    (hwfv : WellFormedSemanticEvalVal ρ₀.eval)
    (hall_tt₀ : ∀ le ∈ inv, ρ₀.eval ρ₀.store le.2 = .some HasBool.tt)
    (hguard_tt₀ : ρ₀.eval ρ₀.store g = some HasBool.tt)
    (hswf_body : ∀ n ∈ Block.modifiedOrDefinedVars body, (ρ₀.store n).isSome)
    -- Target conditions
    (hguard_tt_tgt : ρ_target.eval ρ_target.store g = some HasBool.tt)
    (hall_tt_tgt : ∀ le ∈ inv, ρ_target.eval ρ_target.store le.2 = some HasBool.tt)
    (hswf_tgt : ∀ n ∈ Block.modifiedOrDefinedVars body, (ρ_target.store n).isSome)
    (heval_tgt : ρ_target.eval = ρ₀.eval)
    (hfail_tgt : ρ_target.hasFailure = ρ₀.hasFailure)
    (hagree : ∀ x, x ∉ (Block.modifiedVars body).filter (fun v => v ∉ Block.definedVars body) →
      ρ_target.store x = ρ₀.store x)
    (hmeas_wf : ∀ me, measure = .some me →
      ρ_target.eval ρ_target.store (HasIntOrder.lt me HasIntOrder.zero) = .some HasBool.ff)
    (hm_old_fresh : ρ_target.store (HasIdent.ident (P := Expression)
      s!"$__loop_measure_{(StringGenState.gen "loop" σ.gen).fst}") = none)
    (hok : stmtOk σ (.loop (.det g) measure inv body md)) :
    ∃ (loop_label first_iter_label arb_iter_label : String)
      (first_iter_body : Statements)
      (prefix_stmts suffix_stmts exit_state_stmts : Statements)
      (maintain_invariants : Statements)
      (body_statements : Statements),
    stmtResult σ (.loop (.det g) measure inv body md) =
      .block loop_label
        [.block first_iter_label first_iter_body {},
         .ite (.det g)
           (.block arb_iter_label
             (prefix_stmts ++ body_statements ++ maintain_invariants ++ suffix_stmts) {}
            :: exit_state_stmts) [] {}] {} ∧
    body_statements = body ∧
    (maintain_invariants = inv.mapIdx fun i le =>
      Stmt.cmd (HasPassiveCmds.assert
        s!"{loopElimAssertPrefix}{(StringGenState.gen "loop" σ.gen).fst}_arbitrary_iter_maintain_invariant_{if le.1.isEmpty then toString i else s!"{i}_{le.1}"}" le.2 md)) ∧
    (first_iter_body =
      let loop_num := (StringGenState.gen "loop" σ.gen).fst
      let invSuffix : Nat → String → String := fun i lbl =>
        if lbl.isEmpty then toString i else s!"{i}_{lbl}"
      (inv.mapIdx fun i le => Stmt.cmd (HasPassiveCmds.assert
        s!"{loopElimAssertPrefix}{loop_num}_entry_invariant_{invSuffix i le.1}" le.2 md)) ++
      (inv.mapIdx fun i le => Stmt.cmd (HasPassiveCmds.assume
        s!"{loopElimAssumePrefix}{loop_num}_entry_invariant_{invSuffix i le.1}" le.2 md))) ∧
    (∃ ρ_pf_tgt, CoreStar π φ (.stmts prefix_stmts ρ₀) (.terminal ρ_pf_tgt) ∧
      ρ_pf_tgt.eval = ρ_target.eval ∧ ρ_pf_tgt.hasFailure = ρ_target.hasFailure ∧
      (∀ n ∈ Block.touchedVars body, ρ_pf_tgt.store n = ρ_target.store n)) ∧
    -- Exit-state structure: [havocd, assume_not_guard] ++ invariant_assumes
    (exit_state_stmts =
      let loop_num := (StringGenState.gen "loop" σ.gen).fst
      let invSuffix : Nat → String → String := fun i lbl =>
        if lbl.isEmpty then toString i else s!"{i}_{lbl}"
      let assigned_vars := (Block.modifiedVars body).filter (fun v => v ∉ Block.definedVars body)
      [.block s!"{loopElimBlockPrefix}loop_havoc_{loop_num}"
          (assigned_vars.map fun n => Stmt.cmd (HasHavoc.havoc n md)) {},
        .cmd (HasPassiveCmds.assume s!"{loopElimAssumePrefix}{loop_num}_not_guard" (HasNot.not g) md)]
      ++ inv.mapIdx fun i le =>
        Stmt.cmd (HasPassiveCmds.assume
          s!"{loopElimAssumePrefix}{loop_num}_exit_invariant_{invSuffix i le.1}" le.2 md)) ∧
    -- Suffix structure depends on measure
    (match measure with
      | .none => suffix_stmts = []
      | .some _ => True) := by
  -- Common infrastructure for the semantic part
  let loop_num := (StringGenState.gen "loop" σ.gen).fst
  let assigned_vars := (Block.modifiedVars body).filter (fun v => v ∉ Block.definedVars body)
  have hdef_assigned : ∀ n ∈ assigned_vars, (ρ₀.store n).isSome := by
    intro n hn
    simp only [assigned_vars, List.mem_filter] at hn
    exact hswf_body n
      ((modifiedVars_subset_modifiedOrDefinedVars (Block.sizeOf body)).2 body (Nat.le_refl _) n hn.1)
  have hdef_assigned_tgt : ∀ n ∈ assigned_vars, (ρ_target.store n).isSome := by
    intro n hn
    simp only [assigned_vars, List.mem_filter] at hn
    exact hswf_tgt n
      ((modifiedVars_subset_modifiedOrDefinedVars (Block.sizeOf body)).2 body (Nat.le_refl _) n hn.1)
  -- Havoc targeting: the havoc block targets ρ_target on assigned_vars.  The
  -- loop-elim transform wraps the havoc commands in a block with empty metadata
  -- `∅`, so we use `havoc_block_to_target_empty_outer` (matching the run output).
  have hhavoc_tgt := havoc_block_to_target_empty_outer π φ
    s!"{loopElimBlockPrefix}loop_havoc_{loop_num}" assigned_vars md ρ₀ ρ_target
    hwfvar hdef_assigned hdef_assigned_tgt hagree hnf
  -- { ρ₀ with store := ρ_target.store } = ρ_target
  have henv_eq := env_with_store_eq ρ₀ ρ_target heval_tgt hfail_tgt
  rw [henv_eq] at hhavoc_tgt
  -- WellFormedSemanticEvalBool at ρ_target (since eval is the same)
  have hwfb_tgt : WellFormedSemanticEvalBool ρ_target.eval := heval_tgt ▸ hwfb
  -- Full unfolding to get concrete prefix_stmts and prove termination
  change ∃ (loop_label first_iter_label arb_iter_label : String)
    (first_iter_body : Statements)
    (prefix_stmts suffix_stmts exit_state_stmts : Statements)
    (maintain_invariants : Statements)
    (body_statements : Statements),
    (match (stmtRun σ (.loop (.det g) measure inv body md)).fst with
      | .ok (_, s') => s' | .error _ => default) =
    .block loop_label
      [.block first_iter_label first_iter_body {},
       .ite (.det g)
         (.block arb_iter_label
           (prefix_stmts ++ body_statements ++ maintain_invariants ++ suffix_stmts) {}
          :: exit_state_stmts) [] {}] {} ∧
    body_statements = body ∧
    (maintain_invariants = inv.mapIdx fun i le =>
      Stmt.cmd (HasPassiveCmds.assert
        s!"{loopElimAssertPrefix}{(StringGenState.gen "loop" σ.gen).fst}_arbitrary_iter_maintain_invariant_{if le.1.isEmpty then toString i else s!"{i}_{le.1}"}" le.2 md)) ∧
    (first_iter_body =
      let loop_num := (StringGenState.gen "loop" σ.gen).fst
      let invSuffix : Nat → String → String := fun i lbl =>
        if lbl.isEmpty then toString i else s!"{i}_{lbl}"
      (inv.mapIdx fun i le => Stmt.cmd (HasPassiveCmds.assert
        s!"{loopElimAssertPrefix}{loop_num}_entry_invariant_{invSuffix i le.1}" le.2 md)) ++
      (inv.mapIdx fun i le => Stmt.cmd (HasPassiveCmds.assume
        s!"{loopElimAssumePrefix}{loop_num}_entry_invariant_{invSuffix i le.1}" le.2 md))) ∧
    (∃ ρ_pf_tgt, CoreStar π φ (.stmts prefix_stmts ρ₀) (.terminal ρ_pf_tgt) ∧
      ρ_pf_tgt.eval = ρ_target.eval ∧ ρ_pf_tgt.hasFailure = ρ_target.hasFailure ∧
      (∀ n ∈ Block.touchedVars body, ρ_pf_tgt.store n = ρ_target.store n)) ∧
    (exit_state_stmts =
      let loop_num := (StringGenState.gen "loop" σ.gen).fst
      let invSuffix : Nat → String → String := fun i lbl =>
        if lbl.isEmpty then toString i else s!"{i}_{lbl}"
      let assigned_vars := (Block.modifiedVars body).filter (fun v => v ∉ Block.definedVars body)
      [.block s!"{loopElimBlockPrefix}loop_havoc_{loop_num}"
          (assigned_vars.map fun n => Stmt.cmd (HasHavoc.havoc n md)) {},
        .cmd (HasPassiveCmds.assume s!"{loopElimAssumePrefix}{loop_num}_not_guard" (HasNot.not g) md)]
      ++ inv.mapIdx fun i le =>
        Stmt.cmd (HasPassiveCmds.assume
          s!"{loopElimAssumePrefix}{loop_num}_exit_invariant_{invSuffix i le.1}" le.2 md)) ∧
    (match measure with
      | .none => suffix_stmts = []
      | .some _ => True)
  have hok' := hok
  unfold stmtOk at hok'
  match h : (stmtRun σ (.loop (.det g) measure inv body md)).fst with
  | .error e => simp [h, Except.isOk, Except.toBool] at hok'
  | .ok (b, s') =>
    simp only [h]
    simp only [stmtRun, StateT.run, ExceptT.run, Stmt.removeLoopsM,
      bind, pure, ExceptT.bind, ExceptT.pure, ExceptT.mk, ExceptT.bindCont,
      ExceptT.lift, StateT.bind,
      Functor.map, liftM, monadLift, MonadLift.monadLift,
      modify, MonadState.modifyGet, StateT.modifyGet, StateT.map,
      genLoopNum, bumpStat] at h
    repeat (first
      | (cases h
         refine ⟨_, _, _, _, _, _, _, _, _, rfl, rfl, rfl, rfl, ?_, rfl, ?_⟩ <;> first
           -- Det+none case: prefix = [havocd, assumes_block_det], terminates targeting ρ_target
           | exact ⟨ρ_target, stmts_pair_terminal π φ _ _ ρ₀ ρ_target ρ_target hhavoc_tgt
                (assume_block_step_det π φ
                  s!"{loopElimBlockPrefix}arbitrary_iter_assumes_{loop_num}"
                  _ s!"{loopElimAssumePrefix}{loop_num}_guard"
                  inv md
                  (fun i lbl => s!"{loopElimAssumePrefix}{loop_num}_invariant_{if lbl.isEmpty then toString i else s!"{i}_{lbl}"}")
                  ρ_target hguard_tt_tgt hall_tt_tgt hwfb_tgt),
                rfl, rfl, fun _ _ => rfl⟩
           -- Det+some case: prefix = [havocd, assumes_block_det, init_m_old, assert_lb]
           | (have hmeas_lb := hmeas_wf _ rfl
              have hwfvar_tgt : WellFormedSemanticEvalVar ρ_target.eval := heval_tgt ▸ hwfvar
              have hwfc_tgt : WellFormedCoreEvalCong ρ_target.eval := heval_tgt ▸ hwfc
              have hwfv_tgt : WellFormedSemanticEvalVal ρ_target.eval := heval_tgt ▸ hwfv
              have hnf_tgt : ρ_target.hasFailure = Bool.false := hfail_tgt ▸ hnf
              obtain ⟨ρ_pf, hpf_star, hpf_eval, hpf_fail, hpf_agree⟩ :=
                pre_termination_stmts_terminal π φ loop_num _ md ρ_target
                  hwfb_tgt hwfvar_tgt hnf_tgt hwfc_tgt hwfv_tgt hmeas_lb hm_old_fresh
              exact ⟨ρ_pf,
                stmts_concat_terminal π φ _ _ ρ₀ ρ_target ρ_pf
                  (stmts_pair_terminal π φ _ _ ρ₀ ρ_target ρ_target hhavoc_tgt
                    (assume_block_step_det π φ
                      s!"{loopElimBlockPrefix}arbitrary_iter_assumes_{loop_num}"
                      _ s!"{loopElimAssumePrefix}{loop_num}_guard"
                      inv md
                      (fun i lbl => s!"{loopElimAssumePrefix}{loop_num}_invariant_{if lbl.isEmpty then toString i else s!"{i}_{lbl}"}")
                      ρ_target hguard_tt_tgt hall_tt_tgt hwfb_tgt))
                  hpf_star,
                hpf_eval, hpf_fail,
                fun n hn => hpf_agree n (by
                  intro heq; rename_i hfresh
                  exact absurd (heq ▸ hn) hfresh)⟩)
           -- Suffix goals
           | (simp (config := { decide := true }); done)
           | trivial)
      | (simp [stmtRun, StateT.run, ExceptT.run, Stmt.removeLoopsM,
              bind, pure, ExceptT.bind, ExceptT.pure, ExceptT.mk, ExceptT.bindCont,
              ExceptT.lift, StateT.bind, Functor.map, liftM, monadLift, MonadLift.monadLift,
              modify, MonadState.modifyGet, StateT.modifyGet, StateT.map,
              genLoopNum, bumpStat, Except.isOk, Except.toBool,
              StateT.pure] at hok'; contradiction)
      | contradiction
      | (split at h; skip))
    all_goals (first
      | (cases h
         refine ⟨_, _, _, _, _, _, _, _, _, rfl, rfl, rfl, rfl, ?_, rfl, ?_⟩ <;> first
           | exact ⟨ρ_target, stmts_pair_terminal π φ _ _ ρ₀ ρ_target ρ_target hhavoc_tgt
                (assume_block_step_det π φ
                  s!"{loopElimBlockPrefix}arbitrary_iter_assumes_{loop_num}"
                  _ s!"{loopElimAssumePrefix}{loop_num}_guard"
                  inv md
                  (fun i lbl => s!"{loopElimAssumePrefix}{loop_num}_invariant_{if lbl.isEmpty then toString i else s!"{i}_{lbl}"}")
                  ρ_target hguard_tt_tgt hall_tt_tgt hwfb_tgt),
                rfl, rfl, fun _ _ => rfl⟩
           | (have hmeas_lb := hmeas_wf _ rfl
              have hwfvar_tgt : WellFormedSemanticEvalVar ρ_target.eval := heval_tgt ▸ hwfvar
              have hwfc_tgt : WellFormedCoreEvalCong ρ_target.eval := heval_tgt ▸ hwfc
              have hwfv_tgt : WellFormedSemanticEvalVal ρ_target.eval := heval_tgt ▸ hwfv
              have hnf_tgt : ρ_target.hasFailure = Bool.false := hfail_tgt ▸ hnf
              obtain ⟨ρ_pf, hpf_star, hpf_eval, hpf_fail, hpf_agree⟩ :=
                pre_termination_stmts_terminal π φ loop_num _ md ρ_target
                  hwfb_tgt hwfvar_tgt hnf_tgt hwfc_tgt hwfv_tgt hmeas_lb hm_old_fresh
              exact ⟨ρ_pf,
                stmts_concat_terminal π φ _ _ ρ₀ ρ_target ρ_pf
                  (stmts_pair_terminal π φ _ _ ρ₀ ρ_target ρ_target hhavoc_tgt
                    (assume_block_step_det π φ
                      s!"{loopElimBlockPrefix}arbitrary_iter_assumes_{loop_num}"
                      _ s!"{loopElimAssumePrefix}{loop_num}_guard"
                      inv md
                      (fun i lbl => s!"{loopElimAssumePrefix}{loop_num}_invariant_{if lbl.isEmpty then toString i else s!"{i}_{lbl}"}")
                      ρ_target hguard_tt_tgt hall_tt_tgt hwfb_tgt))
                  hpf_star,
                hpf_eval, hpf_fail,
                fun n hn => hpf_agree n (by
                  intro heq; rename_i hfresh
                  exact absurd (heq ▸ hn) hfresh)⟩)
           | (simp (config := { decide := true }); done)
           | trivial)
      | (simp [stmtRun, StateT.run, ExceptT.run, Stmt.removeLoopsM,
              bind, pure, ExceptT.bind, ExceptT.pure, ExceptT.mk, ExceptT.bindCont,
              ExceptT.lift, StateT.bind, Functor.map, liftM, monadLift, MonadLift.monadLift,
              modify, MonadState.modifyGet, StateT.modifyGet, StateT.map,
              genLoopNum, bumpStat, Except.isOk, Except.toBool,
              StateT.pure] at hok'; contradiction))

/-! ## Partial-store agreement transfer for CoreStar

Execution of statements `ss` depends only on the eval function, the hasFailure
flag, and store values at `Block.modifiedOrDefinedVars ss`.  Two environments
that agree on these produce executions with the same hasFailure behavior and
the same store values on `modifiedOrDefinedVars` at each step.

A full formal proof requires a custom partial-store simulation (analogous to
`step_simulation` in `StmtSemantics.lean` but with `ConfigPSE` instead of
`ConfigSE`) and additional well-formedness hypotheses
(`WellFormedSemanticEvalExprCongr` + `WellFormedSemanticEvalVar`) not threaded
through the partial-store-transfer statements as written.  These lemmas are
currently unused in the loop-elimination correctness argument, so we do not
state them here; once needed they should be restated with the
well-formedness hypotheses and proved by induction on `CoreStar` with a
`ConfigPSE` invariant. -/

/- The three theorems `route_body_canfail_through_target`,
   `loop_enter_canfail_simulation`, and `det_loop_success_target_simulation`
   were helper lemmas that were never invoked anywhere in the file (no
   callers exist in this module or elsewhere in the project).  They were
   removed as unused private dead code. -/

private theorem blockOk_cons_left {σ : LoopElimState} {s : Statement} {ss : Statements}
    (h : blockOk σ (s :: ss)) : stmtOk σ s := by
  simp only [blockOk, blockRun, stmtOk, stmtRun, Block.removeLoopsM, StateT.run, ExceptT.run,
    bind, ExceptT.bind, ExceptT.mk, ExceptT.bindCont, StateT.bind,
    Except.isOk, Except.toBool] at h ⊢
  generalize hq : Stmt.removeLoopsM s σ = r at h ⊢
  obtain ⟨fst_res, snd_st⟩ := r
  cases fst_res with
  | ok v => simp
  | error e => exact Bool.noConfusion h

private theorem blockOk_cons_right {σ : LoopElimState} {s : Statement} {ss : Statements}
    (h : blockOk σ (s :: ss)) : blockOk (stmtPostState σ s) ss := by
  simp only [blockOk, blockRun, stmtPostState, stmtRun, Block.removeLoopsM, StateT.run,
    ExceptT.run, bind, ExceptT.bind, ExceptT.mk, ExceptT.bindCont, StateT.bind,
    Except.isOk, Except.toBool] at h ⊢
  generalize hq : Stmt.removeLoopsM s σ = r at h ⊢
  obtain ⟨fst_res, snd_st⟩ := r
  cases fst_res with
  | ok v =>
    simp only [StateT.bind, ExceptT.bindCont, pure, StateT.pure, ExceptT.pure, ExceptT.mk] at h
    generalize hq2 : Block.removeLoopsM ss snd_st = r2 at h ⊢
    obtain ⟨fst_res2, snd_st2⟩ := r2
    cases fst_res2 with
    | ok v2 => simp
    | error e2 => exact Bool.noConfusion h
  | error e =>
    simp only [pure, StateT.pure, Prod.fst] at h
    exact Bool.noConfusion h

private theorem stmtOk_block_inner {σ : LoopElimState} {l : String}
    {bss : Statements} {md : MetaData Expression}
    (h : stmtOk σ (.block l bss md)) : blockOk σ bss := by
  simp only [stmtOk, stmtRun, blockOk, blockRun, Stmt.removeLoopsM, StateT.run, ExceptT.run,
    bind, ExceptT.bind, ExceptT.mk, ExceptT.bindCont, StateT.bind,
    Functor.map, liftM, monadLift, MonadLift.monadLift,
    Except.isOk, Except.toBool] at h ⊢
  generalize hq : Block.removeLoopsM bss σ = r at h ⊢
  obtain ⟨fst_res, snd_st⟩ := r
  cases fst_res with
  | ok v => simp
  | error e => exact Bool.noConfusion h

private theorem stmtOk_ite_left {σ : LoopElimState} {c : ExprOrNondet Expression}
    {tss ess : Statements} {md : MetaData Expression}
    (h : stmtOk σ (.ite c tss ess md)) : blockOk σ tss := by
  simp only [stmtOk, stmtRun, blockOk, blockRun, Stmt.removeLoopsM, StateT.run, ExceptT.run,
    bind, ExceptT.bind, ExceptT.mk, ExceptT.bindCont, StateT.bind,
    Functor.map, liftM, monadLift, MonadLift.monadLift,
    Except.isOk, Except.toBool] at h ⊢
  generalize hq : Block.removeLoopsM tss σ = r at h ⊢
  obtain ⟨fst_res, snd_st⟩ := r
  cases fst_res with
  | ok v => simp
  | error e => exact Bool.noConfusion h

private theorem stmtOk_ite_right {σ : LoopElimState} {c : ExprOrNondet Expression}
    {tss ess : Statements} {md : MetaData Expression}
    (h : stmtOk σ (.ite c tss ess md)) : blockOk (blockPostState σ tss) ess := by
  simp only [stmtOk, stmtRun, blockOk, blockRun, blockPostState, Stmt.removeLoopsM, StateT.run,
    ExceptT.run, bind, ExceptT.bind, ExceptT.mk, ExceptT.bindCont, StateT.bind,
    Functor.map, liftM, monadLift, MonadLift.monadLift,
    Except.isOk, Except.toBool] at h ⊢
  generalize hq : Block.removeLoopsM tss σ = r at h ⊢
  obtain ⟨fst_res, snd_st⟩ := r
  cases fst_res with
  | ok v =>
    simp only [StateT.bind, ExceptT.bindCont, pure, StateT.pure, ExceptT.pure, ExceptT.mk] at h
    generalize hq2 : Block.removeLoopsM ess snd_st = r2 at h ⊢
    obtain ⟨fst_res2, snd_st2⟩ := r2
    cases fst_res2 with
    | ok v2 => simp
    | error e2 => exact Bool.noConfusion h
  | error e => nomatch h

/-- Self-coverage: any statement's exits are covered by any label list
    that contains each `l ∈ Stmt.labels s`. -/
private theorem stmt_self_exitsCoveredByBlocks
    (s : Statement) (labels : List String)
    (hcovers : ∀ l, l ∈ Stmt.labels s → l ∈ labels) :
    s.exitsCoveredByBlocks labels := by
  suffices hstmt : ∀ (s : Statement),
      ∀ labels : List String,
      (∀ l, l ∈ Stmt.labels s → l ∈ labels) →
      s.exitsCoveredByBlocks labels from
    hstmt s labels hcovers
  intro s'
  induction s' using Stmt.rec (motive_2 := fun ss =>
    ∀ labels : List String,
      (∀ l, l ∈ Block.labels ss → l ∈ labels) →
      Stmt.exitsCoveredByBlocks.Block.exitsCoveredByBlocks labels ss) with
  | cmd _ => intros; trivial
  | funcDecl _ _ => intros; trivial
  | typeDecl _ _ => intros; trivial
  | exit lbl md =>
    intro labels hcovers
    show lbl ∈ labels
    have heq : Stmt.labels (Stmt.exit lbl md : Statement) = [lbl] := rfl
    exact hcovers lbl (heq ▸ List.Mem.head _)
  | block l bss md ih =>
    intro labels hcovers
    show Stmt.exitsCoveredByBlocks.Block.exitsCoveredByBlocks (l :: labels) bss
    have heq : Stmt.labels (Stmt.block l bss md : Statement) = Block.labels bss := rfl
    exact ih (l :: labels)
      (fun lv hlv => List.mem_cons_of_mem _ (hcovers lv (heq ▸ hlv)))
  | ite c tss ess md ih_t ih_e =>
    intro labels hcovers
    have heq : Stmt.labels (Stmt.ite c tss ess md : Statement) =
      Block.labels tss ++ Block.labels ess := rfl
    exact ⟨ih_t labels
             (fun l hl => hcovers l (heq ▸ List.mem_append_left _ hl)),
           ih_e labels
             (fun l hl => hcovers l (heq ▸ List.mem_append_right _ hl))⟩
  | loop g m inv body md ih =>
    intro labels hcovers
    have heq : Stmt.labels (Stmt.loop g m inv body md : Statement) = Block.labels body := rfl
    exact ih labels (fun l hl => hcovers l (heq ▸ hl))
  | nil => intros; trivial
  | cons s rest ih_s ih_rest =>
    rename_i labels hcovers
    have heq : Block.labels (s :: rest) = Stmt.labels s ++ Block.labels rest := rfl
    constructor
    · exact ih_s labels (fun l hl => hcovers l (heq ▸ List.mem_append_left _ hl))
    · exact ih_rest labels (fun l hl => hcovers l (heq ▸ List.mem_append_right _ hl))

/-- Self-coverage: any block's exits are covered by the labels extracted from
    the block itself (via `Block.labels`). -/
private theorem block_self_exitsCoveredByBlocks
    (ss : Statements) :
    Stmt.exitsCoveredByBlocks.Block.exitsCoveredByBlocks (Block.labels ss) ss := by
  induction ss with
  | nil => trivial
  | cons s rest ih =>
    have heq : Block.labels (s :: rest) = Stmt.labels s ++ Block.labels rest := rfl
    exact ⟨stmt_self_exitsCoveredByBlocks s (Block.labels (s :: rest))
             (fun l hl => heq ▸ List.mem_append_left _ hl),
           (exitsCoveredByBlocks_weaken (Block.labels rest) (Block.labels (s :: rest))
             (fun l hl => heq ▸ List.mem_append_right _ hl)).2 rest ih⟩

/-- If executing a block of statements reaches `.exiting l ρ'`,
    then `l` is syntactically present in `Block.labels body`. -/
private theorem stmts_exiting_label_mem
    (body : Statements) (l : String) (ρ ρ' : Env Expression)
    (hstar : CoreStar π φ (.stmts body ρ) (.exiting l ρ')) :
    l ∈ Block.labels body := by
  have hcov : Stmt.exitsCoveredByBlocks.Block.exitsCoveredByBlocks (Block.labels body) body :=
    block_self_exitsCoveredByBlocks body
  -- Multi-step preservation of exitsCoveredByBlocks
  have hpres : ∀ c₁ c₂,
      Config.exitsCoveredByBlocks (Block.labels body) c₁ →
      StepStmtStar Expression (EvalCommand π φ) (EvalPureFunc φ) c₁ c₂ →
      Config.exitsCoveredByBlocks (Block.labels body) c₂ := by
    intro c₁ c₂ hwp hstar_c
    induction hstar_c with
    | refl => exact hwp
    | step _ _ _ hstep _ ih =>
      exact ih (step_preserves_exitsCoveredByBlocks Expression
        (EvalCommand π φ) (EvalPureFunc φ) (Block.labels body) _ _ hstep hwp)
  have hcov' : Config.exitsCoveredByBlocks (Block.labels body) (.stmts body ρ) := hcov
  have hwp_final := hpres _ _ hcov' hstar
  -- Config.exitsCoveredByBlocks (Block.labels body) (.exiting l ρ') = (l ∈ Block.labels body)
  exact hwp_final

/-- When the loop transformation succeeds, generated block labels don't collide
    with exit labels in the body. -/
private theorem stmtOk_loop_label_fresh {σ : LoopElimState}
    {guard : ExprOrNondet Expression} {measure : Option Expression.Expr}
    {inv : List (String × Expression.Expr)} {body : Statements}
    {md : MetaData Expression}
    (h : stmtOk σ (.loop guard measure inv body md)) :
    let loop_num := (StringGenState.gen "loop" σ.gen).fst
    s!"{loopElimBlockPrefix}arbitrary_iter_facts_{loop_num}" ∉ Block.labels body ∧
    s!"{loopElimBlockPrefix}loop_{loop_num}" ∉ Block.labels body := by
  have hok' := h
  unfold stmtOk at hok'
  match hrun : (stmtRun σ (.loop guard measure inv body md)).fst with
  | .error e => simp [hrun, Except.isOk, Except.toBool] at hok'
  | .ok (b, s') =>
    simp only [stmtRun, StateT.run, ExceptT.run, Stmt.removeLoopsM,
      bind, pure, ExceptT.bind, ExceptT.pure, ExceptT.mk, ExceptT.bindCont,
      ExceptT.lift, StateT.bind,
      Functor.map, liftM, monadLift, MonadLift.monadLift,
      modify, MonadState.modifyGet, StateT.map,
      genLoopNum, bumpStat] at hrun
    repeat (first
      | (split at hrun; skip)
      | contradiction)
    all_goals (first
      | (cases hrun; rename_i h; simp_all)
      | (simp_all))

/-! ## InitEnvWF derivations for sub-statements

Helpers to extract `BlockInitEnvWF`/`InitEnvWF` of sub-pieces from a parent
`InitEnvWF`/`BlockInitEnvWF`. These power the recursive calls in
`simulation`/`canfail_simulation`. -/

/-- `BlockInitEnvWF bss` follows from `InitEnvWF (.block l bss md)`: the block
    has the same touched/defined vars as its inner statements. -/
private theorem InitEnvWF.toBlock_block {reserved : List String} {l : String}
    {bss : Statements} {md : MetaData Expression} {ρ : Env Expression}
    (h : InitEnvWF reserved (.block l bss md) ρ) :
    BlockInitEnvWF reserved bss ρ where
  readWritesDefined n hn hnd := by
    refine h.readWritesDefined n ?_ ?_
    · show n ∈ Stmt.touchedVars (.block l bss md)
      show n ∈ Stmt.modifiedOrDefinedVars (.block l bss md) ++
              Stmt.getVars (.block l bss md)
      have hn' : n ∈ Block.modifiedOrDefinedVars bss ++ Block.getVars bss := hn
      have heq1 : Stmt.modifiedOrDefinedVars (.block l bss md : Statement) =
                  Block.modifiedOrDefinedVars bss := rfl
      have heq2 : Stmt.getVars (.block l bss md : Statement) =
                  Block.getVars bss := rfl
      rw [heq1, heq2]; exact hn'
    · show n ∉ Stmt.definedVars (.block l bss md)
      have heq : Stmt.definedVars (.block l bss md : Statement) =
                 Block.definedVars bss := rfl
      rw [heq]; exact hnd
  defsUndefined n hn := h.defsUndefined n (by
    show n ∈ Stmt.definedVars (.block l bss md)
    have heq : Stmt.definedVars (.block l bss md : Statement) =
               Block.definedVars bss := rfl
    rw [heq]; exact hn)
  reservedFresh := h.reservedFresh
  evalCong := h.evalCong
  exprCongr := h.exprCongr

/-- For ite: `BlockInitEnvWF tss` follows from `InitEnvWF (.ite c tss ess md)`,
    when `Block.definedVars ess` is disjoint from `Block.touchedVars tss \ Block.definedVars tss`.
    The disjointness condition rules out malformed programs where one branch reads/sets
    a var only initialized by the other branch. -/
private theorem InitEnvWF.toBlock_ite_left {reserved : List String}
    {c : ExprOrNondet Expression}
    {tss ess : Statements} {md : MetaData Expression} {ρ : Env Expression}
    (h : InitEnvWF reserved (.ite c tss ess md) ρ)
    (hdisj_left : ∀ n ∈ Block.touchedVars tss, n ∉ Block.definedVars tss →
      n ∉ Block.definedVars ess) :
    BlockInitEnvWF reserved tss ρ where
  readWritesDefined n hn hnd := by
    apply h.readWritesDefined n
    · show n ∈ Stmt.modifiedOrDefinedVars (.ite c tss ess md) ++
              Stmt.getVars (.ite c tss ess md)
      have hntouched : n ∈ Block.touchedVars tss := hn
      simp only [Stmt.modifiedOrDefinedVars, Stmt.getVars,
        Block.touchedVars, List.mem_append] at hntouched ⊢
      rcases hntouched with h | h
      · left; left; exact h
      · right; left; right; exact h
    · show n ∉ Stmt.definedVars (.ite c tss ess md)
      simp only [Stmt.definedVars, List.mem_append, not_or]
      exact ⟨hnd, hdisj_left n hn hnd⟩
  defsUndefined n hn := h.defsUndefined n (by
    show n ∈ Stmt.definedVars (.ite c tss ess md)
    simp only [Stmt.definedVars, List.mem_append]; left; exact hn)
  reservedFresh := h.reservedFresh
  evalCong := h.evalCong
  exprCongr := h.exprCongr

private theorem InitEnvWF.toBlock_ite_right {reserved : List String}
    {c : ExprOrNondet Expression}
    {tss ess : Statements} {md : MetaData Expression} {ρ : Env Expression}
    (h : InitEnvWF reserved (.ite c tss ess md) ρ)
    (hdisj_right : ∀ n ∈ Block.touchedVars ess, n ∉ Block.definedVars ess →
      n ∉ Block.definedVars tss) :
    BlockInitEnvWF reserved ess ρ where
  readWritesDefined n hn hnd := by
    apply h.readWritesDefined n
    · show n ∈ Stmt.modifiedOrDefinedVars (.ite c tss ess md) ++
              Stmt.getVars (.ite c tss ess md)
      have hntouched : n ∈ Block.touchedVars ess := hn
      simp only [Stmt.modifiedOrDefinedVars, Stmt.getVars,
        Block.touchedVars, List.mem_append] at hntouched ⊢
      rcases hntouched with h | h
      · left; right; exact h
      · right; right; exact h
    · show n ∉ Stmt.definedVars (.ite c tss ess md)
      simp only [Stmt.definedVars, List.mem_append, not_or]
      exact ⟨hdisj_right n hn hnd, hnd⟩
  defsUndefined n hn := h.defsUndefined n (by
    show n ∈ Stmt.definedVars (.ite c tss ess md)
    simp only [Stmt.definedVars, List.mem_append]; right; exact hn)
  reservedFresh := h.reservedFresh
  evalCong := h.evalCong
  exprCongr := h.exprCongr

/-- `InitEnvWF s` follows from `BlockInitEnvWF (s :: ss)`, when
    `Block.definedVars ss` is disjoint from `Stmt.touchedVars s \ Stmt.definedVars s`.  -/
private theorem BlockInitEnvWF.toStmt_head {reserved : List String} {s : Statement}
    {ss : Statements} {ρ : Env Expression}
    (h : BlockInitEnvWF reserved (s :: ss) ρ)
    (hdisj : ∀ n ∈ Stmt.touchedVars s, n ∉ Stmt.definedVars s →
      n ∉ Block.definedVars ss) :
    InitEnvWF reserved s ρ where
  readWritesDefined n hn hnd := by
    apply h.readWritesDefined n
    · show n ∈ Block.modifiedOrDefinedVars (s :: ss) ++ Block.getVars (s :: ss)
      have hntouched : n ∈ Stmt.touchedVars s := hn
      simp only [Block.modifiedOrDefinedVars, Block.getVars, Block.touchedVars,
        Stmt.touchedVars, List.mem_append] at hntouched ⊢
      rcases hntouched with h | h
      · left; left; exact h
      · right; left; exact h
    · show n ∉ Block.definedVars (s :: ss)
      simp only [Block.definedVars, List.mem_append, not_or]
      exact ⟨hnd, hdisj n hn hnd⟩
  defsUndefined n hn := h.defsUndefined n (by
    show n ∈ Block.definedVars (s :: ss)
    simp only [Block.definedVars, List.mem_append]; left; exact hn)
  reservedFresh := h.reservedFresh
  evalCong := h.evalCong
  exprCongr := h.exprCongr

/-- `BlockInitEnvWF ss` follows from `BlockInitEnvWF (s :: ss)` when ρ is preserved.
    But after s terminates at ρ₁, definedVars of s are now isSome at ρ₁ (init introduced them).
    So we need a more semantic argument; for now, this is a pure-syntactic projection
    when ρ stays the same. -/
private theorem BlockInitEnvWF.toBlock_tail_pure {reserved : List String}
    {s : Statement} {ss : Statements} {ρ : Env Expression}
    (h : BlockInitEnvWF reserved (s :: ss) ρ)
    (hdisj : ∀ n ∈ Block.touchedVars ss, n ∉ Block.definedVars ss →
      n ∉ Stmt.definedVars s) :
    BlockInitEnvWF reserved ss ρ where
  readWritesDefined n hn hnd := by
    apply h.readWritesDefined n
    · show n ∈ Block.modifiedOrDefinedVars (s :: ss) ++ Block.getVars (s :: ss)
      have hntouched : n ∈ Block.touchedVars ss := hn
      simp only [Block.modifiedOrDefinedVars, Block.getVars, Block.touchedVars,
        List.mem_append] at hntouched ⊢
      rcases hntouched with h | h
      · left; right; exact h
      · right; right; exact h
    · show n ∉ Block.definedVars (s :: ss)
      simp only [Block.definedVars, List.mem_append, not_or]
      exact ⟨hdisj n hn hnd, hnd⟩
  defsUndefined n hn := h.defsUndefined n (by
    show n ∈ Block.definedVars (s :: ss)
    simp only [Block.definedVars, List.mem_append]; right; exact hn)
  reservedFresh := h.reservedFresh
  evalCong := h.evalCong
  exprCongr := h.exprCongr

/-! ## Simulation -/

set_option maxHeartbeats 400000 in
private theorem simulation
    (hwf_ext : WFEvalExtension φ) (sz : Nat) :
    -- Statement level
    (∀ (σ : LoopElimState) (st : Statement),
      Stmt.sizeOf st ≤ sz →
      Stmt.noFuncDecl st = Bool.true →
      stmtOk σ st →
      ∀ (ρ₀ : Env Expression),
        WellFormedSemanticEvalBool ρ₀.eval →
        WellFormedSemanticEvalVal ρ₀.eval →
        WellFormedSemanticEvalVar ρ₀.eval →
        WellFormedCoreEvalCong ρ₀.eval →
        (∀ n ∈ Stmt.modifiedOrDefinedVars st, (ρ₀.store n).isSome) →
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
      blockOk σ bss →
      ∀ (ρ₀ : Env Expression),
        WellFormedSemanticEvalBool ρ₀.eval →
        WellFormedSemanticEvalVal ρ₀.eval →
        WellFormedSemanticEvalVar ρ₀.eval →
        WellFormedCoreEvalCong ρ₀.eval →
        (∀ n ∈ Block.modifiedOrDefinedVars bss, (ρ₀.store n).isSome) →
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
      stmtOk σ st →
      ∀ (ρ₀ : Env Expression),
        WellFormedSemanticEvalBool ρ₀.eval →
        WellFormedSemanticEvalVal ρ₀.eval →
        WellFormedSemanticEvalVar ρ₀.eval →
        WellFormedCoreEvalCong ρ₀.eval →
        (∀ n ∈ Stmt.modifiedOrDefinedVars st, (ρ₀.store n).isSome) →
        Transform.CanFail (LangCore π φ) st ρ₀ →
        Transform.CanFail (LangCore π φ) (stmtResult σ st) ρ₀)
    ∧
    -- Block CanFail preservation
    (∀ (σ : LoopElimState) (bss : Statements),
      Block.sizeOf bss ≤ sz →
      Block.noFuncDecl bss = Bool.true →
      blockOk σ bss →
      ∀ (ρ₀ : Env Expression),
        WellFormedSemanticEvalBool ρ₀.eval →
        WellFormedSemanticEvalVal ρ₀.eval →
        WellFormedSemanticEvalVar ρ₀.eval →
        WellFormedCoreEvalCong ρ₀.eval →
        (∀ n ∈ Block.modifiedOrDefinedVars bss, (ρ₀.store n).isSome) →
        CanFailBlock π φ bss ρ₀ →
        CanFailBlock π φ (blockResult σ bss) ρ₀) := by
  sorry

private theorem canfail_simulation
    (hwf_ext : WFEvalExtension φ) (sz : Nat) :
    (∀ (σ : LoopElimState) (st : Statement),
      Stmt.sizeOf st ≤ sz →
      stmtOk σ st →
      Stmt.noFuncDecl st = Bool.true →
      ∀ (ρ₀ : Env Expression),
        WellFormedSemanticEvalBool ρ₀.eval →
        WellFormedSemanticEvalVal ρ₀.eval →
        WellFormedSemanticEvalVar ρ₀.eval →
        WellFormedCoreEvalCong ρ₀.eval →
        (∀ n ∈ Stmt.modifiedOrDefinedVars st, (ρ₀.store n).isSome) →
        Transform.CanFail (LangCore π φ) st ρ₀ →
        Transform.CanFail (LangCore π φ) (stmtResult σ st) ρ₀)
    ∧
    (∀ (σ : LoopElimState) (bss : Statements),
      Block.sizeOf bss ≤ sz →
      blockOk σ bss →
      Block.noFuncDecl bss = Bool.true →
      ∀ (ρ₀ : Env Expression),
        WellFormedSemanticEvalBool ρ₀.eval →
        WellFormedSemanticEvalVal ρ₀.eval →
        WellFormedSemanticEvalVar ρ₀.eval →
        WellFormedCoreEvalCong ρ₀.eval →
        (∀ n ∈ Block.modifiedOrDefinedVars bss, (ρ₀.store n).isSome) →
        CanFailBlock π φ bss ρ₀ →
        CanFailBlock π φ (blockResult σ bss) ρ₀) := by
  induction sz with
  | zero =>
    refine ⟨fun σ st hsz _ _ => ?_, fun σ bss hsz _ _ => ?_⟩
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
        intro ρ₀ _ _ _ _ _ hcf
        rw [blockResult_nil]
        exact hcf
      | _ :: _ => exact absurd hsz (by simp [Block.sizeOf])
  | succ n ih =>
    constructor
    · intro σ st hsz hok hnofd ρ₀ hwfb hwfv hwfvar hwfc hswf hcf
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
            have ⟨cfg', hfail'', hreach'⟩ := ih.2 σ bss hsz_bss (stmtOk_block_inner hok) hnofd_bss ρ₀ hwfb hwfv hwfvar hwfc hswf ⟨inner_cfg, hfail', hinner⟩
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
            have ⟨cfg', hfail', hreach'⟩ := ih.2 σ tss hsz_tss (stmtOk_ite_left hok) hnofd_tss ρ₀ hwfb hwfv hwfvar hwfc (fun n hn => hswf n (List.mem_append_left _ hn)) ⟨cfg, hfail, r1⟩
            exact ⟨cfg', hfail', .step _ _ _ (.step_ite_true hcond hwfb') hreach'⟩
          | step_ite_false hcond hwfb' =>
            have ⟨cfg', hfail', hreach'⟩ := ih.2 (blockPostState σ tss) ess hsz_ess (stmtOk_ite_right hok) hnofd_ess ρ₀ hwfb hwfv hwfvar hwfc (fun n hn => hswf n (List.mem_append_right _ hn)) ⟨cfg, hfail, r1⟩
            exact ⟨cfg', hfail', .step _ _ _ (.step_ite_false hcond hwfb') hreach'⟩
          | step_ite_nondet_true =>
            have ⟨cfg', hfail', hreach'⟩ := ih.2 σ tss hsz_tss (stmtOk_ite_left hok) hnofd_tss ρ₀ hwfb hwfv hwfvar hwfc (fun n hn => hswf n (List.mem_append_left _ hn)) ⟨cfg, hfail, r1⟩
            exact ⟨cfg', hfail', .step _ _ _ .step_ite_nondet_true hreach'⟩
          | step_ite_nondet_false =>
            have ⟨cfg', hfail', hreach'⟩ := ih.2 (blockPostState σ tss) ess hsz_ess (stmtOk_ite_right hok) hnofd_ess ρ₀ hwfb hwfv hwfvar hwfc (fun n hn => hswf n (List.mem_append_right _ hn)) ⟨cfg, hfail, r1⟩
            exact ⟨cfg', hfail', .step _ _ _ .step_ite_nondet_false hreach'⟩
      | .loop guard measure inv body md =>
        -- Delegate to the simulation theorem's canfail part
        by_cases hnf₀ : ρ₀.hasFailure = Bool.true
        · exact ⟨.stmt (stmtResult σ (.loop guard measure inv body md)) ρ₀,
            by show ρ₀.hasFailure = Bool.true; exact hnf₀, .refl _⟩
        · exact (simulation π φ hwf_ext (Stmt.sizeOf (.loop guard measure inv body md))).2.2.1
            σ (.loop guard measure inv body md) (Nat.le_refl _) hnofd hok ρ₀ hwfb hwfv hwfvar hwfc hswf ⟨cfg, hfail, hreach⟩
    · intro σ bss hsz hok hnofd ρ₀ hwfb hwfv hwfvar hwfc hswf hcf
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
          simp [Block.noFuncDecl, Bool.and_eq_true] at hnofd; exact hnofd.1
        have hnofd_ss : Block.noFuncDecl ss = Bool.true := by
          simp [Block.noFuncDecl, Bool.and_eq_true] at hnofd; exact hnofd.2
        cases hreach with
        | refl =>
          exact ⟨.stmts (stmtResult σ s :: blockResult (stmtPostState σ s) ss) ρ₀, hfail, .refl _⟩
        | step _ _ _ h1 r1 => cases h1 with
          | step_stmts_cons =>
            match seq_canfail_prop r1 hfail with
            | .inl ⟨cfg', hf', hstar'⟩ =>
              have ⟨kcfg, hkf, hkstar⟩ := ih.1 σ s hsz_s (blockOk_cons_left hok) hnofd_s ρ₀ hwfb hwfv hwfvar hwfc (fun n hn => hswf n (List.mem_append_left _ hn)) ⟨cfg', hf', hstar'⟩
              exact canFail_head_to_block π φ (stmtResult σ s) (blockResult (stmtPostState σ s) ss) ρ₀ ⟨kcfg, hkf, hkstar⟩
            | .inr ⟨ρ₁, hterm_s, cfg', hf', hstar_rest⟩ =>
              -- s terminates at ρ₁, rest can fail
              have hsim_s := (simulation π φ hwf_ext (Stmt.sizeOf s)).1 σ s (Nat.le_refl _) hnofd_s (blockOk_cons_left hok) ρ₀ hwfb hwfv hwfvar hwfc (fun n hn => hswf n (List.mem_append_left _ hn))
              match hsim_s.1 ρ₁ hterm_s with
              | .inl hcf_s =>
                exact canFail_head_to_block π φ (stmtResult σ s) (blockResult (stmtPostState σ s) ss) ρ₀ hcf_s
              | .inr hok_s =>
                by_cases hnf₁ : ρ₁.hasFailure = Bool.true
                · have hcf_src_s : Transform.CanFail (LangCore π φ) s ρ₀ :=
                    ⟨.terminal ρ₁, by show ρ₁.hasFailure = Bool.true; exact hnf₁, hterm_s⟩
                  have hcf_tgt_s := ih.1 σ s hsz_s (blockOk_cons_left hok) hnofd_s ρ₀ hwfb hwfv hwfvar hwfc (fun n hn => hswf n (List.mem_append_left _ hn)) hcf_src_s
                  exact canFail_head_to_block π φ (stmtResult σ s) (blockResult (stmtPostState σ s) ss) ρ₀ hcf_tgt_s
                · have hnf₁' : ρ₁.hasFailure = Bool.false := by cases h : ρ₁.hasFailure <;> simp_all
                  have htgt_s := hok_s hnf₁'
                  have hwfb₁ := star_preserves_wf π φ hwf_ext hterm_s hwfb
                  have hwfv₁ := star_preserves_wfVal π φ hwf_ext hterm_s hwfv
                  have hwfvar₁ := star_preserves_wfVar π φ hwf_ext hterm_s hwfvar
                  have ⟨kcfg2, hkf2, hkstar2⟩ := ih.2 (stmtPostState σ s) ss hsz_ss (blockOk_cons_right hok) hnofd_ss ρ₁
                    hwfb₁ hwfv₁ hwfvar₁ ((smallStep_noFuncDecl_preserves_eval Expression (EvalCommand π φ) (EvalPureFunc φ) s ρ₀ ρ₁ hnofd_s hterm_s) ▸ hwfc) (fun n hn => stmt_star_preserves_isSome π φ s ρ₀ _ hterm_s n (hswf n (List.mem_append_right _ hn))) ⟨cfg', hf', hstar_rest⟩
                  exact canFail_tail_to_block π φ (stmtResult σ s)
                    (blockResult (stmtPostState σ s) ss) ρ₀ ρ₁ htgt_s ⟨kcfg2, hkf2, hkstar2⟩

/-! ## Top-level theorem -/

/-- The prefix that loop-elim claims for its fresh names. Any caller invoking
    `loopElim_overapproximatesAggressive` must include this in `reserved`. -/
def loopElimReservedPrefix : String := "$__loop"

/-- Havoc-only command lists have empty `Block.definedVars`. -/
private theorem definedVars_havoc_map (xs : List Expression.Ident)
    (md : MetaData Expression) :
    @Block.definedVars Expression Command _
        (xs.map (fun n => Stmt.cmd (HasHavoc.havoc n md))) = [] := by
  induction xs with
  | nil => simp [Block.definedVars]
  | cons x rest ih =>
    show Stmt.definedVars (Stmt.cmd (HasHavoc.havoc x md)) ++
         Block.definedVars (rest.map (fun n => Stmt.cmd (HasHavoc.havoc n md))) = []
    rw [ih]
    show HasVarsImp.definedVars (HasHavoc.havoc x md) ++ [] = []
    simp [HasVarsImp.definedVars, HasHavoc.havoc, Command.definedVars, Cmd.definedVars]

/-- A `mapIdx` of asserts has empty `Block.definedVars`. -/
private theorem definedVars_mapIdx_assert
    (inv : List (String × Expression.Expr)) (md : MetaData Expression)
    (label : Nat → (String × Expression.Expr) → String) :
    @Block.definedVars Expression Command _
      (inv.mapIdx fun i le =>
        Stmt.cmd (HasPassiveCmds.assert (label i le) le.2 md)) = [] := by
  induction inv generalizing label with
  | nil => simp [List.mapIdx_nil, Block.definedVars]
  | cons x rest ih =>
    rw [List.mapIdx_cons]
    show Stmt.definedVars (Stmt.cmd (HasPassiveCmds.assert (label 0 x) x.2 md)) ++
         Block.definedVars
           (rest.mapIdx (fun i le =>
              Stmt.cmd (HasPassiveCmds.assert (label (i + 1) le) le.2 md))) = []
    rw [ih]
    show HasVarsImp.definedVars (HasPassiveCmds.assert (label 0 x) x.2 md) ++ [] = []
    simp [HasVarsImp.definedVars, HasPassiveCmds.assert,
      Command.definedVars, Cmd.definedVars]

/-- A `mapIdx` of assumes has empty `Block.definedVars`. -/
private theorem definedVars_mapIdx_assume
    (inv : List (String × Expression.Expr)) (md : MetaData Expression)
    (label : Nat → (String × Expression.Expr) → String) :
    @Block.definedVars Expression Command _
      (inv.mapIdx fun i le =>
        Stmt.cmd (HasPassiveCmds.assume (label i le) le.2 md)) = [] := by
  induction inv generalizing label with
  | nil => simp [List.mapIdx_nil, Block.definedVars]
  | cons x rest ih =>
    rw [List.mapIdx_cons]
    show Stmt.definedVars (Stmt.cmd (HasPassiveCmds.assume (label 0 x) x.2 md)) ++
         Block.definedVars
           (rest.mapIdx (fun i le =>
              Stmt.cmd (HasPassiveCmds.assume (label (i + 1) le) le.2 md))) = []
    rw [ih]
    show HasVarsImp.definedVars (HasPassiveCmds.assume (label 0 x) x.2 md) ++ [] = []
    simp [HasVarsImp.definedVars, HasPassiveCmds.assume,
      Command.definedVars, Cmd.definedVars]

/-- The prefix `"$__loop"` is a list-prefix of `"$__loop_measure_<n>"`. -/
private theorem loopElimReservedPrefix_isPrefixOf_measure (loop_num : String) :
    loopElimReservedPrefix.toList.isPrefixOf
      (s!"$__loop_measure_{loop_num}").toList := by
  -- `s!"$__loop_measure_{loop_num}"` reduces to `"$__loop" ++ "_measure_" ++ loop_num`.
  show loopElimReservedPrefix.toList.isPrefixOf
        (("$__loop" ++ "_measure_" ++ loop_num).toList) = Bool.true
  rw [String.toList_append, String.toList_append]
  show loopElimReservedPrefix.toList.isPrefixOf
        (loopElimReservedPrefix.toList ++ "_measure_".toList ++ loop_num.toList) = Bool.true
  rw [List.append_assoc]
  exact isPrefixOf_append_self _ _

/-! Additional helper lemmas for `Block.getVars`/`Block.modifiedOrDefinedVars`
    over append and over havoc/assert/assume `map`/`mapIdx` — needed for
    `mem_touchedVars_stmtResult_loop` (mirroring `definedVars_havoc_map` etc.). -/

private theorem block_getVars_append (ss₁ ss₂ : Statements) :
    Block.getVars (ss₁ ++ ss₂) = Block.getVars ss₁ ++ Block.getVars ss₂ := by
  induction ss₁ with
  | nil => simp [Block.getVars]
  | cons s rest ih => simp [Block.getVars, ih, List.append_assoc]

private theorem block_modifiedOrDefinedVars_append (ss₁ ss₂ : Statements) :
    Block.modifiedOrDefinedVars (ss₁ ++ ss₂) =
      Block.modifiedOrDefinedVars ss₁ ++ Block.modifiedOrDefinedVars ss₂ := by
  induction ss₁ with
  | nil => simp [Block.modifiedOrDefinedVars]
  | cons s rest ih => simp [Block.modifiedOrDefinedVars, ih, List.append_assoc]

/-- Havoc-only command lists have empty `Block.getVars` (havoc reads nothing). -/
private theorem getVars_havoc_map (xs : List Expression.Ident)
    (md : MetaData Expression) :
    @Block.getVars Expression Command _ _
        (xs.map (fun n => Stmt.cmd (HasHavoc.havoc n md))) = [] := by
  induction xs with
  | nil => simp [Block.getVars]
  | cons x rest ih =>
    show @Stmt.getVars Expression Command _ _ (Stmt.cmd (HasHavoc.havoc x md)) ++
         @Block.getVars Expression Command _ _
           (rest.map (fun n => Stmt.cmd (HasHavoc.havoc n md))) = []
    rw [ih]
    show @HasVarsPure.getVars Expression Command _ (HasHavoc.havoc x md) ++ [] = []
    simp [HasVarsPure.getVars, HasHavoc.havoc, Command.getVars, Cmd.getVars,
      ExprOrNondet.getVars]

/-- Havoc-only command lists have `Block.modifiedOrDefinedVars` equal to the
    havoc'd variables (havoc modifies but does not define). -/
private theorem modifiedOrDefinedVars_havoc_map (xs : List Expression.Ident)
    (md : MetaData Expression) :
    @Block.modifiedOrDefinedVars Expression Command _
        (xs.map (fun n => Stmt.cmd (HasHavoc.havoc n md))) = xs := by
  induction xs with
  | nil => simp [Block.modifiedOrDefinedVars]
  | cons x rest ih =>
    show Stmt.modifiedOrDefinedVars (Stmt.cmd (HasHavoc.havoc x md)) ++
         Block.modifiedOrDefinedVars (rest.map (fun n => Stmt.cmd (HasHavoc.havoc n md))) =
         x :: rest
    rw [ih]
    show (Stmt.definedVars (Stmt.cmd (HasHavoc.havoc x md)) ++
          Stmt.modifiedVars (Stmt.cmd (HasHavoc.havoc x md))) ++ rest = x :: rest
    show (HasVarsImp.definedVars (HasHavoc.havoc x md) ++
          HasVarsImp.modifiedVars (HasHavoc.havoc x md)) ++ rest = x :: rest
    simp [HasVarsImp.definedVars, HasVarsImp.modifiedVars, HasHavoc.havoc,
      Command.definedVars, Command.modifiedVars, Cmd.definedVars, Cmd.modifiedVars]

/-- A `mapIdx` of asserts has empty `Block.modifiedOrDefinedVars`. -/
private theorem modifiedOrDefinedVars_mapIdx_assert
    (inv : List (String × Expression.Expr)) (md : MetaData Expression)
    (label : Nat → (String × Expression.Expr) → String) :
    @Block.modifiedOrDefinedVars Expression Command _
      (inv.mapIdx fun i le =>
        Stmt.cmd (HasPassiveCmds.assert (label i le) le.2 md)) = [] := by
  induction inv generalizing label with
  | nil => simp [List.mapIdx_nil, Block.modifiedOrDefinedVars]
  | cons x rest ih =>
    rw [List.mapIdx_cons]
    show Stmt.modifiedOrDefinedVars
           (Stmt.cmd (HasPassiveCmds.assert (label 0 x) x.2 md)) ++
         Block.modifiedOrDefinedVars
           (rest.mapIdx (fun i le =>
              Stmt.cmd (HasPassiveCmds.assert (label (i + 1) le) le.2 md))) = []
    rw [ih]
    show (Stmt.definedVars (Stmt.cmd (HasPassiveCmds.assert (label 0 x) x.2 md)) ++
          Stmt.modifiedVars (Stmt.cmd (HasPassiveCmds.assert (label 0 x) x.2 md))) ++ [] = []
    simp [HasVarsImp.definedVars, HasVarsImp.modifiedVars, HasPassiveCmds.assert,
      Command.definedVars, Command.modifiedVars, Cmd.definedVars, Cmd.modifiedVars]

/-- A `mapIdx` of assumes has empty `Block.modifiedOrDefinedVars`. -/
private theorem modifiedOrDefinedVars_mapIdx_assume
    (inv : List (String × Expression.Expr)) (md : MetaData Expression)
    (label : Nat → (String × Expression.Expr) → String) :
    @Block.modifiedOrDefinedVars Expression Command _
      (inv.mapIdx fun i le =>
        Stmt.cmd (HasPassiveCmds.assume (label i le) le.2 md)) = [] := by
  induction inv generalizing label with
  | nil => simp [List.mapIdx_nil, Block.modifiedOrDefinedVars]
  | cons x rest ih =>
    rw [List.mapIdx_cons]
    show Stmt.modifiedOrDefinedVars
           (Stmt.cmd (HasPassiveCmds.assume (label 0 x) x.2 md)) ++
         Block.modifiedOrDefinedVars
           (rest.mapIdx (fun i le =>
              Stmt.cmd (HasPassiveCmds.assume (label (i + 1) le) le.2 md))) = []
    rw [ih]
    show (Stmt.definedVars (Stmt.cmd (HasPassiveCmds.assume (label 0 x) x.2 md)) ++
          Stmt.modifiedVars (Stmt.cmd (HasPassiveCmds.assume (label 0 x) x.2 md))) ++ [] = []
    simp [HasVarsImp.definedVars, HasVarsImp.modifiedVars, HasPassiveCmds.assume,
      Command.definedVars, Command.modifiedVars, Cmd.definedVars, Cmd.modifiedVars]

/-- The `getVars` of a `mapIdx` of asserts equals the `flatMap` of `getVars`
    over the underlying expressions (the labels do not contribute reads). -/
private theorem getVars_mapIdx_assert
    (inv : List (String × Expression.Expr)) (md : MetaData Expression)
    (label : Nat → (String × Expression.Expr) → String) :
    @Block.getVars Expression Command _ _
      (inv.mapIdx fun i le =>
        Stmt.cmd (HasPassiveCmds.assert (label i le) le.2 md)) =
    inv.flatMap (fun lp => HasVarsPure.getVars lp.2) := by
  induction inv generalizing label with
  | nil => simp [List.mapIdx_nil, Block.getVars]
  | cons x rest ih =>
    rw [List.mapIdx_cons, List.flatMap_cons]
    show @Stmt.getVars Expression Command _ _
           (Stmt.cmd (HasPassiveCmds.assert (label 0 x) x.2 md)) ++
         @Block.getVars Expression Command _ _
           (rest.mapIdx (fun i le =>
              Stmt.cmd (HasPassiveCmds.assert (label (i + 1) le) le.2 md))) =
         HasVarsPure.getVars x.2 ++
         rest.flatMap (fun lp => HasVarsPure.getVars lp.2)
    rw [ih]
    show @HasVarsPure.getVars Expression Command _
            (HasPassiveCmds.assert (label 0 x) x.2 md) ++
         rest.flatMap (fun lp => HasVarsPure.getVars lp.2) =
         HasVarsPure.getVars x.2 ++
         rest.flatMap (fun lp => HasVarsPure.getVars lp.2)
    simp [HasVarsPure.getVars, HasPassiveCmds.assert, Command.getVars, Cmd.getVars]

/-- The `getVars` of a `mapIdx` of assumes equals the `flatMap` of `getVars`. -/
private theorem getVars_mapIdx_assume
    (inv : List (String × Expression.Expr)) (md : MetaData Expression)
    (label : Nat → (String × Expression.Expr) → String) :
    @Block.getVars Expression Command _ _
      (inv.mapIdx fun i le =>
        Stmt.cmd (HasPassiveCmds.assume (label i le) le.2 md)) =
    inv.flatMap (fun lp => HasVarsPure.getVars lp.2) := by
  induction inv generalizing label with
  | nil => simp [List.mapIdx_nil, Block.getVars]
  | cons x rest ih =>
    rw [List.mapIdx_cons, List.flatMap_cons]
    show @Stmt.getVars Expression Command _ _
           (Stmt.cmd (HasPassiveCmds.assume (label 0 x) x.2 md)) ++
         @Block.getVars Expression Command _ _
           (rest.mapIdx (fun i le =>
              Stmt.cmd (HasPassiveCmds.assume (label (i + 1) le) le.2 md))) =
         HasVarsPure.getVars x.2 ++
         rest.flatMap (fun lp => HasVarsPure.getVars lp.2)
    rw [ih]
    show @HasVarsPure.getVars Expression Command _
            (HasPassiveCmds.assume (label 0 x) x.2 md) ++
         rest.flatMap (fun lp => HasVarsPure.getVars lp.2) =
         HasVarsPure.getVars x.2 ++
         rest.flatMap (fun lp => HasVarsPure.getVars lp.2)
    simp [HasVarsPure.getVars, HasPassiveCmds.assume, Command.getVars, Cmd.getVars]

/-- The loop case of `mem_definedVars_stmtResult`. -/
private theorem mem_definedVars_stmtResult_loop
    (σ : LoopElimState)
    (guard : ExprOrNondet Expression)
    (measure : Option Expression.Expr)
    (inv : List (String × Expression.Expr))
    (body : Statements) (md : MetaData Expression)
    (hok : stmtOk σ (.loop guard measure inv body md))
    (n : Expression.Ident)
    (hn : n ∈ Stmt.definedVars (stmtResult σ (.loop guard measure inv body md))) :
    n ∈ Block.definedVars body ∨
    loopElimReservedPrefix.toList.isPrefixOf n.name.toList := by
  -- Mirror the existing `stmtResult_loop_struct` proof structure.  The KEY trick:
  -- the goal is wrapped in an existential whose witnesses are inferred by the
  -- closing `cases h; exact ⟨_, ..., rfl⟩` pattern.  We re-state the goal as
  -- such an existential (over the loop_num).
  suffices h_suff :
    ∃ (loop_num : String) (s' : Statement),
      stmtResult σ (.loop guard measure inv body md) = s' ∧
      ∀ m, m ∈ Stmt.definedVars s' →
        m ∈ Block.definedVars body ∨
        m = (⟨"$__loop_measure_" ++ loop_num, ()⟩ : Expression.Ident) by
    obtain ⟨loop_num, s', hs'_eq, hs'_prop⟩ := h_suff
    rw [hs'_eq] at hn
    rcases hs'_prop n hn with h_body | h_meas
    · exact .inl h_body
    · subst h_meas
      exact .inr (loopElimReservedPrefix_isPrefixOf_measure _)
  -- Now mirror `stmtResult_loop_struct`'s proof.
  change ∃ (loop_num : String) (s' : Statement),
    (match (stmtRun σ (.loop guard measure inv body md)).fst with
      | .ok (_, s'') => s'' | .error _ => default) = s' ∧
    ∀ m, m ∈ Stmt.definedVars s' →
      m ∈ Block.definedVars body ∨
      m = (⟨"$__loop_measure_" ++ loop_num, ()⟩ : Expression.Ident)
  have hok' := hok
  unfold stmtOk at hok'
  match h : (stmtRun σ (.loop guard measure inv body md)).fst with
  | .error e => simp [h, Except.isOk, Except.toBool] at hok'
  | .ok (b, s') =>
    simp only [h]
    -- Use dsimp (definitional simp) to fully reduce the monadic plumbing.
    dsimp only [stmtRun, StateT.run, ExceptT.run, Stmt.removeLoopsM,
      bind, pure, ExceptT.bind, ExceptT.pure, ExceptT.mk, ExceptT.bindCont,
      ExceptT.lift, StateT.bind, StateT.pure,
      Functor.map, liftM, monadLift, MonadLift.monadLift,
      modify, MonadState.modifyGet, StateT.modifyGet, StateT.map,
      genLoopNum, bumpStat] at h
    -- Closing tactic: `cases h; exact ⟨loop_num, _, rfl, fun m hm => ...⟩` as a
    -- SINGLE TERM, mirroring the unification trick from `stmtResult_loop_struct`.
    repeat (first
      | (cases h; exact
          ⟨(StringGenState.gen "loop" σ.gen).fst, _, rfl, fun m hm => by
            -- Stage 1: structural unfolding.
            simp only [Stmt.definedVars, Block.definedVars,
              block_definedVars_append, List.append_nil] at hm
            -- Stage 2: rewrite havoc/mapIdx-empty pieces via rw.
            repeat rw [definedVars_havoc_map] at hm
            repeat rw [definedVars_mapIdx_assert] at hm
            repeat rw [definedVars_mapIdx_assume] at hm
            -- Stage 3: rewrite individual cmd HasVarsImp.definedVars; the
            -- crucial step is that `HasInit.init` produces `[m_old_ident]`.
            simp only [HasVarsImp.definedVars, HasPassiveCmds.assert,
              HasPassiveCmds.assume, HasInit.init, HasIdent.ident,
              Command.definedVars, Cmd.definedVars,
              List.append_nil, List.nil_append, List.mem_append,
              List.not_mem_nil, false_or, or_false, List.mem_singleton] at hm
            -- After all reductions, hm is a (possibly-empty) nested disjunction
            -- of the form `m = m_old ∨ m ∈ Block.definedVars body` (in some order).
            -- Use a single `aesop`-style heuristic: match left or right of every disj.
            first
              | exact .inl hm                          -- (just body)
              | exact .inr hm                          -- (just m_old equality)
              | (rcases hm with h1 | h1 <;> first
                  | exact .inl h1 | exact .inr h1)
              | (rcases hm with h1 | h1 | h1 <;> first
                  | exact .inl h1 | exact .inr h1)
              | (rcases hm with h1 | h1 | h1 | h1 <;> first
                  | exact .inl h1 | exact .inr h1)
              | (rcases hm with h1 | h1 | h1 | h1 | h1 <;> first
                  | exact .inl h1 | exact .inr h1)⟩)
      | contradiction
      | (split at h; skip))
    all_goals (first
      | (cases h; exact
          ⟨(StringGenState.gen "loop" σ.gen).fst, _, rfl, fun m hm => by
            -- Stage 1: structural unfolding.
            simp only [Stmt.definedVars, Block.definedVars,
              block_definedVars_append, List.append_nil] at hm
            -- Stage 2: rewrite havoc/mapIdx-empty pieces via rw.
            repeat rw [definedVars_havoc_map] at hm
            repeat rw [definedVars_mapIdx_assert] at hm
            repeat rw [definedVars_mapIdx_assume] at hm
            -- Stage 3: rewrite individual cmd HasVarsImp.definedVars; the
            -- crucial step is that `HasInit.init` produces `[m_old_ident]`.
            simp only [HasVarsImp.definedVars, HasPassiveCmds.assert,
              HasPassiveCmds.assume, HasInit.init, HasIdent.ident,
              Command.definedVars, Cmd.definedVars,
              List.append_nil, List.nil_append, List.mem_append,
              List.not_mem_nil, false_or, or_false, List.mem_singleton] at hm
            -- After all reductions, hm is a (possibly-empty) nested disjunction
            -- of the form `m = m_old ∨ m ∈ Block.definedVars body` (in some order).
            -- Use a single `aesop`-style heuristic: match left or right of every disj.
            first
              | exact .inl hm                          -- (just body)
              | exact .inr hm                          -- (just m_old equality)
              | (rcases hm with h1 | h1 <;> first
                  | exact .inl h1 | exact .inr h1)
              | (rcases hm with h1 | h1 | h1 <;> first
                  | exact .inl h1 | exact .inr h1)
              | (rcases hm with h1 | h1 | h1 | h1 <;> first
                  | exact .inl h1 | exact .inr h1)
              | (rcases hm with h1 | h1 | h1 | h1 | h1 <;> first
                  | exact .inl h1 | exact .inr h1)⟩)
      | contradiction)

/-! Every name newly defined by the transform either was already a defined var
    of the source statement, or starts with the reserved `loopElimReservedPrefix`. -/
mutual
private theorem mem_definedVars_stmtResult
    (σ : LoopElimState) (s : Statement) (hok : stmtOk σ s) (n : Expression.Ident)
    (hn : n ∈ Stmt.definedVars (stmtResult σ s)) :
    n ∈ Stmt.definedVars s ∨
    loopElimReservedPrefix.toList.isPrefixOf n.name.toList := by
  match s with
  | .cmd c =>
    rw [stmtResult_cmd] at hn; exact .inl hn
  | .exit l md =>
    rw [stmtResult_exit] at hn; exact .inl hn
  | .funcDecl d md =>
    rw [stmtResult_funcDecl] at hn; exact .inl hn
  | .typeDecl tc md =>
    rw [stmtResult_typeDecl] at hn; exact .inl hn
  | .block l bss md =>
    rw [stmtResult_block] at hn
    -- Stmt.definedVars (.block l bss md) = Block.definedVars bss (by rfl)
    have hn' : n ∈ Block.definedVars (blockResult σ bss) := hn
    have := mem_definedVars_blockResult σ bss (stmtOk_block_inner hok) n hn'
    rcases this with h | h
    · exact .inl h
    · exact .inr h
  | .ite c tss ess md =>
    rw [stmtResult_ite] at hn
    have hn' : n ∈ Block.definedVars (blockResult σ tss) ++
                   Block.definedVars (blockResult (blockPostState σ tss) ess) := hn
    rcases List.mem_append.mp hn' with h | h
    · rcases mem_definedVars_blockResult σ tss (stmtOk_ite_left hok) n h with h | h
      · exact .inl (List.mem_append_left _ h)
      · exact .inr h
    · rcases mem_definedVars_blockResult (blockPostState σ tss) ess
                (stmtOk_ite_right hok) n h with h | h
      · exact .inl (List.mem_append_right _ h)
      · exact .inr h
  | .loop guard measure inv body md =>
    -- The loop body is *not* recursively transformed by `stmtResult` — only the
    -- outer wrapper is generated.  Hence `Stmt.definedVars (loop ... body ...)`
    -- equals `Block.definedVars body`, and the helper directly suffices.
    have h := mem_definedVars_stmtResult_loop σ guard measure inv body md hok n hn
    rcases h with h | h
    · exact .inl (by simp [Stmt.definedVars]; exact h)
    · exact .inr h

private theorem mem_definedVars_blockResult
    (σ : LoopElimState) (bss : Statements) (hok : blockOk σ bss)
    (n : Expression.Ident)
    (hn : n ∈ Block.definedVars (blockResult σ bss)) :
    n ∈ Block.definedVars bss ∨
    loopElimReservedPrefix.toList.isPrefixOf n.name.toList := by
  match bss with
  | [] =>
    rw [blockResult_nil] at hn
    have : n ∈ Block.definedVars ([] : Statements) := hn
    simp [Block.definedVars] at this
  | s :: rest =>
    rw [blockResult_cons] at hn
    have hn' : n ∈ Stmt.definedVars (stmtResult σ s) ++
                   Block.definedVars (blockResult (stmtPostState σ s) rest) := hn
    rcases List.mem_append.mp hn' with h | h
    · rcases mem_definedVars_stmtResult σ s (blockOk_cons_left hok) n h with h | h
      · exact .inl (List.mem_append_left _ h)
      · exact .inr h
    · rcases mem_definedVars_blockResult (stmtPostState σ s) rest
              (blockOk_cons_right hok) n h with h | h
      · exact .inl (List.mem_append_right _ h)
      · exact .inr h
end

/-! ## Helpers for `mem_touchedVars_stmtResult` -/

/-- The loop case of `definedVars_subset_stmtResult`.  Mirrors
    `mem_definedVars_stmtResult_loop`'s structural unfolding pattern but in
    the *converse* direction. -/
private theorem definedVars_subset_stmtResult_loop
    (σ : LoopElimState)
    (guard : ExprOrNondet Expression)
    (measure : Option Expression.Expr)
    (inv : List (String × Expression.Expr))
    (body : Statements) (md : MetaData Expression)
    (hok : stmtOk σ (.loop guard measure inv body md))
    (n : Expression.Ident)
    (hn : n ∈ Block.definedVars body) :
    n ∈ Stmt.definedVars (stmtResult σ (.loop guard measure inv body md)) := by
  suffices h_suff :
    ∃ (loop_num : String) (s' : Statement),
      stmtResult σ (.loop guard measure inv body md) = s' ∧
      ∀ m, m ∈ Block.definedVars body → m ∈ Stmt.definedVars s' by
    obtain ⟨_, s', hs'_eq, hs'_prop⟩ := h_suff
    rw [hs'_eq]
    exact hs'_prop n hn
  change ∃ (loop_num : String) (s' : Statement),
    (match (stmtRun σ (.loop guard measure inv body md)).fst with
      | .ok (_, s'') => s'' | .error _ => default) = s' ∧
    ∀ m, m ∈ Block.definedVars body → m ∈ Stmt.definedVars s'
  have hok' := hok
  unfold stmtOk at hok'
  match h : (stmtRun σ (.loop guard measure inv body md)).fst with
  | .error e => simp [h, Except.isOk, Except.toBool] at hok'
  | .ok (b, s') =>
    simp only [h]
    dsimp only [stmtRun, StateT.run, ExceptT.run, Stmt.removeLoopsM,
      bind, pure, ExceptT.bind, ExceptT.pure, ExceptT.mk, ExceptT.bindCont,
      ExceptT.lift, StateT.bind, StateT.pure,
      Functor.map, liftM, monadLift, MonadLift.monadLift,
      modify, MonadState.modifyGet, StateT.modifyGet, StateT.map,
      genLoopNum, bumpStat] at h
    repeat (first
      | (cases h; exact
          ⟨(StringGenState.gen "loop" σ.gen).fst, _, rfl, fun m hm => by
            simp only [Stmt.definedVars, Block.definedVars,
              block_definedVars_append, List.append_nil]
            repeat rw [definedVars_havoc_map]
            repeat rw [definedVars_mapIdx_assert]
            repeat rw [definedVars_mapIdx_assume]
            simp only [HasVarsImp.definedVars,
              HasPassiveCmds.assert, HasPassiveCmds.assume,
              HasInit.init, HasIdent.ident,
              Command.definedVars, Cmd.definedVars,
              List.append_nil, List.nil_append, List.mem_append,
              List.not_mem_nil, List.mem_singleton, false_or, or_false]
            first
              | exact hm
              | exact .inl hm
              | exact .inr hm
              | exact .inl (.inl hm)
              | exact .inl (.inr hm)
              | exact .inr (.inl hm)
              | exact .inr (.inr hm)
              | exact .inl (.inl (.inl hm))
              | exact .inl (.inl (.inr hm))
              | exact .inl (.inr (.inl hm))
              | exact .inl (.inr (.inr hm))
              | exact .inr (.inl (.inl hm))
              | exact .inr (.inl (.inr hm))
              | exact .inr (.inr (.inl hm))
              | exact .inr (.inr (.inr hm))⟩)
      | contradiction
      | (split at h; skip))
    all_goals (first
      | (cases h; exact
          ⟨(StringGenState.gen "loop" σ.gen).fst, _, rfl, fun m hm => by
            simp only [Stmt.definedVars, Block.definedVars,
              block_definedVars_append, List.append_nil]
            repeat rw [definedVars_havoc_map]
            repeat rw [definedVars_mapIdx_assert]
            repeat rw [definedVars_mapIdx_assume]
            simp only [HasVarsImp.definedVars,
              HasPassiveCmds.assert, HasPassiveCmds.assume,
              HasInit.init, HasIdent.ident,
              Command.definedVars, Cmd.definedVars,
              List.append_nil, List.nil_append, List.mem_append,
              List.not_mem_nil, List.mem_singleton, false_or, or_false]
            first
              | exact hm
              | exact .inl hm
              | exact .inr hm
              | exact .inl (.inl hm)
              | exact .inl (.inr hm)
              | exact .inr (.inl hm)
              | exact .inr (.inr hm)
              | exact .inl (.inl (.inl hm))
              | exact .inl (.inl (.inr hm))
              | exact .inl (.inr (.inl hm))
              | exact .inl (.inr (.inr hm))
              | exact .inr (.inl (.inl hm))
              | exact .inr (.inl (.inr hm))
              | exact .inr (.inr (.inl hm))
              | exact .inr (.inr (.inr hm))⟩)
      | contradiction)

-- The transform preserves `definedVars` (the source's defined vars are a
-- subset of the transform's defined vars), assuming the transform succeeds.
mutual
private theorem definedVars_subset_stmtResult
    (σ : LoopElimState) (s : Statement) (hok : stmtOk σ s)
    (n : Expression.Ident)
    (hn : n ∈ Stmt.definedVars s) :
    n ∈ Stmt.definedVars (stmtResult σ s) := by
  match s with
  | .cmd c => rw [stmtResult_cmd]; exact hn
  | .exit l md => rw [stmtResult_exit]; exact hn
  | .funcDecl d md => rw [stmtResult_funcDecl]; exact hn
  | .typeDecl tc md => rw [stmtResult_typeDecl]; exact hn
  | .block l bss md =>
    rw [stmtResult_block]
    show n ∈ Block.definedVars (blockResult σ bss)
    have h : n ∈ Block.definedVars bss := hn
    exact definedVars_subset_blockResult σ bss (stmtOk_block_inner hok) n h
  | .ite c tss ess md =>
    rw [stmtResult_ite]
    show n ∈ Block.definedVars (blockResult σ tss) ++
              Block.definedVars (blockResult (blockPostState σ tss) ess)
    have h : n ∈ Block.definedVars tss ++ Block.definedVars ess := hn
    rcases List.mem_append.mp h with ht | he
    · exact List.mem_append_left _
        (definedVars_subset_blockResult σ tss (stmtOk_ite_left hok) n ht)
    · exact List.mem_append_right _
        (definedVars_subset_blockResult (blockPostState σ tss) ess
          (stmtOk_ite_right hok) n he)
  | .loop guard measure inv body md =>
    have h : n ∈ Block.definedVars body := hn
    exact definedVars_subset_stmtResult_loop σ guard measure inv body md hok n h

private theorem definedVars_subset_blockResult
    (σ : LoopElimState) (ss : Statements) (hok : blockOk σ ss)
    (n : Expression.Ident)
    (hn : n ∈ Block.definedVars ss) :
    n ∈ Block.definedVars (blockResult σ ss) := by
  match ss with
  | [] => exact hn
  | s :: rest =>
    rw [blockResult_cons]
    show n ∈ Stmt.definedVars (stmtResult σ s) ++
              Block.definedVars (blockResult (stmtPostState σ s) rest)
    have h : n ∈ Stmt.definedVars s ++ Block.definedVars rest := hn
    rcases List.mem_append.mp h with hs | hr
    · exact List.mem_append_left _
        (definedVars_subset_stmtResult σ s (blockOk_cons_left hok) n hs)
    · exact List.mem_append_right _
        (definedVars_subset_blockResult (stmtPostState σ s) rest
          (blockOk_cons_right hok) n hr)
end

/-- The loop case of `mem_touchedVars_stmtResult`.

    Strategy: mirror `mem_definedVars_stmtResult_loop`'s `dsimp`+structural
    pattern.  The closing `cases h` exposes the concrete transform output, then
    we expand `Stmt.touchedVars` via a series of helper-rewrites and dispatch
    each disjunct of `hm` to either `m ∈ definedVars (transform)` or
    `m ∈ touchedVars (source)`.

    NOTE: The body of this proof is below at the leaf-dispatch sorry. The
    overall structure is in place: the `hnd_src` half is fully proved, and
    the suffices+dsimp+structural-cases scaffold mirrors
    `mem_definedVars_stmtResult_loop`.  What remains is the inner per-leaf
    dispatch: when the closing `cases h` does not fully substitute `s'`
    (because of unreduced inner `match`/`bind` in `h`), the resulting `hm` is
    in the form `m ∈ Stmt.modifiedOrDefinedVars s' ∨ m ∈ Stmt.getVars s'`
    with `s'` still abstract.  Resolving this requires either further
    `simp at h` to fully reduce or a different `cases`/`subst` strategy. -/
private theorem mem_touchedVars_stmtResult_loop
    (σ : LoopElimState)
    (guard : ExprOrNondet Expression)
    (measure : Option Expression.Expr)
    (inv : List (String × Expression.Expr))
    (body : Statements) (md : MetaData Expression)
    (hok : stmtOk σ (.loop guard measure inv body md))
    (n : Expression.Ident)
    (hn : n ∈ Stmt.touchedVars (stmtResult σ (.loop guard measure inv body md)))
    (hnd : n ∉ Stmt.definedVars (stmtResult σ (.loop guard measure inv body md))) :
    n ∈ Stmt.touchedVars (.loop guard measure inv body md) ∧
    n ∉ Stmt.definedVars (.loop guard measure inv body md) := by
  -- The source's `definedVars` ⊆ transform's `definedVars`; combined with
  -- `hnd` we conclude the second component immediately.
  have hnd_src : n ∉ Stmt.definedVars (.loop guard measure inv body md) := fun h =>
    hnd (definedVars_subset_stmtResult_loop σ guard measure inv body md hok n h)
  refine ⟨?_, hnd_src⟩
  -- Suffices: the transform output equals some `s'` such that every `m` in
  -- its `touchedVars` lies in either its `definedVars` (then `hnd` rules it
  -- out) or in source's `touchedVars`.
  suffices h_suff :
    ∃ (loop_num : String) (s' : Statement),
      stmtResult σ (.loop guard measure inv body md) = s' ∧
      ∀ m, m ∈ Stmt.touchedVars s' →
        m ∈ Stmt.definedVars s' ∨
        m ∈ Stmt.touchedVars (.loop guard measure inv body md) by
    obtain ⟨_, s', hs'_eq, hs'_prop⟩ := h_suff
    rw [hs'_eq] at hn hnd
    rcases hs'_prop n hn with hdef | hsrc
    · exact absurd hdef hnd
    · exact hsrc
  -- Prove the suffices via the dsimp+structural-cases pattern.
  change ∃ (loop_num : String) (s' : Statement),
    (match (stmtRun σ (.loop guard measure inv body md)).fst with
      | .ok (_, s'') => s'' | .error _ => default) = s' ∧
    ∀ m, m ∈ Stmt.touchedVars s' →
      m ∈ Stmt.definedVars s' ∨
      m ∈ Stmt.touchedVars (.loop guard measure inv body md)
  have hok' := hok
  unfold stmtOk at hok'
  match h : (stmtRun σ (.loop guard measure inv body md)).fst with
  | .error e => simp [h, Except.isOk, Except.toBool] at hok'
  | .ok (b, s') =>
    simp only [h]
    dsimp only [stmtRun, StateT.run, ExceptT.run, Stmt.removeLoopsM,
      bind, pure, ExceptT.bind, ExceptT.pure, ExceptT.mk, ExceptT.bindCont,
      ExceptT.lift, StateT.bind, StateT.pure,
      Functor.map, liftM, monadLift, MonadLift.monadLift,
      modify, MonadState.modifyGet, StateT.modifyGet, StateT.map,
      genLoopNum, bumpStat,
      Except.bind, Except.pure, Except.map] at h
    -- Inline per-case proof.
    --
    -- Key auxiliary facts:
    -- (1) `assigned_vars ⊆ Block.modifiedVars body ⊆ Stmt.modifiedOrDefinedVars (.loop ...)`.
    -- (2) `m_old_ident ∈ Stmt.definedVars (concrete)` (when measure = some _).
    -- (3) `Block.modifiedOrDefinedVars body ⊆ Stmt.modifiedOrDefinedVars (.loop ...)`.
    -- (4) `Block.getVars body ⊆ Stmt.getVars (.loop ...)`.
    -- (5) Same for `guard.getVars`, `(measure.map getVars).getD []`,
    --     `inv.flatMap (fun lp => HasVarsPure.getVars lp.2)`.
    --
    -- Helper: if `m` lies in source's `touchedVars`, that suffices.
    -- We pre-build closures for each "way of landing in source".
    have body_md_to_src : ∀ m, m ∈ Block.modifiedOrDefinedVars body →
        m ∈ Stmt.touchedVars (.loop guard measure inv body md) := by
      intro m hm
      apply List.mem_append_left
      show m ∈ Stmt.definedVars (.loop guard measure inv body md) ++
                Stmt.modifiedVars (.loop guard measure inv body md)
      have := (modifiedOrDefinedVars_subset (Block.sizeOf body)).2
                body (Nat.le_refl _) m hm
      simp only [Stmt.definedVars, Stmt.modifiedVars]; exact this
    have body_mod_to_src : ∀ m, m ∈ Block.modifiedVars body →
        m ∈ Stmt.touchedVars (.loop guard measure inv body md) := by
      intro m hm
      apply List.mem_append_left
      show m ∈ Stmt.definedVars (.loop guard measure inv body md) ++
                Stmt.modifiedVars (.loop guard measure inv body md)
      apply List.mem_append_right
      show m ∈ Block.modifiedVars body
      exact hm
    have body_def_to_src : ∀ m, m ∈ Block.definedVars body →
        m ∈ Stmt.touchedVars (.loop guard measure inv body md) := by
      intro m hm
      apply List.mem_append_left
      show m ∈ Stmt.definedVars (.loop guard measure inv body md) ++
                Stmt.modifiedVars (.loop guard measure inv body md)
      apply List.mem_append_left
      show m ∈ Block.definedVars body
      exact hm
    have body_gv_to_src : ∀ m, m ∈ Block.getVars body →
        m ∈ Stmt.touchedVars (.loop guard measure inv body md) := by
      intro m hm
      apply List.mem_append_right
      show m ∈ guard.getVars ++ (measure.map HasVarsPure.getVars).getD [] ++
                (inv.flatMap fun lp => HasVarsPure.getVars lp.2) ++
                Block.getVars body
      exact List.mem_append_right _ hm
    have guard_to_src : ∀ m, m ∈ guard.getVars →
        m ∈ Stmt.touchedVars (.loop guard measure inv body md) := by
      intro m hm
      apply List.mem_append_right
      show m ∈ guard.getVars ++ (measure.map HasVarsPure.getVars).getD [] ++
                (inv.flatMap fun lp => HasVarsPure.getVars lp.2) ++
                Block.getVars body
      exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ hm))
    have measure_to_src : ∀ m, m ∈ (measure.map HasVarsPure.getVars).getD [] →
        m ∈ Stmt.touchedVars (.loop guard measure inv body md) := by
      intro m hm
      apply List.mem_append_right
      show m ∈ guard.getVars ++ (measure.map HasVarsPure.getVars).getD [] ++
                (inv.flatMap fun lp => HasVarsPure.getVars lp.2) ++
                Block.getVars body
      exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ hm))
    have inv_to_src : ∀ m, m ∈ inv.flatMap (fun lp => HasVarsPure.getVars lp.2) →
        m ∈ Stmt.touchedVars (.loop guard measure inv body md) := by
      intro m hm
      apply List.mem_append_right
      show m ∈ guard.getVars ++ (measure.map HasVarsPure.getVars).getD [] ++
                (inv.flatMap fun lp => HasVarsPure.getVars lp.2) ++
                Block.getVars body
      exact List.mem_append_left _ (List.mem_append_right _ hm)
    -- Specific consequences:
    -- For `measure = some m_e`, `HasVarsPure.getVars m_e ⊆ measure.map getVars`.
    have measure_some_to_src : ∀ (m_e : Expression.Expr) (m : Expression.Ident),
        measure = some m_e → m ∈ HasVarsPure.getVars m_e →
        m ∈ Stmt.touchedVars (.loop guard measure inv body md) := by
      intro m_e m heq hm
      apply measure_to_src
      rw [heq]
      simp [Option.map, Option.getD]
      exact hm
    have guard_det_to_src : ∀ (g : Expression.Expr) (m : Expression.Ident),
        guard = .det g → m ∈ HasVarsPure.getVars g →
        m ∈ Stmt.touchedVars (.loop guard measure inv body md) := by
      intro g m heq hm
      apply guard_to_src
      rw [heq]
      show m ∈ HasVarsPure.getVars g
      exact hm
    -- Per-case tactic: dispatch each atomic disjunct of `hm` to the
    -- appropriate side of the goal.
    --
    -- The outer `repeat (first | (cases h; exact …) | contradiction |
    -- (split at h; skip))` exposes the concrete transform output for each
    -- (guard × measure) sub-case.  The inner `by` block then expands
    -- `Stmt.touchedVars (concrete output)` via our helper rewrites
    -- (`getVars_havoc_map`, `getVars_mapIdx_assert`, …) and dispatches
    -- each disjunct of `hm` to either `m ∈ Stmt.definedVars (concrete)`
    -- (handled by `Or.inl + subst + simp`) or `m ∈ Stmt.touchedVars (.loop …)`
    -- (handled by one of the `body_*_to_src` / `guard_to_src` / `measure_to_src` /
    -- `inv_to_src` closures).  In one of the branches `cases h` does not
    -- fully substitute `s'` (it still depends on an inner abstract `y`
    -- introduced by `bind`); the leaf-dispatch sorry below covers that gap.
    repeat (first
      | (cases h; exact
          ⟨(StringGenState.gen "loop" σ.gen).fst, _, rfl, fun m hm => by
            simp only [Stmt.touchedVars, Block.touchedVars,
              Stmt.modifiedOrDefinedVars, Stmt.getVars, Stmt.definedVars,
              Block.modifiedOrDefinedVars, Block.getVars, Block.definedVars,
              block_modifiedOrDefinedVars_append, block_getVars_append,
              block_definedVars_append,
              modifiedOrDefinedVars_havoc_map, getVars_havoc_map,
              definedVars_havoc_map,
              modifiedOrDefinedVars_mapIdx_assert, getVars_mapIdx_assert,
              definedVars_mapIdx_assert,
              modifiedOrDefinedVars_mapIdx_assume, getVars_mapIdx_assume,
              definedVars_mapIdx_assume,
              HasVarsImp.definedVars, HasVarsImp.modifiedVars,
              HasVarsPure.getVars,
              HasPassiveCmds.assert, HasPassiveCmds.assume,
              HasInit.init, HasIdent.ident, HasHavoc.havoc,
              Command.definedVars, Command.modifiedVars, Command.getVars,
              Cmd.definedVars, Cmd.modifiedVars, Cmd.getVars,
              ExprOrNondet.getVars,
              List.append_nil, List.nil_append,
              List.mem_append, List.not_mem_nil, List.mem_singleton,
              false_or, or_false] at hm
            try simp only [List.mem_filter, decide_eq_true_eq] at hm
            -- Dispatch each disjunct of `hm` to the appropriate side.
            (repeat first
              | exact .inr (body_md_to_src _ hm)
              | exact .inr (body_mod_to_src _ hm.1)
              | exact .inr (body_mod_to_src _ hm)
              | exact .inr (body_def_to_src _ hm)
              | exact .inr (body_gv_to_src _ hm)
              | exact .inr (guard_to_src _ hm)
              | exact .inr (measure_to_src _ hm)
              | exact .inr (inv_to_src _ hm)
              | (rcases hm with hm | hm)
              | (refine .inl ?_
                 subst hm
                 simp [Stmt.definedVars, Block.definedVars, block_definedVars_append,
                   definedVars_havoc_map, definedVars_mapIdx_assert,
                   definedVars_mapIdx_assume,
                   HasVarsImp.definedVars, HasInit.init, HasIdent.ident,
                   Command.definedVars, Cmd.definedVars])
              | exact absurd hm List.not_mem_nil)
            -- Residual goal (abstract-`s'` branch).  In a few rare paths
            -- through the outer `repeat (first | ...)`, the leading `cases h`
            -- does not fully concretize `s'` because the inner monadic bind
            -- chain still contains an unreduced `match guard with` /
            -- `match measure with` / `if measure.isSome` form.  We then have
            -- `hm : m ∈ Stmt.touchedVars s'` with `s'` abstract.
            --
            -- The decomposition `s' = .block loop_label [.., .ite ...]` from
            -- `stmtResult_loop_then_branch_struct` exposes abstract
            -- `prefix_stmts / suffix_stmts / exit_state_stmts` pieces.
            -- Closing this gap requires structural lemmas asserting that
            -- their `modifiedOrDefinedVars / getVars` are contained in
            --   Block.modifiedVars body ∪ {m_old_ident}     (mod-def)
            --   guard.getVars ∪ inv.getVars ∪ measure.getVars  (get)
            -- which are not yet available in this file.  Deferring.
            all_goals sorry⟩)
      | contradiction
      | (split at h; skip))
    all_goals (first
      | (cases h; exact
          ⟨(StringGenState.gen "loop" σ.gen).fst, _, rfl, fun m hm => by
            simp only [Stmt.touchedVars, Block.touchedVars,
              Stmt.modifiedOrDefinedVars, Stmt.getVars, Stmt.definedVars,
              Block.modifiedOrDefinedVars, Block.getVars, Block.definedVars,
              block_modifiedOrDefinedVars_append, block_getVars_append,
              block_definedVars_append,
              modifiedOrDefinedVars_havoc_map, getVars_havoc_map,
              definedVars_havoc_map,
              modifiedOrDefinedVars_mapIdx_assert, getVars_mapIdx_assert,
              definedVars_mapIdx_assert,
              modifiedOrDefinedVars_mapIdx_assume, getVars_mapIdx_assume,
              definedVars_mapIdx_assume,
              HasVarsImp.definedVars, HasVarsImp.modifiedVars,
              HasVarsPure.getVars,
              HasPassiveCmds.assert, HasPassiveCmds.assume,
              HasInit.init, HasIdent.ident, HasHavoc.havoc,
              Command.definedVars, Command.modifiedVars, Command.getVars,
              Cmd.definedVars, Cmd.modifiedVars, Cmd.getVars,
              ExprOrNondet.getVars,
              List.append_nil, List.nil_append,
              List.mem_append, List.not_mem_nil, List.mem_singleton,
              false_or, or_false] at hm
            try simp only [List.mem_filter, decide_eq_true_eq] at hm
            (repeat first
              | exact .inr (body_md_to_src _ hm)
              | exact .inr (body_mod_to_src _ hm.1)
              | exact .inr (body_mod_to_src _ hm)
              | exact .inr (body_def_to_src _ hm)
              | exact .inr (body_gv_to_src _ hm)
              | exact .inr (guard_to_src _ hm)
              | exact .inr (measure_to_src _ hm)
              | exact .inr (inv_to_src _ hm)
              | (rcases hm with hm | hm)
              | (refine .inl ?_
                 subst hm
                 simp [Stmt.definedVars, Block.definedVars, block_definedVars_append,
                   definedVars_havoc_map, definedVars_mapIdx_assert,
                   definedVars_mapIdx_assume,
                   HasVarsImp.definedVars, HasInit.init, HasIdent.ident,
                   Command.definedVars, Cmd.definedVars])
              | exact absurd hm List.not_mem_nil)
            done⟩)
      | contradiction)

-- Every name in the transform's `touchedVars` outside its `definedVars` was
-- already in the source's `touchedVars` outside source's `definedVars`.
mutual
private theorem mem_touchedVars_stmtResult
    (σ : LoopElimState) (s : Statement) (hok : stmtOk σ s)
    (n : Expression.Ident)
    (hn : n ∈ Stmt.touchedVars (stmtResult σ s))
    (hnd : n ∉ Stmt.definedVars (stmtResult σ s)) :
    n ∈ Stmt.touchedVars s ∧ n ∉ Stmt.definedVars s := by
  match s with
  | .cmd c =>
    rw [stmtResult_cmd] at hn hnd
    exact ⟨hn, hnd⟩
  | .exit l md =>
    rw [stmtResult_exit] at hn hnd
    exact ⟨hn, hnd⟩
  | .funcDecl d md =>
    rw [stmtResult_funcDecl] at hn hnd
    exact ⟨hn, hnd⟩
  | .typeDecl tc md =>
    rw [stmtResult_typeDecl] at hn hnd
    exact ⟨hn, hnd⟩
  | .block l bss md =>
    rw [stmtResult_block] at hn hnd
    -- Stmt.touchedVars (.block l bss md) = Block.touchedVars bss
    have hn' : n ∈ Block.touchedVars (blockResult σ bss) := by
      have : n ∈ Stmt.modifiedOrDefinedVars (.block l (blockResult σ bss) md) ++
                 Stmt.getVars (.block l (blockResult σ bss) md) := hn
      show n ∈ Block.modifiedOrDefinedVars (blockResult σ bss) ++
                Block.getVars (blockResult σ bss)
      exact this
    have hnd' : n ∉ Block.definedVars (blockResult σ bss) := hnd
    have ⟨ht_src, hd_src⟩ :=
      mem_touchedVars_blockResult σ bss (stmtOk_block_inner hok) n hn' hnd'
    refine ⟨?_, hd_src⟩
    show n ∈ Stmt.modifiedOrDefinedVars (.block l bss md) ++
              Stmt.getVars (.block l bss md)
    show n ∈ Block.modifiedOrDefinedVars bss ++ Block.getVars bss
    exact ht_src
  | .ite c tss ess md =>
    rw [stmtResult_ite] at hn hnd
    -- definedVars (.ite c (br σ tss) (br σ' ess) md) = definedVars (br σ tss) ++ definedVars (br σ' ess)
    have hnd_t : n ∉ Block.definedVars (blockResult σ tss) := by
      intro h
      apply hnd
      show n ∈ Block.definedVars (blockResult σ tss) ++
                Block.definedVars (blockResult (blockPostState σ tss) ess)
      exact List.mem_append_left _ h
    have hnd_e : n ∉ Block.definedVars (blockResult (blockPostState σ tss) ess) := by
      intro h
      apply hnd
      show n ∈ Block.definedVars (blockResult σ tss) ++
                Block.definedVars (blockResult (blockPostState σ tss) ess)
      exact List.mem_append_right _ h
    -- touchedVars (.ite c tss' ess' md) = (modifiedOrDefinedVars tss' ++ modifiedOrDefinedVars ess')
    --                                    ++ (c.getVars ++ getVars tss' ++ getVars ess')
    have hn' : n ∈ (Block.modifiedOrDefinedVars (blockResult σ tss) ++
                    Block.modifiedOrDefinedVars (blockResult (blockPostState σ tss) ess)) ++
                   (c.getVars ++ Block.getVars (blockResult σ tss) ++
                    Block.getVars (blockResult (blockPostState σ tss) ess)) := hn
    -- Goal: ⟨n ∈ touchedVars source, n ∉ definedVars source⟩.  Source's
    -- touchedVars = mod-or-def tss ++ mod-or-def ess ++ c.getVars ++ getVars tss ++ getVars ess.
    -- Source's definedVars = definedVars tss ++ definedVars ess.
    -- Strategy: dispatch on which sub-component contains n.
    -- For the pieces inside one branch (mod-or-def tss', getVars tss', etc.), we
    -- recurse via `mem_touchedVars_blockResult` to map into source's touched/def.
    -- For c.getVars, it's directly in source's getVars.
    -- The "n ∉ definedVars source" obligation: by contrapositive of
    -- `definedVars_subset_blockResult` applied to each branch.
    have hd_src_goal : n ∉ Stmt.definedVars (.ite c tss ess md) := by
      intro h
      have h' : n ∈ Block.definedVars tss ++ Block.definedVars ess := h
      rcases List.mem_append.mp h' with htd | hed
      · apply hnd_t
        exact (definedVars_subset_blockResult σ tss (stmtOk_ite_left hok) n htd)
      · apply hnd_e
        exact (definedVars_subset_blockResult (blockPostState σ tss) ess
          (stmtOk_ite_right hok) n hed)
    refine ⟨?_, hd_src_goal⟩
    show n ∈ Stmt.modifiedOrDefinedVars (.ite c tss ess md) ++
              Stmt.getVars (.ite c tss ess md)
    rcases List.mem_append.mp hn' with hmd | hgv
    · -- n ∈ mod-or-def tss' ++ mod-or-def ess'.  Recurse via touchedVars on each.
      rcases List.mem_append.mp hmd with hmt | hme
      · -- n ∈ mod-or-def (blockResult σ tss).  Get touchedVars membership, recurse.
        have hn_t : n ∈ Block.touchedVars (blockResult σ tss) :=
          List.mem_append_left _ hmt
        have ⟨ht_src, _⟩ :=
          mem_touchedVars_blockResult σ tss (stmtOk_ite_left hok) n hn_t hnd_t
        rcases List.mem_append.mp ht_src with htmd | htgv
        · apply List.mem_append_left
          show n ∈ Block.modifiedOrDefinedVars tss ++ Block.modifiedOrDefinedVars ess
          exact List.mem_append_left _ htmd
        · apply List.mem_append_right
          show n ∈ c.getVars ++ Block.getVars tss ++ Block.getVars ess
          exact List.mem_append_left _ (List.mem_append_right _ htgv)
      · -- n ∈ mod-or-def (blockResult σ' ess)
        have hn_t : n ∈ Block.touchedVars (blockResult (blockPostState σ tss) ess) :=
          List.mem_append_left _ hme
        have ⟨ht_src, _⟩ :=
          mem_touchedVars_blockResult (blockPostState σ tss) ess
            (stmtOk_ite_right hok) n hn_t hnd_e
        rcases List.mem_append.mp ht_src with hemd | hegv
        · apply List.mem_append_left
          show n ∈ Block.modifiedOrDefinedVars tss ++ Block.modifiedOrDefinedVars ess
          exact List.mem_append_right _ hemd
        · apply List.mem_append_right
          show n ∈ c.getVars ++ Block.getVars tss ++ Block.getVars ess
          exact List.mem_append_right _ hegv
    · rcases List.mem_append.mp hgv with hcg | hee
      · rcases List.mem_append.mp hcg with hcond | htg
        · -- n ∈ c.getVars → in source's getVars
          apply List.mem_append_right
          show n ∈ c.getVars ++ Block.getVars tss ++ Block.getVars ess
          exact List.mem_append_left _ (List.mem_append_left _ hcond)
        · -- n ∈ Block.getVars (blockResult σ tss) → recurse via touchedVars helper
          have hn_t : n ∈ Block.touchedVars (blockResult σ tss) :=
            List.mem_append_right _ htg
          have ⟨ht_src, _⟩ :=
            mem_touchedVars_blockResult σ tss (stmtOk_ite_left hok) n hn_t hnd_t
          rcases List.mem_append.mp ht_src with htmd | htgv
          · apply List.mem_append_left
            show n ∈ Block.modifiedOrDefinedVars tss ++ Block.modifiedOrDefinedVars ess
            exact List.mem_append_left _ htmd
          · apply List.mem_append_right
            show n ∈ c.getVars ++ Block.getVars tss ++ Block.getVars ess
            exact List.mem_append_left _ (List.mem_append_right _ htgv)
      · -- n ∈ Block.getVars (blockResult σ' ess) → recurse via touchedVars helper
        have hn_t : n ∈ Block.touchedVars (blockResult (blockPostState σ tss) ess) :=
          List.mem_append_right _ hee
        have ⟨ht_src, _⟩ :=
          mem_touchedVars_blockResult (blockPostState σ tss) ess
            (stmtOk_ite_right hok) n hn_t hnd_e
        rcases List.mem_append.mp ht_src with hemd | hegv
        · apply List.mem_append_left
          show n ∈ Block.modifiedOrDefinedVars tss ++ Block.modifiedOrDefinedVars ess
          exact List.mem_append_right _ hemd
        · apply List.mem_append_right
          show n ∈ c.getVars ++ Block.getVars tss ++ Block.getVars ess
          exact List.mem_append_right _ hegv
  | .loop guard measure inv body md =>
    exact mem_touchedVars_stmtResult_loop σ guard measure inv body md hok n hn hnd

private theorem mem_touchedVars_blockResult
    (σ : LoopElimState) (bss : Statements) (hok : blockOk σ bss)
    (n : Expression.Ident)
    (hn : n ∈ Block.touchedVars (blockResult σ bss))
    (hnd : n ∉ Block.definedVars (blockResult σ bss)) :
    n ∈ Block.touchedVars bss ∧ n ∉ Block.definedVars bss := by
  match bss with
  | [] =>
    rw [blockResult_nil] at hn hnd
    refine ⟨?_, hnd⟩
    -- Block.touchedVars [] = [] ++ [] = [] → contradiction
    simp [Block.touchedVars, Block.modifiedOrDefinedVars, Block.getVars] at hn
  | s :: rest =>
    rw [blockResult_cons] at hn hnd
    -- definedVars (s :: rest result) = definedVars (stmtResult σ s) ++ definedVars (blockResult ...)
    have hnd_s : n ∉ Stmt.definedVars (stmtResult σ s) := by
      intro h
      apply hnd
      show n ∈ Stmt.definedVars (stmtResult σ s) ++
                Block.definedVars (blockResult (stmtPostState σ s) rest)
      exact List.mem_append_left _ h
    have hnd_r : n ∉ Block.definedVars (blockResult (stmtPostState σ s) rest) := by
      intro h
      apply hnd
      show n ∈ Stmt.definedVars (stmtResult σ s) ++
                Block.definedVars (blockResult (stmtPostState σ s) rest)
      exact List.mem_append_right _ h
    -- touchedVars (s :: rest result) = (mod-or-def s ++ mod-or-def rest)
    --                                  ++ (getVars s ++ getVars rest)
    have hn' : n ∈ (Stmt.modifiedOrDefinedVars (stmtResult σ s) ++
                    Block.modifiedOrDefinedVars (blockResult (stmtPostState σ s) rest)) ++
                   (Stmt.getVars (stmtResult σ s) ++
                    Block.getVars (blockResult (stmtPostState σ s) rest)) := hn
    rcases List.mem_append.mp hn' with hmd | hgv
    · rcases List.mem_append.mp hmd with hms | hmr
      · -- n ∈ mod-or-def stmtResult s → in touchedVars stmtResult s, recurse on s
        have hns_t : n ∈ Stmt.touchedVars (stmtResult σ s) := List.mem_append_left _ hms
        have ⟨ht_src, hd_src⟩ :=
          mem_touchedVars_stmtResult σ s (blockOk_cons_left hok) n hns_t hnd_s
        refine ⟨?_, ?_⟩
        · show n ∈ Block.modifiedOrDefinedVars (s :: rest) ++ Block.getVars (s :: rest)
          rcases List.mem_append.mp ht_src with hsmd | hsgv
          · apply List.mem_append_left
            show n ∈ Stmt.modifiedOrDefinedVars s ++ Block.modifiedOrDefinedVars rest
            exact List.mem_append_left _ hsmd
          · apply List.mem_append_right
            show n ∈ Stmt.getVars s ++ Block.getVars rest
            exact List.mem_append_left _ hsgv
        · intro h
          have h' : n ∈ Stmt.definedVars s ++ Block.definedVars rest := h
          rcases List.mem_append.mp h' with hds | hdr
          · exact hd_src hds
          · exact hnd_r (definedVars_subset_blockResult (stmtPostState σ s) rest
              (blockOk_cons_right hok) n hdr)
      · -- n ∈ mod-or-def of blockResult rest → recurse on rest
        have hnr_t : n ∈ Block.touchedVars (blockResult (stmtPostState σ s) rest) :=
          List.mem_append_left _ hmr
        have ⟨ht_src, hd_src⟩ :=
          mem_touchedVars_blockResult (stmtPostState σ s) rest
            (blockOk_cons_right hok) n hnr_t hnd_r
        refine ⟨?_, ?_⟩
        · show n ∈ Block.modifiedOrDefinedVars (s :: rest) ++ Block.getVars (s :: rest)
          rcases List.mem_append.mp ht_src with hrmd | hrgv
          · apply List.mem_append_left
            show n ∈ Stmt.modifiedOrDefinedVars s ++ Block.modifiedOrDefinedVars rest
            exact List.mem_append_right _ hrmd
          · apply List.mem_append_right
            show n ∈ Stmt.getVars s ++ Block.getVars rest
            exact List.mem_append_right _ hrgv
        · intro h
          have h' : n ∈ Stmt.definedVars s ++ Block.definedVars rest := h
          rcases List.mem_append.mp h' with hds | hdr
          · exact hnd_s (definedVars_subset_stmtResult σ s (blockOk_cons_left hok) n hds)
          · exact hd_src hdr
    · rcases List.mem_append.mp hgv with hgs | hgr
      · -- n ∈ getVars stmtResult s → in touchedVars
        have hns_t : n ∈ Stmt.touchedVars (stmtResult σ s) := List.mem_append_right _ hgs
        have ⟨ht_src, hd_src⟩ :=
          mem_touchedVars_stmtResult σ s (blockOk_cons_left hok) n hns_t hnd_s
        refine ⟨?_, ?_⟩
        · show n ∈ Block.modifiedOrDefinedVars (s :: rest) ++ Block.getVars (s :: rest)
          rcases List.mem_append.mp ht_src with hsmd | hsgv
          · apply List.mem_append_left
            show n ∈ Stmt.modifiedOrDefinedVars s ++ Block.modifiedOrDefinedVars rest
            exact List.mem_append_left _ hsmd
          · apply List.mem_append_right
            show n ∈ Stmt.getVars s ++ Block.getVars rest
            exact List.mem_append_left _ hsgv
        · intro h
          have h' : n ∈ Stmt.definedVars s ++ Block.definedVars rest := h
          rcases List.mem_append.mp h' with hds | hdr
          · exact hd_src hds
          · exact hnd_r (definedVars_subset_blockResult (stmtPostState σ s) rest
              (blockOk_cons_right hok) n hdr)
      · -- n ∈ getVars blockResult rest
        have hnr_t : n ∈ Block.touchedVars (blockResult (stmtPostState σ s) rest) :=
          List.mem_append_right _ hgr
        have ⟨ht_src, hd_src⟩ :=
          mem_touchedVars_blockResult (stmtPostState σ s) rest
            (blockOk_cons_right hok) n hnr_t hnd_r
        refine ⟨?_, ?_⟩
        · show n ∈ Block.modifiedOrDefinedVars (s :: rest) ++ Block.getVars (s :: rest)
          rcases List.mem_append.mp ht_src with hrmd | hrgv
          · apply List.mem_append_left
            show n ∈ Stmt.modifiedOrDefinedVars s ++ Block.modifiedOrDefinedVars rest
            exact List.mem_append_right _ hrmd
          · apply List.mem_append_right
            show n ∈ Stmt.getVars s ++ Block.getVars rest
            exact List.mem_append_right _ hrgv
        · intro h
          have h' : n ∈ Stmt.definedVars s ++ Block.definedVars rest := h
          rcases List.mem_append.mp h' with hds | hdr
          · exact hnd_s (definedVars_subset_stmtResult σ s (blockOk_cons_left hok) n hds)
          · exact hd_src hdr
end

theorem loopElim_overapproximatesAggressive
    (hwf_ext : WFEvalExtension φ) (σ : LoopElimState)
    (reserved : List String)
    (h_loop_reserved : loopElimReservedPrefix ∈ reserved) :
    Transform.OverapproximatesAggressively
      (LangCore π φ reserved)
      (LangCore π φ reserved)
      (fun s => open Classical in
                if Stmt.noFuncDecl s = Bool.true ∧ stmtOk σ s
                then some (stmtResult σ s) else none) := by
  intro st st' ht ρ₀ hwfb hwfv hwfvar hswf
  simp only at ht
  split at ht
  · rename_i hcond
    obtain ⟨hnofd, hok⟩ := hcond
    simp only [Option.some.injEq] at ht; subst ht
    -- Derive the OLD-style `(∀ n ∈ modifiedOrDefinedVars, isSome)` precondition
    -- needed by `simulation`/`canfail_simulation`.  This precondition is
    -- derivable from `InitEnvWF` only when `definedVars st = []` (no top-level
    -- inits in the source); otherwise `defsUndefined` says `isNone` directly
    -- contradicting the simulation precondition.
    -- The deeper resolution requires refactoring `simulation`/`canfail_simulation`
    -- to take `InitEnvWF` directly; for now, we residualize the gap to a single
    -- targeted sorry below.
    have hswf_mod_isSome : ∀ n ∈ Stmt.modifiedOrDefinedVars st, (ρ₀.store n).isSome := by
      intro n hn
      by_cases hd : n ∈ Stmt.definedVars st
      · -- Fundamental gap: defsUndefined says isNone, simulation needs isSome.
        sorry
      · have htouched : n ∈ Stmt.touchedVars st := by
          show n ∈ Stmt.modifiedOrDefinedVars st ++ Stmt.getVars st
          exact List.mem_append_left _ hn
        exact hswf.readWritesDefined n htouched hd
    have hsim := (simulation π φ hwf_ext (Stmt.sizeOf st)).1
      σ st (Nat.le_refl _) hnofd hok ρ₀ hwfb hwfv hwfvar hswf.evalCong hswf_mod_isSome
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro ρ' hstar; exact hsim.1 ρ' hstar
    · intro lbl ρ' hstar; exact hsim.2 lbl ρ' hstar
    · intro ⟨cfg, hfail, hreach⟩
      by_cases hnf₀ : ρ₀.hasFailure = Bool.true
      · exact ⟨.stmt (stmtResult σ st) ρ₀, by show ρ₀.hasFailure = Bool.true; exact hnf₀, .refl _⟩
      · exact (canfail_simulation π φ hwf_ext (Stmt.sizeOf st)).1
          σ st (Nat.le_refl _) hok hnofd ρ₀ hwfb hwfv hwfvar hswf.evalCong hswf_mod_isSome ⟨cfg, hfail, hreach⟩
    · -- Show `InitEnvWF reserved (stmtResult σ st) ρ₀` from `InitEnvWF reserved st ρ₀`.
      -- The transform's fresh `$__loop_measure_N` names start with the reserved
      -- prefix `$__loop`; `hswf.reservedFresh` rules them out of `ρ₀.store`.
      refine
        { readWritesDefined := ?_,
          defsUndefined := ?_,
          reservedFresh := hswf.reservedFresh,
          evalCong := hswf.evalCong,
          exprCongr := hswf.exprCongr }
      · intro n hn hnd
        have ⟨hn_src, hnd_src⟩ := mem_touchedVars_stmtResult σ st hok n hn hnd
        exact hswf.readWritesDefined n hn_src hnd_src
      · intro n hn
        rcases mem_definedVars_stmtResult σ st hok n hn with hold | hpref
        · exact hswf.defsUndefined n hold
        · -- n.name has reserved prefix; reservedFresh's contrapositive gives isNone.
          rw [Option.isNone_iff_eq_none]
          cases h : ρ₀.store n with
          | none => rfl
          | some v =>
            exfalso
            have hsome : (ρ₀.store n).isSome := by rw [h]; rfl
            exact hswf.reservedFresh n hsome loopElimReservedPrefix h_loop_reserved hpref
  · exact absurd ht (by nofun)

end Core.LoopElim

end -- public section
