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

abbrev LangCore :=
  Core.Specification.Lang.core π φ
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

/-- Taking the false/else branch of a det-ite with empty else-block terminates at the
    same env (after scoped-ite projection, which is identity on self). -/
private theorem ite_det_false_empty_terminal
    (g : Expression.Expr) (then_branch : Statements) (md : MetaData Expression)
    (ρ₀ : Env Expression)
    (hg_ff : ρ₀.eval ρ₀.store g = some HasBool.ff)
    (hwfb : WellFormedSemanticEvalBool ρ₀.eval) :
    CoreStar π φ (.stmt (.ite (.det g) then_branch [] md) ρ₀) (.terminal ρ₀) := by
  have h_inner : CoreStar π φ (.stmts ([] : Statements) ρ₀) (.terminal ρ₀) :=
    .step _ _ _ .step_stmts_nil (.refl _)
  have h_block : CoreStar π φ
      (.block .none ρ₀.store (.stmts ([] : Statements) ρ₀))
      (.terminal { ρ₀ with store := projectStore ρ₀.store ρ₀.store }) :=
    ReflTrans_Transitive _ _ _ _
      (block_inner_star Expression (EvalCommand π φ) (EvalPureFunc φ)
        _ _ .none ρ₀.store h_inner)
      (.step _ _ _ .step_block_done (.refl _))
  rw [projectStore_self_env] at h_block
  exact .step _ _ _ (.step_ite_false hg_ff hwfb) h_block

/-- Taking the false/else branch of a nondet-ite with empty else-block terminates at the
    same env (after scoped-ite projection, which is identity on self). -/
private theorem ite_nondet_false_empty_terminal
    (then_branch : Statements) (md : MetaData Expression)
    (ρ₀ : Env Expression) :
    CoreStar π φ (.stmt (.ite .nondet then_branch [] md) ρ₀) (.terminal ρ₀) := by
  have h_inner : CoreStar π φ (.stmts ([] : Statements) ρ₀) (.terminal ρ₀) :=
    .step _ _ _ .step_stmts_nil (.refl _)
  have h_block : CoreStar π φ
      (.block .none ρ₀.store (.stmts ([] : Statements) ρ₀))
      (.terminal { ρ₀ with store := projectStore ρ₀.store ρ₀.store }) :=
    ReflTrans_Transitive _ _ _ _
      (block_inner_star Expression (EvalCommand π φ) (EvalPureFunc φ)
        _ _ .none ρ₀.store h_inner)
      (.step _ _ _ .step_block_done (.refl _))
  rw [projectStore_self_env] at h_block
  exact .step _ _ _ .step_ite_nondet_false h_block

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
    simp only [stmtRun, StateT.run, ExceptT.run, Stmt.removeLoopsM, removeLoopsLoopCase, buildLoopOutput, buildLoopPassive, buildArbitraryIterFacts, buildArbitraryIterAssumes, buildExitStateAssumes, buildHavocBlock, buildFirstIterFacts, buildEntryInvariants, buildEntryInvariantAssumes, buildInvAssumes, buildMaintainInvariants, buildExitInvariantAssumes, buildGuardParts, buildTerminationStmtsSome, hasLabelConflict, numAssertAssumesForLoop, invSuffix, measureOldIdent,
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
    simp only [stmtRun, StateT.run, ExceptT.run, Stmt.removeLoopsM, removeLoopsLoopCase, buildLoopOutput, buildLoopPassive, buildArbitraryIterFacts, buildArbitraryIterAssumes, buildExitStateAssumes, buildHavocBlock, buildFirstIterFacts, buildEntryInvariants, buildEntryInvariantAssumes, buildInvAssumes, buildMaintainInvariants, buildExitInvariantAssumes, buildGuardParts, buildTerminationStmtsSome, hasLabelConflict, numAssertAssumesForLoop, invSuffix, measureOldIdent,
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

private theorem block_definedVars_append (ss₁ ss₂ : Statements) (ex : Bool) :
    Block.definedVars (ss₁ ++ ss₂) ex = Block.definedVars ss₁ ex ++ Block.definedVars ss₂ ex := by
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

/-! ### EvalCmd store frame -/

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
    (hdef : x ∉ Stmt.definedVars (Stmt.cmd c) false) :
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
      simp [Stmt.definedVars, HasVarsImp.definedVars, Command.definedVars, Cmd.definedVars]
      exact heq.symm
    | eval_init_unconstrained hinit _ =>
      apply initState_store_frame hinit
      intro heq; apply hdef
      simp [Stmt.definedVars, HasVarsImp.definedVars, Command.definedVars, Cmd.definedVars]
      exact heq.symm
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
  | .stmt s _ => Stmt.modifiedVars s ++ Stmt.definedVars s false
  | .stmts ss _ => Block.modifiedVars ss ++ Block.definedVars ss false
  | .terminal _ => []
  | .exiting _ _ => []
  | .block _ _ inner => Config.touchedVarsSet inner
  | .seq inner ss => Config.touchedVarsSet inner ++ Block.modifiedVars ss ++ Block.definedVars ss false

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
  | step_ite_true _ _ => exact ⟨hinv, hinv⟩
  | step_ite_false _ _ => exact ⟨hinv, hinv⟩
  | step_ite_nondet_true => exact ⟨hinv, hinv⟩
  | step_ite_nondet_false => exact ⟨hinv, hinv⟩
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
    trace-reachability invariant for `stmt_star_preserves_reservedFresh`. -/

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
    ∀ x, x ∈ Imperative.HasVarsImp.definedVars c false → x ∈ Stmt.definedVars s false := by
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
    ∀ x, x ∈ Imperative.HasVarsImp.definedVars c false → x ∈ Block.definedVars ss false := by
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
private theorem definedVars_subset_modifiedOrDefinedVars (sz : Nat) (ex : Bool) :
    (∀ (s : Stmt Expression Command), Stmt.sizeOf s ≤ sz →
      ∀ x, x ∈ Stmt.definedVars s ex → x ∈ Stmt.modifiedOrDefinedVars s ex) ∧
    (∀ (ss : Statements), Block.sizeOf ss ≤ sz →
      ∀ x, x ∈ Block.definedVars ss ex → x ∈ Block.modifiedOrDefinedVars ss ex) := by
  exact ⟨fun _ _ x hx => by simp only [Stmt.modifiedOrDefinedVars, List.mem_append]; exact Or.inr hx,
         fun _ _ x hx => by simp only [Block.modifiedOrDefinedVars, List.mem_append]; exact Or.inr hx⟩

/-! ### "No new variables" helpers for `stmt_star_preserves_reservedFresh` -/

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
    (hdef_old : ∀ y ∈ Imperative.HasVarsImp.definedVars c false, (ρ.store y).isSome)
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
    (hdef_safe : ∀ c ∈ Config.cmdsIn a, ∀ y ∈ Imperative.HasVarsImp.definedVars c false,
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
    have hdef_local : ∀ y ∈ Imperative.HasVarsImp.definedVars cmd false,
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
    (hdef_safe : ∀ c ∈ Config.cmdsIn a, ∀ y ∈ Imperative.HasVarsImp.definedVars c false,
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

/-- Preservation of an arbitrary "fresh-name" predicate across a single-statement
    trace `.stmt s ρ₀ →* .terminal ρ₁`.  If every var that `s` *defines* (via init
    or funcDecl) is already isSome in `ρ₀`, then no fresh names appear at `ρ₁`, so
    any predicate that holds for all currently-defined names at `ρ₀` continues to
    hold at `ρ₁`.

    Stated generically over a predicate `P` (e.g., "name doesn't have a reserved
    prefix") so this can be used at multiple call sites.  The
    `Stmt.definedVars s ⊆ ρ₀ isSome` precondition is precisely what's needed
    to keep init/funcDecl from firing.  This is a derived form of the
    simulation-level hypothesis (`Stmt.modifiedOrDefinedVars s ⊆ ρ₀ isSome`),
    which is genuinely strong and tied to the architectural-gap pre-`InitEnvWF`
    interface still threaded through `simulation`/`canfail_simulation`. -/
private theorem stmt_star_preserves_reservedFresh
    (s : Stmt Expression Command) (ρ₀ ρ₁ : Env Expression)
    (hstar : CoreStar π φ (.stmt s ρ₀) (.terminal ρ₁))
    (hswf_def : ∀ n ∈ Stmt.definedVars s false, (ρ₀.store n).isSome)
    {P : Expression.Ident → Prop}
    (hreserved : ∀ n, (ρ₀.store n).isSome → P n) :
    ∀ n, (ρ₁.store n).isSome → P n := by
  intro n hn
  apply hreserved n
  -- Reduce to `(ρ₀.store n).isSome` via star_no_new_vars.
  have hinv₀ : outerInv ρ₀.store (.stmt s ρ₀) := fun _ h => h
  have hdef_safe : ∀ c ∈ Config.cmdsIn (Config.stmt s ρ₀),
      ∀ y ∈ Imperative.HasVarsImp.definedVars c false, (ρ₀.store y).isSome := by
    intro c hc y hy
    apply hswf_def
    simp only [Config.cmdsIn] at hc
    exact Stmt.definedVars_of_commandIn s c hc y hy
  have := star_no_new_vars (π := π) (φ := φ) hstar hinv₀ hdef_safe (n := n)
  simp only [Config.getEnv] at this
  exact this hn

/-- `Block.noFuncDecl (body ++ [loop body]) = true` when `Block.noFuncDecl body = true`. -/
private theorem mem_Block_modifiedOrDefinedVars_append {ss₁ ss₂ : Statements} {ex : Bool}
    {n : Expression.Ident}
    (hmem : n ∈ Block.modifiedOrDefinedVars (ss₁ ++ ss₂) ex) :
    n ∈ Block.modifiedOrDefinedVars ss₁ ex ∨ n ∈ Block.modifiedOrDefinedVars ss₂ ex := by
  simp only [Block.modifiedOrDefinedVars, List.mem_append] at hmem ⊢
  rw [block_modifiedVars_append] at hmem
  rw [block_definedVars_append ss₁ ss₂ ex] at hmem
  simp only [List.mem_append] at hmem
  rcases hmem with (h | h) | (h | h)
  · exact Or.inl (Or.inl h)
  · exact Or.inr (Or.inl h)
  · exact Or.inl (Or.inr h)
  · exact Or.inr (Or.inr h)

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
    have hdef : x ∉ Stmt.definedVars (Stmt.cmd ‹Command›) false :=
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
    simp only [Config.touchedVarsSet, Stmt.modifiedVars, Stmt.definedVars,
      Bool.false_eq_true, ↓reduceIte] at hx ⊢
    exact hx
  | step_ite_true _ _ =>
    simp only [Config.touchedVarsSet, Stmt.modifiedVars, Stmt.definedVars,
      Bool.false_eq_true, ↓reduceIte, List.mem_append] at hx ⊢
    rcases hx with h | h
    · left; left; exact h
    · right; left; exact h
  | step_ite_false _ _ =>
    simp only [Config.touchedVarsSet, Stmt.modifiedVars, Stmt.definedVars,
      Bool.false_eq_true, ↓reduceIte, List.mem_append] at hx ⊢
    rcases hx with h | h
    · left; right; exact h
    · right; right; exact h
  | step_ite_nondet_true =>
    simp only [Config.touchedVarsSet, Stmt.modifiedVars, Stmt.definedVars,
      Bool.false_eq_true, ↓reduceIte, List.mem_append] at hx ⊢
    rcases hx with h | h
    · left; left; exact h
    · right; left; exact h
  | step_ite_nondet_false =>
    simp only [Config.touchedVarsSet, Stmt.modifiedVars, Stmt.definedVars,
      Bool.false_eq_true, ↓reduceIte, List.mem_append] at hx ⊢
    rcases hx with h | h
    · left; right; exact h
    · right; right; exact h
  | step_loop_enter _ _ _ _ _ =>
    simp only [Config.touchedVarsSet, Stmt.modifiedVars, Stmt.definedVars,
               Bool.false_eq_true, ↓reduceIte, Block.modifiedVars, Block.definedVars,
               List.append_nil, List.mem_append] at hx ⊢
    rcases hx with ((h | h) | h) | h
    · exact .inl h
    · exact .inr h
    · exact .inl h
    · exact .inr h
  | step_loop_exit _ _ _ _ => simp [Config.touchedVarsSet] at hx
  | step_loop_nondet_enter _ _ =>
    simp only [Config.touchedVarsSet, Stmt.modifiedVars, Stmt.definedVars,
               Bool.false_eq_true, ↓reduceIte, Block.modifiedVars, Block.definedVars,
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

/-! ### Multi-step store preservation (isNone-preservation, no outerInv needed)

For the `BlockInitEnvWF.toBlock_tail_post` derivation we need to argue that
variables that are `isNone` at `ρ₀` and outside `touchedVarsSet` of the trace
remain `isNone` at `ρ₁`.  This is *one-directional* and doesn't require any
`outerInv` hypothesis (block-exit's `projectStore` produces `none` for both
input branches when the var is `isNone`). -/

/-- Single-step store frame for variables that are `isNone` at `c₁` and outside
    `c₁`'s touched vars: the store at `x` stays the same after a single step. -/
private theorem step_preserves_store_outside_touchedVars_isNone
    {c₁ c₂ : CC}
    (hstep : StepStmt Expression (EvalCommand π φ) (EvalPureFunc φ) c₁ c₂)
    (x : Expression.Ident)
    (hnone : (c₁.getEnv.store x).isNone)
    (hx : x ∉ Config.touchedVarsSet c₁) :
    c₂.getEnv.store x = c₁.getEnv.store x := by
  induction hstep with
  | step_cmd heval =>
    have hmod : x ∉ Stmt.modifiedVars (Stmt.cmd ‹Command›) :=
      fun hmem => hx (show x ∈ Config.touchedVarsSet _ by
        simp only [Config.touchedVarsSet]; exact List.mem_append_left _ hmem)
    have hdef : x ∉ Stmt.definedVars (Stmt.cmd ‹Command›) false :=
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
    exact ih hnone (fun hmem => hx (by
      simp only [Config.touchedVarsSet, List.mem_append]
      left; left; exact hmem))
  | step_seq_done => rfl
  | step_seq_exit => rfl
  | step_block_body _ ih =>
    simp only [Config.getEnv, Config.touchedVarsSet] at hnone hx ⊢
    exact ih hnone hx
  | step_block_done =>
    -- c₁ = .block l σ_parent (.terminal ρ'), c₁.store x = ρ'.store x.
    -- c₂.store x = projectStore σ_parent ρ'.store x.  Since (ρ'.store x).isNone
    -- (= hnone), both branches of projectStore give `none`.
    simp only [Config.getEnv] at hnone ⊢
    simp only [projectStore]
    have hρ'_none : ‹Env Expression›.store x = none :=
      Option.isNone_iff_eq_none.mp hnone
    rw [hρ'_none]; split <;> rfl
  | step_block_exit_match _ =>
    simp only [Config.getEnv] at hnone ⊢
    simp only [projectStore]
    have hρ'_none : ‹Env Expression›.store x = none :=
      Option.isNone_iff_eq_none.mp hnone
    rw [hρ'_none]; split <;> rfl
  | step_block_exit_mismatch _ =>
    simp only [Config.getEnv] at hnone ⊢
    simp only [projectStore]
    have hρ'_none : ‹Env Expression›.store x = none :=
      Option.isNone_iff_eq_none.mp hnone
    rw [hρ'_none]; split <;> rfl

/-- Star version of `step_preserves_store_outside_touchedVars_isNone`. -/
private theorem star_preserves_store_outside_touchedVars_isNone
    {c₁ c₂ : CC}
    (hstar : CoreStar π φ c₁ c₂)
    (x : Expression.Ident)
    (hnone : (c₁.getEnv.store x).isNone)
    (hx : x ∉ Config.touchedVarsSet c₁) :
    c₂.getEnv.store x = c₁.getEnv.store x := by
  induction hstar with
  | refl => rfl
  | step _ mid _ hstep _ ih =>
    have hx_mid : x ∉ Config.touchedVarsSet mid :=
      fun hmem => hx (step_touchedVars_subset π φ _ _ hstep x hmem)
    have hframe := step_preserves_store_outside_touchedVars_isNone
      (π := π) (φ := φ) hstep x hnone hx
    have hnone_mid : (mid.getEnv.store x).isNone := by
      rw [hframe]; exact hnone
    rw [ih hnone_mid hx_mid, hframe]

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
    (reserved : List String)
    (g : Expression.Expr) (measure : Option Expression.Expr)
    (inv : List (String × Expression.Expr))
    (body : Statements) (md : MetaData Expression)
    (ρ₀ ρ' : Env Expression)
    (hguard_tt : ρ₀.eval ρ₀.store g = some HasBool.tt)
    (hall_tt : ∀ le ∈ inv, ρ₀.eval ρ₀.store le.2 = some HasBool.tt)
    (hnofd : Block.noFuncDecl body = Bool.true)
    (hswf : BlockInitEnvWF reserved body ρ₀)
    (hnf : ρ'.hasFailure = Bool.false)
    (hloop : CoreStar π φ (.stmt (.loop (.det g) measure inv body md) ρ₀) (.terminal ρ')) :
    -- Success: last iteration body terminates at ρ_body_exit, all invs tt at ρ',
    -- and ρ' is the projection of ρ_body_exit through ρ_last.store.
    ∃ ρ_last ρ_body_exit,
      ρ_last.eval ρ_last.store g = some HasBool.tt ∧
      (∀ le ∈ inv, ρ_last.eval ρ_last.store le.2 = some HasBool.tt) ∧
      ρ_last.hasFailure = Bool.false ∧
      CoreStar π φ (.stmts body ρ_last) (.terminal ρ_body_exit) ∧
      ρ'.eval = ρ_body_exit.eval ∧
      ρ'.hasFailure = ρ_body_exit.hasFailure ∧
      ρ'.store = projectStore ρ_last.store ρ_body_exit.store ∧
      (∀ le ∈ inv, ρ'.eval ρ'.store le.2 = some HasBool.tt) ∧
      ρ'.eval ρ'.store g = some HasBool.ff ∧
      BlockInitEnvWF reserved body ρ_last ∧
      (∀ x, x ∉ Block.modifiedVars body → x ∉ Block.definedVars body false → ρ_last.store x = ρ₀.store x) ∧
      ρ_last.eval = ρ₀.eval ∧
      (∀ me, measure = .some me →
        ρ_last.eval ρ_last.store (HasIntOrder.lt me HasIntOrder.zero) = .some HasBool.ff) := by
  -- Convert to ReflTransT and use strong induction on trace length, generalized over ρ₀ and measure.
  have hloopT := reflTrans_to_T hloop
  suffices ∀ (n : Nat) (ρ₀ : Env Expression) (measure : Option Expression.Expr),
      ρ₀.eval ρ₀.store g = some HasBool.tt →
      (∀ le ∈ inv, ρ₀.eval ρ₀.store le.2 = some HasBool.tt) →
      BlockInitEnvWF reserved body ρ₀ →
      ∀ (hstarT : ReflTransT (StepStmt Expression (EvalCommand π φ) (EvalPureFunc φ))
          (.stmt (.loop (.det g) measure inv body md) ρ₀) (.terminal ρ')),
        hstarT.len ≤ n →
      ∃ ρ_last ρ_body_exit,
        ρ_last.eval ρ_last.store g = some HasBool.tt ∧
        (∀ le ∈ inv, ρ_last.eval ρ_last.store le.2 = some HasBool.tt) ∧
        ρ_last.hasFailure = Bool.false ∧
        CoreStar π φ (.stmts body ρ_last) (.terminal ρ_body_exit) ∧
        ρ'.eval = ρ_body_exit.eval ∧
        ρ'.hasFailure = ρ_body_exit.hasFailure ∧
        ρ'.store = projectStore ρ_last.store ρ_body_exit.store ∧
        (∀ le ∈ inv, ρ'.eval ρ'.store le.2 = some HasBool.tt) ∧
        ρ'.eval ρ'.store g = some HasBool.ff ∧
        BlockInitEnvWF reserved body ρ_last ∧
        (∀ x, x ∉ Block.modifiedVars body → x ∉ Block.definedVars body false →
              ρ_last.store x = ρ₀.store x) ∧
        ρ_last.eval = ρ₀.eval ∧
        (∀ me, measure = .some me →
          ρ_last.eval ρ_last.store (HasIntOrder.lt me HasIntOrder.zero) = .some HasBool.ff) by
    exact this hloopT.len ρ₀ measure hguard_tt hall_tt hswf hloopT (Nat.le_refl _)
  intro n
  induction n with
  | zero =>
    intro ρ₀ measure _ _ _ hstarT hlen
    -- Trace must take at least one step (LHS is .stmt loop, RHS is .terminal),
    -- so hstarT.len ≥ 1, contradiction with hlen ≤ 0.
    match hstarT, hlen with
    | .step _ _ _ _ _, hlen => simp [ReflTransT.len] at hlen
  | succ n ih =>
    intro ρ₀ measure hguard_tt₀ hall_tt₀ hswf₀ hstarT hlen
    -- Extract WF eval fields from hswf₀ for repeated reuse.
    have hwfb₀ := hswf₀.wfBool
    have hwfv₀ := hswf₀.wfVal
    have hwfvar₀ := hswf₀.wfVar
    have hwfc₀ := hswf₀.evalCong
    have hwfecong₀ := hswf₀.exprCongr
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
      have hrest_prop := reflTransT_to_prop hrest
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
      -- Under BlockInitEnvWF, the body's exit env ρ_inner has fresh inits projected away
      -- when crossing the block boundary: ρ₁ = { ρ_inner with store := projectStore ρ₀.store ρ_inner.store }.
      have hρ₁_eq' :
          ρ₁ = { ρ_inner with store := projectStore ρ₀.store ρ_inner.store } := hρ₁_eq
      -- Now decompose the tail: .stmts [loop] ρ₁ →T .terminal ρ'.
      obtain ⟨ρ_loop_term, h_loop_raw, h_nil, hlen_tail⟩ :=
        stmtsT_cons_terminal (extendEval := EvalPureFunc φ) h_tail
      have hρlt : ρ' = ρ_loop_term := by
        match h_nil with
        | .step _ _ _ .step_stmts_nil hrest_nil =>
          match hrest_nil with
          | .refl _ => rfl
      subst hρlt
      -- Now h_loop_raw : .stmt loop ρ₁ →T .terminal ρ' directly.
      let h_loop := h_loop_raw
      -- The body did not change the eval, so ρ_inner.eval = ρ₀.eval.
      have heval_inner : ρ_inner.eval = ρ₀.eval :=
        smallStep_noFuncDecl_preserves_eval_block Expression
          (EvalCommand π φ) (EvalPureFunc φ) body ρ₀ ρ_inner hnofd hbody
      -- ρ₁.eval = ρ_inner.eval (only store changes via projection).
      have heval_ρ₁ : ρ₁.eval = ρ_inner.eval := by rw [hρ₁_eq']
      have heval_ρ₁_eq : ρ₁.eval = ρ₀.eval := heval_ρ₁.trans heval_inner
      -- WF properties at ρ₁.
      have hwfb₁ : WellFormedSemanticEvalBool ρ₁.eval := heval_ρ₁_eq ▸ hwfb₀
      have hwfv₁ : WellFormedSemanticEvalVal ρ₁.eval := heval_ρ₁_eq ▸ hwfv₀
      have hwfvar₁ : WellFormedSemanticEvalVar ρ₁.eval := heval_ρ₁_eq ▸ hwfvar₀
      have hwfc₁ : WellFormedCoreEvalCong ρ₁.eval := heval_ρ₁_eq ▸ hwfc₀
      have hwfecong₁ : WellFormedSemanticEvalExprCongr ρ₁.eval := heval_ρ₁_eq ▸ hwfecong₀
      -- hasFailure at ρ₁ is false (backwards from ρ').
      have hnf_ρ₁ : ρ₁.hasFailure = Bool.false := by
        have hloop_prop : CoreStar π φ (.stmt (.loop (.det g) measure inv body md) ρ₁)
            (.terminal ρ') := reflTransT_to_prop h_loop
        exact hasFailure_false_backwards (π := π) (φ := φ) hloop_prop hnf
      -- Bridge for store agreement: ρ_inner.store x = ρ₀.store x when x is outside body's
      -- touched vars and (ρ₀.store x).isSome.  The full statement uses projectStore.
      have hstore_bridge_inner : ∀ x, x ∉ Block.modifiedVars body → x ∉ Block.definedVars body false →
          (ρ₀.store x).isSome → ρ_inner.store x = ρ₀.store x := by
        intro x hmod hdef hsome
        have hinv₀ : outerInv ρ₀.store (.stmts body ρ₀) := fun _ h => h
        have hxnot : x ∉ Config.touchedVarsSet (.stmts body ρ₀) := by
          simp only [Config.touchedVarsSet, List.mem_append]
          exact fun h => h.elim hmod hdef
        have h := star_preserves_store_outside_touchedVars_outerInv
          (π := π) (φ := φ) ρ₀.store _ _ hbody hinv₀ x hsome hxnot
        simpa [Config.getEnv] using h
      -- Bridge: ρ₁.store x = ρ₀.store x when x is outside body's touched vars.
      have hstore_bridge : ∀ x, x ∉ Block.modifiedVars body → x ∉ Block.definedVars body false →
          ρ₁.store x = ρ₀.store x := by
        intro x hmod hdef
        rw [hρ₁_eq']
        show projectStore ρ₀.store ρ_inner.store x = ρ₀.store x
        simp only [projectStore]
        by_cases hsome : (ρ₀.store x).isSome
        · rw [if_pos hsome]; exact hstore_bridge_inner x hmod hdef hsome
        · rw [if_neg hsome]
          exact (Option.not_isSome_iff_eq_none.mp hsome).symm
      -- BlockInitEnvWF at ρ₁: preserved across an iteration.
      have hswf_ρ₁ : BlockInitEnvWF reserved body ρ₁ := by
        refine
          { readWritesDefined := ?_, defsUndefined := ?_,
            definedVarsNotReserved := hswf₀.definedVarsNotReserved,
            reservedFresh := ?_,
            wfBool := hwfb₁, wfVal := hwfv₁, wfVar := hwfvar₁,
            evalCong := hwfc₁, exprCongr := hwfecong₁,
            defUseOk := ?_ }
        · -- readWritesDefined: vars in touched\defined are isSome in ρ₁.store
          intro x hxt hxnd
          rw [hρ₁_eq']
          show (projectStore ρ₀.store ρ_inner.store x).isSome
          simp only [projectStore]
          have hsome₀ : (ρ₀.store x).isSome :=
            hswf₀.readWritesDefined x hxt hxnd
          rw [if_pos hsome₀]
          -- ρ_inner.store x is isSome by outerInv preservation.
          have := stmts_star_preserves_isSome (π := π) (φ := φ) body ρ₀ _ hbody x hsome₀
          simpa [Config.getEnv] using this
        · -- defsUndefined: vars in definedVars body are isNone in ρ₁.store
          intro x hxd
          rw [hρ₁_eq']
          show (projectStore ρ₀.store ρ_inner.store x).isNone
          simp only [projectStore]
          have hnone₀ : (ρ₀.store x).isNone := hswf₀.defsUndefined x hxd
          rw [if_neg (by rw [Option.isNone_iff_eq_none.mp hnone₀]; simp)]
          rfl
        · -- reservedFresh: any name isSome in ρ₁ has no reserved prefix.
          intro x hxsome p hp
          have hxsome' : (ρ₁.store x).isSome := hxsome
          rw [hρ₁_eq'] at hxsome'
          show ¬ p.toList.isPrefixOf x.name.toList
          -- ρ₁.store x = projectStore ρ₀.store ρ_inner.store x, isSome means (ρ₀.store x).isSome
          have hρ₀_some : (ρ₀.store x).isSome := by
            simp only [projectStore] at hxsome'
            split at hxsome'
            · assumption
            · simp at hxsome'
          exact hswf₀.reservedFresh x hρ₀_some p hp
        · -- defUseOk: ρ₁ has the same isSome-domain as ρ₀ (projectStore mask).
          have heq_pred : (fun n => (ρ₁.store n).isSome) = (fun n => (ρ₀.store n).isSome) := by
            funext itm
            simp only [hρ₁_eq', projectStore]
            split
            · next hsome₀ =>
              have := stmts_star_preserves_isSome (π := π) (φ := φ) body ρ₀ _ hbody itm hsome₀
              simp [Config.getEnv] at this
              simp [this, hsome₀]
            · next hns =>
              simp [Bool.eq_false_iff.mpr hns]
          rw [heq_pred]
          exact hswf₀.defUseOk
      -- Length bound for h_loop relative to n.
      have hrest_len : hrest.len ≤ n := by
        have hh : 1 + hrest.len ≤ n + 1 := hlen
        omega
      have hloop_len : h_loop.len ≤ n := by
        have h1 : h_loop_raw.len ≤ h_tail.len := by
          have : h_loop_raw.len + h_nil.len + 2 ≤ h_tail.len := hlen_tail
          omega
        have h2 : h_tail.len ≤ hrest.len := by
          have : h_block.len + h_tail.len < hrest.len := hlen_seq
          omega
        show h_loop_raw.len ≤ n
        omega
      -- Case split on the loop trace's first step at ρ₁.
      match h_loop, hloop_len with
      | .step _ _ _ (@StepStmt.step_loop_exit _ _ _ _ _ _ _ _ _ _ _ _ _
          hasInvFailure₁ hg_ff₁ hinv_bool₁ hff_iff₁ _) hrest₁, _ =>
        -- Last iteration: guard is ff at ρ₁.
        have hρ'_eq_raw :
            ρ' = { ρ₁ with hasFailure := ρ₁.hasFailure || hasInvFailure₁ } := by
          match hrest₁ with
          | .refl _ => rfl
          | .step _ _ _ h _ => cases h
        have hnf_or₁ : (ρ₁.hasFailure || hasInvFailure₁) = Bool.false := by
          have hh : ρ'.hasFailure = (ρ₁.hasFailure || hasInvFailure₁) := by
            rw [hρ'_eq_raw]
          rw [← hh]; exact hnf
        have hnif₁ : hasInvFailure₁ = Bool.false :=
          loop_step_hasInvFailure_false_of_or hnf_or₁
        have hall_tt₁ := all_inv_tt_of_hasInvFailure_false hinv_bool₁ hff_iff₁ hnif₁
        subst hnif₁
        have hρ'_eq : ρ' = ρ₁ := by
          rw [hρ'_eq_raw]; cases ρ₁; simp [Bool.or_false]
        -- ρ_last := ρ₀, ρ_body_exit := ρ_inner.
        refine ⟨ρ₀, ρ_inner, hguard_tt₀, hall_tt₀, hnf₀, hbody, ?_, ?_, ?_, ?_, ?_,
          hswf₀, fun _ _ _ => rfl, rfl, ?_⟩
        · -- ρ'.eval = ρ_body_exit.eval (= ρ_inner.eval).
          rw [hρ'_eq, hρ₁_eq']
        · -- ρ'.hasFailure = ρ_body_exit.hasFailure
          rw [hρ'_eq, hρ₁_eq']
        · -- ρ'.store = projectStore ρ_last.store ρ_body_exit.store
          rw [hρ'_eq, hρ₁_eq']
        · -- All invariants tt at ρ'.
          intro le hle
          rw [hρ'_eq]; exact hall_tt₁ le hle
        · -- guard is ff at ρ'.
          rw [hρ'_eq]; exact hg_ff₁
        · -- Measure conjunct.
          intro me hme
          exact (hmeas_lb₀ me me hme).2
      | .step _ _ _ (@StepStmt.step_loop_enter _ _ _ _ _ _ _ _ _ _ _ _ _
          hasInvFailure₁ hg_tt₁ hinv_bool₁ hff_iff₁ _ _) hrest₁, hloop_len =>
        -- Recursive case: more iterations needed.
        let hloop_full : ReflTransT (StepStmt Expression (EvalCommand π φ) (EvalPureFunc φ))
            (.stmt (.loop (.det g) measure inv body md) ρ₁) (.terminal ρ') :=
          .step _ _ _ (.step_loop_enter hg_tt₁ hinv_bool₁ hff_iff₁ ‹_› ‹_›) hrest₁
        have hloop_full_len : hloop_full.len ≤ n := by
          show 1 + hrest₁.len ≤ n
          have : (1 + hrest₁.len) ≤ n := hloop_len
          omega
        have hnf_start₁ : (ρ₁.hasFailure || hasInvFailure₁) = Bool.false := by
          have hh := hasFailure_false_backwards (π := π) (φ := φ)
            (reflTransT_to_prop hrest₁) hnf
          simpa [Config.getEnv] using hh
        have hnif₁ : hasInvFailure₁ = Bool.false :=
          loop_step_hasInvFailure_false_of_or hnf_start₁
        have hall_tt₁ := all_inv_tt_of_hasInvFailure_false hinv_bool₁ hff_iff₁ hnif₁
        -- Apply IH at ρ₁.
        have ih_result := ih ρ₁ measure hg_tt₁ hall_tt₁ hswf_ρ₁ hloop_full hloop_full_len
        obtain ⟨ρ_last, ρ_body_exit, h1, h2, h3, h4_body, h5_eval, h5_fail, h5_store,
          h6inv, h6g, h7swf, h8store, h9eval, h10meas⟩ := ih_result
        -- Compose: store agreement: ρ_last.store x = ρ₁.store x = ρ₀.store x outside body's vars.
        refine ⟨ρ_last, ρ_body_exit, h1, h2, h3, h4_body, h5_eval, h5_fail, h5_store,
          h6inv, h6g, h7swf,
          fun x hmod hdef => (h8store x hmod hdef).trans (hstore_bridge x hmod hdef),
          h9eval.trans heval_ρ₁_eq, h10meas⟩

/-! ## TouchedVars subset lemmas -/

/-- `Block.modifiedOrDefinedVars ss ⊆ Block.definedVars ss ++ Block.modifiedVars ss`. -/
private theorem modifiedVars_subset_modifiedOrDefinedVars (sz : Nat) :
    (∀ (s : Statement), Stmt.sizeOf s ≤ sz →
      ∀ n, n ∈ Stmt.modifiedVars s → n ∈ Stmt.modifiedOrDefinedVars s false) ∧
    (∀ (ss : Statements), Block.sizeOf ss ≤ sz →
      ∀ n, n ∈ Block.modifiedVars ss → n ∈ Block.modifiedOrDefinedVars ss false) := by
  exact ⟨fun _ _ n hn => by simp only [Stmt.modifiedOrDefinedVars, List.mem_append]; exact Or.inl hn,
         fun _ _ n hn => by simp only [Block.modifiedOrDefinedVars, List.mem_append]; exact Or.inl hn⟩

/-- The prefix_stmts from the loop transformation terminate at ρ₀ when
    guard+invs are tt and all body-touched vars are defined.
    Returns the same structural decomposition as `stmtResult_loop_then_branch_struct`
    plus a prefix termination proof. -/
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
    (reserved : List String)
    (g : Expression.Expr)
    (measure : Option Expression.Expr)
    (inv : List (String × Expression.Expr))
    (body : Statements) (md : MetaData Expression)
    (ρ₀ ρ_target : Env Expression)
    (hnf : ρ₀.hasFailure = Bool.false)
    (hall_tt₀ : ∀ le ∈ inv, ρ₀.eval ρ₀.store le.2 = .some HasBool.tt)
    (hguard_tt₀ : ρ₀.eval ρ₀.store g = some HasBool.tt)
    (hswf_body : BlockInitEnvWF reserved body ρ₀)
    -- Target conditions
    (hguard_tt_tgt : ρ_target.eval ρ_target.store g = some HasBool.tt)
    (hall_tt_tgt : ∀ le ∈ inv, ρ_target.eval ρ_target.store le.2 = some HasBool.tt)
    (hswf_tgt : BlockInitEnvWF reserved body ρ_target)
    (heval_tgt : ρ_target.eval = ρ₀.eval)
    (hfail_tgt : ρ_target.hasFailure = ρ₀.hasFailure)
    (hagree : ∀ x, x ∉ (Block.modifiedVars body).filter (fun v => v ∉ Block.definedVars body false) →
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
      let assigned_vars := (Block.modifiedVars body).filter (fun v => v ∉ Block.definedVars body false)
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
  -- Extract WF eval fields from BlockInitEnvWF.
  have hwfb := hswf_body.wfBool
  have hwfvar := hswf_body.wfVar
  have hwfc := hswf_body.evalCong
  have hwfv := hswf_body.wfVal
  let loop_num := (StringGenState.gen "loop" σ.gen).fst
  let assigned_vars := (Block.modifiedVars body).filter (fun v => v ∉ Block.definedVars body false)
  -- `assigned_vars ⊆ touchedVars body \ definedVars body`, so `readWritesDefined`
  -- from `BlockInitEnvWF` gives `(ρ.store n).isSome` for ρ ∈ {ρ₀, ρ_target}.
  have hdef_assigned : ∀ n ∈ assigned_vars, (ρ₀.store n).isSome := by
    intro n hn
    have hmod : n ∈ Block.modifiedVars body :=
      (List.mem_filter.mp hn).1
    have hndef : n ∉ Block.definedVars body false := by
      have h := (List.mem_filter.mp hn).2
      simpa using h
    apply hswf_body.readWritesDefined n
    · show n ∈ Block.modifiedOrDefinedVars body true ++ Block.getVars body
      exact List.mem_append_left _ (List.mem_append_left _ hmod)
    · exact hndef
  have hdef_assigned_tgt : ∀ n ∈ assigned_vars, (ρ_target.store n).isSome := by
    intro n hn
    have hmod : n ∈ Block.modifiedVars body :=
      (List.mem_filter.mp hn).1
    have hndef : n ∉ Block.definedVars body false := by
      have h := (List.mem_filter.mp hn).2
      simpa using h
    apply hswf_tgt.readWritesDefined n
    · show n ∈ Block.modifiedOrDefinedVars body true ++ Block.getVars body
      exact List.mem_append_left _ (List.mem_append_left _ hmod)
    · exact hndef
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
      let assigned_vars := (Block.modifiedVars body).filter (fun v => v ∉ Block.definedVars body false)
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
    simp only [stmtRun, StateT.run, ExceptT.run, Stmt.removeLoopsM, removeLoopsLoopCase, buildLoopOutput, buildLoopPassive, buildArbitraryIterFacts, buildArbitraryIterAssumes, buildExitStateAssumes, buildHavocBlock, buildFirstIterFacts, buildEntryInvariants, buildEntryInvariantAssumes, buildInvAssumes, buildMaintainInvariants, buildExitInvariantAssumes, buildGuardParts, buildTerminationStmtsSome, hasLabelConflict, numAssertAssumesForLoop, invSuffix, measureOldIdent,
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
      | (simp [stmtRun, StateT.run, ExceptT.run, Stmt.removeLoopsM, removeLoopsLoopCase, buildLoopOutput, buildLoopPassive, buildArbitraryIterFacts, buildArbitraryIterAssumes, buildExitStateAssumes, buildHavocBlock, buildFirstIterFacts, buildEntryInvariants, buildEntryInvariantAssumes, buildInvAssumes, buildMaintainInvariants, buildExitInvariantAssumes, buildGuardParts, buildTerminationStmtsSome, hasLabelConflict, numAssertAssumesForLoop, invSuffix, measureOldIdent,
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
      | (simp [stmtRun, StateT.run, ExceptT.run, Stmt.removeLoopsM, removeLoopsLoopCase, buildLoopOutput, buildLoopPassive, buildArbitraryIterFacts, buildArbitraryIterAssumes, buildExitStateAssumes, buildHavocBlock, buildFirstIterFacts, buildEntryInvariants, buildEntryInvariantAssumes, buildInvAssumes, buildMaintainInvariants, buildExitInvariantAssumes, buildGuardParts, buildTerminationStmtsSome, hasLabelConflict, numAssertAssumesForLoop, invSuffix, measureOldIdent,
              bind, pure, ExceptT.bind, ExceptT.pure, ExceptT.mk, ExceptT.bindCont,
              ExceptT.lift, StateT.bind, Functor.map, liftM, monadLift, MonadLift.monadLift,
              modify, MonadState.modifyGet, StateT.modifyGet, StateT.map,
              genLoopNum, bumpStat, Except.isOk, Except.toBool,
              StateT.pure] at hok'; (try contradiction); (try simp_all)))

/-! ## Arbitrary-iteration block plumbing

These are pure trace-composition helpers used by the main simulation
argument to assemble the trace through the transformed `arb_iter_block`
(prefix ++ body ++ maintain ++ suffix, all wrapped in a `.block`) and
through the `exit_state_stmts` (havoc + assume(¬G) + invariant_assumes).
They are mechanical: each combines existing primitives like
`block_wrap_terminal`, `stmts_concat_terminal`, etc.  No new semantic
content is introduced. -/

/-- Pure trace composition: if the four pieces (prefix, body, maintain,
    suffix) each terminate in sequence, then the full block
    `(prefix ++ body ++ maintain ++ suffix)` wrapped in a `.block`
    terminates at the suffix's final env (with the parent store
    re-projected by `block_wrap_terminal`). -/
private theorem arb_iter_block_terminates
    (arb_iter_label : String)
    (prefix_stmts body_stmts maintain_invariants suffix_stmts : Statements)
    (md : MetaData Expression)
    (ρ₀ ρ_pf ρ_body ρ_maint ρ_end : Env Expression)
    (hpf : CoreStar π φ (.stmts prefix_stmts ρ₀) (.terminal ρ_pf))
    (hbody : CoreStar π φ (.stmts body_stmts ρ_pf) (.terminal ρ_body))
    (hmaint : CoreStar π φ (.stmts maintain_invariants ρ_body) (.terminal ρ_maint))
    (hsuffix : CoreStar π φ (.stmts suffix_stmts ρ_maint) (.terminal ρ_end)) :
    CoreStar π φ
      (.stmt (.block arb_iter_label
        (prefix_stmts ++ body_stmts ++ maintain_invariants ++ suffix_stmts) md) ρ₀)
      (.terminal { ρ_end with store := projectStore ρ₀.store ρ_end.store }) := by
  -- Concatenate the four pieces into a single terminating run of the inner stmts.
  have h_pf_body : CoreStar π φ (.stmts (prefix_stmts ++ body_stmts) ρ₀) (.terminal ρ_body) :=
    stmts_concat_terminal π φ _ _ ρ₀ ρ_pf ρ_body hpf hbody
  have h_pf_body_maint : CoreStar π φ
      (.stmts ((prefix_stmts ++ body_stmts) ++ maintain_invariants) ρ₀)
      (.terminal ρ_maint) :=
    stmts_concat_terminal π φ _ _ ρ₀ ρ_body ρ_maint h_pf_body hmaint
  have h_all : CoreStar π φ
      (.stmts (((prefix_stmts ++ body_stmts) ++ maintain_invariants) ++ suffix_stmts) ρ₀)
      (.terminal ρ_end) :=
    stmts_concat_terminal π φ _ _ ρ₀ ρ_maint ρ_end h_pf_body_maint hsuffix
  -- Re-associate into the canonical form.
  have hassoc :
      ((prefix_stmts ++ body_stmts) ++ maintain_invariants) ++ suffix_stmts =
      prefix_stmts ++ body_stmts ++ maintain_invariants ++ suffix_stmts := by
    simp [List.append_assoc]
  rw [hassoc] at h_all
  exact block_wrap_terminal π φ arb_iter_label _ md ρ₀ ρ_end h_all

/-- Variant of `arb_iter_block_terminates` for the case where one of the
    four inner pieces terminates by `.exiting` at a label different from
    `arb_iter_label` — the exit propagates out of the block.  Here we
    take the most general statement: assume the inner concatenation runs
    to `.exiting lv` for `lv ≠ arb_iter_label`. -/
private theorem ite_det_true_terminal
    (g : Expression.Expr) (then_branch : Statements) (md : MetaData Expression)
    (ρ₀ ρ' : Env Expression)
    (hguard_tt : ρ₀.eval ρ₀.store g = some HasBool.tt)
    (hwfb : WellFormedSemanticEvalBool ρ₀.eval)
    (hthen : CoreStar π φ (.stmts then_branch ρ₀) (.terminal ρ')) :
    CoreStar π φ (.stmt (.ite (.det g) then_branch [] md) ρ₀)
      (.terminal { ρ' with store := projectStore ρ₀.store ρ'.store }) :=
  .step _ _ _ (.step_ite_true hguard_tt hwfb)
    (ReflTrans_Transitive _ _ _ _
      (block_inner_star Expression (EvalCommand π φ) (EvalPureFunc φ) _ _ .none ρ₀.store hthen)
      (.step _ _ _ .step_block_done (.refl _)))

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
  simp only [stmtOk, stmtRun, blockOk, blockRun, Stmt.removeLoopsM, removeLoopsLoopCase, buildLoopOutput, buildLoopPassive, buildArbitraryIterFacts, buildArbitraryIterAssumes, buildExitStateAssumes, buildHavocBlock, buildFirstIterFacts, buildEntryInvariants, buildEntryInvariantAssumes, buildInvAssumes, buildMaintainInvariants, buildExitInvariantAssumes, buildGuardParts, buildTerminationStmtsSome, hasLabelConflict, numAssertAssumesForLoop, invSuffix, measureOldIdent, StateT.run, ExceptT.run,
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
  simp only [stmtOk, stmtRun, blockOk, blockRun, Stmt.removeLoopsM, removeLoopsLoopCase, buildLoopOutput, buildLoopPassive, buildArbitraryIterFacts, buildArbitraryIterAssumes, buildExitStateAssumes, buildHavocBlock, buildFirstIterFacts, buildEntryInvariants, buildEntryInvariantAssumes, buildInvAssumes, buildMaintainInvariants, buildExitInvariantAssumes, buildGuardParts, buildTerminationStmtsSome, hasLabelConflict, numAssertAssumesForLoop, invSuffix, measureOldIdent, StateT.run, ExceptT.run,
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
  simp only [stmtOk, stmtRun, blockOk, blockRun, blockPostState, Stmt.removeLoopsM, removeLoopsLoopCase, buildLoopOutput, buildLoopPassive, buildArbitraryIterFacts, buildArbitraryIterAssumes, buildExitStateAssumes, buildHavocBlock, buildFirstIterFacts, buildEntryInvariants, buildEntryInvariantAssumes, buildInvAssumes, buildMaintainInvariants, buildExitInvariantAssumes, buildGuardParts, buildTerminationStmtsSome, hasLabelConflict, numAssertAssumesForLoop, invSuffix, measureOldIdent, StateT.run,
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

/-! ## InitEnvWF derivations for sub-statements

Helpers to extract `BlockInitEnvWF`/`InitEnvWF` of sub-pieces from a parent
`InitEnvWF`/`BlockInitEnvWF`. These power the recursive calls in
`simulation`/`canfail_simulation`. -/

/-! ### `defUseWellFormed` projection helpers -/

/-- Extensional congruence for blocks. -/
private theorem defUseWellFormed_block_congr {outer₁ outer₂ : Expression.Ident → Bool}
    (heq : ∀ n, outer₁ n = outer₂ n) (bss : Statements) :
    Block.defUseWellFormed outer₁ bss = Block.defUseWellFormed outer₂ bss := by
  have hf : outer₁ = outer₂ := funext heq
  rw [hf]




/-- Project `Stmt.defUseWellFormed outer (.block l bss md) = Block.defUseWellFormed outer bss`. -/
private theorem defUseWellFormed_block (outer : Expression.Ident → Bool) (l : String)
    (bss : Statements) (md : MetaData Expression) :
    Stmt.defUseWellFormed outer (.block l bss md) = Block.defUseWellFormed outer bss := by
  unfold Stmt.defUseWellFormed; rfl

/-- From a true `defUseWellFormed` for an `.ite`, project both branches. -/
private theorem defUseWellFormed_ite_branches {outer : Expression.Ident → Bool}
    {c : ExprOrNondet Expression} {tss ess : Statements} {md : MetaData Expression}
    (h : Stmt.defUseWellFormed outer (.ite c tss ess md) = Bool.true) :
    Block.defUseWellFormed outer tss = Bool.true ∧
    Block.defUseWellFormed outer ess = Bool.true := by
  unfold Stmt.defUseWellFormed at h
  simp only [Bool.and_eq_true] at h
  exact ⟨h.1.2, h.2⟩

/-- From a true `defUseWellFormed` on `s :: ss`, project the head and tail
    (with the tail seen against an extended outer scope). -/
private theorem defUseWellFormed_cons {outer : Expression.Ident → Bool}
    {s : Statement} {ss : Statements}
    (h : Block.defUseWellFormed outer (s :: ss) = Bool.true) :
    Stmt.defUseWellFormed outer s = Bool.true ∧
    Block.defUseWellFormed (fun n => outer n || decide (n ∈ Stmt.definedVars s true)) ss = Bool.true := by
  unfold Block.defUseWellFormed at h
  simp only [Bool.and_eq_true] at h
  exact h

/-- Build a `Block.defUseWellFormed` from a stmt and a tail well-formedness
    against an extended outer scope. -/
private theorem defUseWellFormed_cons_intro {outer : Expression.Ident → Bool}
    {s : Statement} {ss : Statements}
    (h_s : Stmt.defUseWellFormed outer s = Bool.true)
    (h_ss : Block.defUseWellFormed (fun n => outer n || decide (n ∈ Stmt.definedVars s true)) ss = Bool.true) :
    Block.defUseWellFormed outer (s :: ss) = Bool.true := by
  unfold Block.defUseWellFormed
  simp only [Bool.and_eq_true]; exact ⟨h_s, h_ss⟩

/-- Monotonicity-with-freshness for `defUseWellFormed`: extending `outer` by a
    set of fresh names that don't appear in the statement's `touchedVars` ∪
    `definedVars` preserves `defUseWellFormed`.

    Concretely: if the statement is well-formed against `outer`, and a predicate
    `extra` characterizes a set of names disjoint from the statement's vars,
    then the statement is also well-formed against `(fun n => outer n || extra n)`. -/
private theorem defUseWellFormed_outer_extend_aux (sz : Nat) :
    (∀ (outer extra : Expression.Ident → Bool) (s : Statement),
      Stmt.sizeOf s ≤ sz →
      Stmt.defUseWellFormed outer s = Bool.true →
      (∀ n, extra n = Bool.true →
        n ∉ Stmt.modifiedVars s ∧ n ∉ Stmt.getVars s ∧
        n ∉ Stmt.definedVars s false) →
      Stmt.defUseWellFormed (fun n => outer n || extra n) s = Bool.true) ∧
    (∀ (outer extra : Expression.Ident → Bool) (bss : Statements),
      Block.sizeOf bss ≤ sz →
      Block.defUseWellFormed outer bss = Bool.true →
      (∀ n, extra n = Bool.true →
        n ∉ Block.modifiedVars bss ∧ n ∉ Block.getVars bss ∧
        n ∉ Block.definedVars bss false) →
      Block.defUseWellFormed (fun n => outer n || extra n) bss = Bool.true) := by
  induction sz with
  | zero =>
    refine ⟨?_, ?_⟩
    · intro outer extra s hsz; cases s <;> simp [Stmt.sizeOf] at hsz
    · intro outer extra bss hsz hwf hext
      match bss with
      | [] => simp [Block.defUseWellFormed]
      | s :: rest => simp [Block.sizeOf] at hsz
  | succ k ih =>
    obtain ⟨ih_stmt, ih_block⟩ := ih
    refine ⟨?_, ?_⟩
    · -- Stmt case
      intro outer extra s hsz hwf hext
      match s with
      | .cmd c =>
        unfold Stmt.defUseWellFormed at hwf ⊢
        simp only [Bool.and_eq_true] at hwf ⊢
        obtain ⟨⟨hgv, hmv⟩, hdef⟩ := hwf
        refine ⟨⟨?_, ?_⟩, ?_⟩
        · rw [List.all_eq_true] at hgv ⊢
          intro n hn
          simp only [Bool.or_eq_true]
          exact .inl (hgv n hn)
        · rw [List.all_eq_true] at hmv ⊢
          intro n hn
          simp only [Bool.or_eq_true]
          exact .inl (hmv n hn)
        · rw [List.all_eq_true] at hdef ⊢
          intro n hn
          have hd := hdef n hn
          simp only [decide_eq_true_eq] at hd ⊢
          intro hcontra
          rw [Bool.or_eq_true] at hcontra
          rcases hcontra with h | h
          · exact hd h
          · exact (hext n h).2.2 (by
              simp only [Stmt.definedVars, HasVarsImp.definedVars] at hn
              simp only [Stmt.definedVars, HasVarsImp.definedVars]; exact hn)
      | .block l bss md =>
        unfold Stmt.defUseWellFormed at hwf ⊢
        have hsz_bss : Block.sizeOf bss ≤ k := by simp [Stmt.sizeOf] at hsz; omega
        have hext_bss : ∀ n, extra n = Bool.true →
            n ∉ Block.modifiedVars bss ∧ n ∉ Block.getVars bss ∧
            n ∉ Block.definedVars bss false := by
          intro n hn
          have ⟨hm, hg, hd⟩ := hext n hn
          refine ⟨?_, ?_, ?_⟩
          · simpa [Stmt.modifiedVars] using hm
          · simpa [Stmt.getVars] using hg
          · simpa [Stmt.definedVars] using hd
        exact ih_block outer extra bss hsz_bss hwf hext_bss
      | .ite cond tbss ebss md =>
        unfold Stmt.defUseWellFormed at hwf ⊢
        simp only [Bool.and_eq_true] at hwf ⊢
        obtain ⟨⟨hcond_all, htbss⟩, hebss⟩ := hwf
        rw [List.all_eq_true] at hcond_all
        have hsz_t : Block.sizeOf tbss ≤ k := by simp [Stmt.sizeOf] at hsz; omega
        have hsz_e : Block.sizeOf ebss ≤ k := by simp [Stmt.sizeOf] at hsz; omega
        have hext_t : ∀ n, extra n = Bool.true →
            n ∉ Block.modifiedVars tbss ∧ n ∉ Block.getVars tbss ∧
            n ∉ Block.definedVars tbss false := by
          intro n hn
          have ⟨hm, hg, hd⟩ := hext n hn
          refine ⟨?_, ?_, ?_⟩
          · intro hh; exact hm (by
              simp only [Stmt.modifiedVars, List.mem_append]; exact .inl hh)
          · intro hh; exact hg (by
              simp only [Stmt.getVars, List.mem_append]; exact .inl (.inr hh))
          · intro hh; exact hd (by
              simp only [Stmt.definedVars, Bool.false_eq_true, ↓reduceIte, List.mem_append]
              exact .inl hh)
        have hext_e : ∀ n, extra n = Bool.true →
            n ∉ Block.modifiedVars ebss ∧ n ∉ Block.getVars ebss ∧
            n ∉ Block.definedVars ebss false := by
          intro n hn
          have ⟨hm, hg, hd⟩ := hext n hn
          refine ⟨?_, ?_, ?_⟩
          · intro hh; exact hm (by
              simp only [Stmt.modifiedVars, List.mem_append]; exact .inr hh)
          · intro hh; exact hg (by
              simp only [Stmt.getVars, List.mem_append]; exact .inr hh)
          · intro hh; exact hd (by
              simp only [Stmt.definedVars, Bool.false_eq_true, ↓reduceIte, List.mem_append]
              exact .inr hh)
        refine ⟨⟨?_, ?_⟩, ?_⟩
        · rw [List.all_eq_true]
          intro n hn; simp only [Bool.or_eq_true]; exact .inl (hcond_all n hn)
        · exact ih_block outer extra tbss hsz_t htbss hext_t
        · exact ih_block outer extra ebss hsz_e hebss hext_e
      | .loop guard measure inv body md =>
        unfold Stmt.defUseWellFormed at hwf ⊢
        simp only [Bool.and_eq_true] at hwf ⊢
        obtain ⟨⟨⟨hguard_all, hmeas_all⟩, hinv_all⟩, hbody⟩ := hwf
        rw [List.all_eq_true] at hguard_all hmeas_all hinv_all
        have hsz_body : Block.sizeOf body ≤ k := by simp [Stmt.sizeOf] at hsz; omega
        have hext_body : ∀ n, extra n = Bool.true →
            n ∉ Block.modifiedVars body ∧ n ∉ Block.getVars body ∧
            n ∉ Block.definedVars body false := by
          intro n hn
          have ⟨hm, hg, hd⟩ := hext n hn
          refine ⟨?_, ?_, ?_⟩
          · simpa [Stmt.modifiedVars] using hm
          · intro hh; exact hg (by
              simp only [Stmt.getVars, List.mem_append]; exact .inr hh)
          · simpa [Stmt.definedVars] using hd
        refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
        · rw [List.all_eq_true]
          intro n hn; simp only [Bool.or_eq_true]; exact .inl (hguard_all n hn)
        · rw [List.all_eq_true]
          intro n hn; simp only [Bool.or_eq_true]; exact .inl (hmeas_all n hn)
        · rw [List.all_eq_true]
          intro n hn; simp only [Bool.or_eq_true]; exact .inl (hinv_all n hn)
        · exact ih_block outer extra body hsz_body hbody hext_body
      | .exit l md => simp [Stmt.defUseWellFormed]
      | .funcDecl decl md =>
        unfold Stmt.defUseWellFormed at hwf; simp at hwf
      | .typeDecl tc md => simp [Stmt.defUseWellFormed]
    · -- Block case
      intro outer extra bss hsz hwf hext
      match bss with
      | [] => simp [Block.defUseWellFormed]
      | s :: rest =>
        unfold Block.defUseWellFormed at hwf ⊢
        simp only [Bool.and_eq_true] at hwf ⊢
        obtain ⟨hwf_s, hwf_rest⟩ := hwf
        have hsz_s : Stmt.sizeOf s ≤ k := by simp [Block.sizeOf] at hsz; omega
        have hsz_rest : Block.sizeOf rest ≤ k := by simp [Block.sizeOf] at hsz; omega
        have hext_s : ∀ n, extra n = Bool.true →
            n ∉ Stmt.modifiedVars s ∧ n ∉ Stmt.getVars s ∧
            n ∉ Stmt.definedVars s false := by
          intro n hn
          have ⟨hm, hg, hd⟩ := hext n hn
          refine ⟨?_, ?_, ?_⟩
          · intro hh; exact hm (by
              simp only [Block.modifiedVars, List.mem_append]; exact .inl hh)
          · intro hh; exact hg (by
              simp only [Block.getVars, List.mem_append]; exact .inl hh)
          · intro hh; exact hd (by
              simp only [Block.definedVars, List.mem_append]; exact .inl hh)
        have hext_rest : ∀ n, extra n = Bool.true →
            n ∉ Block.modifiedVars rest ∧ n ∉ Block.getVars rest ∧
            n ∉ Block.definedVars rest false := by
          intro n hn
          have ⟨hm, hg, hd⟩ := hext n hn
          refine ⟨?_, ?_, ?_⟩
          · intro hh; exact hm (by
              simp only [Block.modifiedVars, List.mem_append]; exact .inr hh)
          · intro hh; exact hg (by
              simp only [Block.getVars, List.mem_append]; exact .inr hh)
          · intro hh; exact hd (by
              simp only [Block.definedVars, List.mem_append]; exact .inr hh)
        refine ⟨ih_stmt outer extra s hsz_s hwf_s hext_s, ?_⟩
        -- For tail, the inner outer extends by `decide (n ∈ Stmt.definedVars s true)`.
        -- Want: Block.defUseWellFormed
        --   (fun n => (outer n || extra n) || decide (n ∈ Stmt.definedVars s true)) rest
        -- Have: Block.defUseWellFormed
        --   (fun n => outer n || decide (n ∈ Stmt.definedVars s true)) rest
        -- Use ih_block with extra := extra and outer = original tail outer.
        have h_inner : Block.defUseWellFormed
            (fun n => (fun m => outer m || decide (m ∈ Stmt.definedVars s true)) n || extra n)
            rest = Bool.true :=
          ih_block (fun m => outer m || decide (m ∈ Stmt.definedVars s true)) extra rest
            hsz_rest hwf_rest hext_rest
        -- Reorganize the boolean predicate.
        have heq : (fun n =>
              (outer n || decide (n ∈ Stmt.definedVars s true)) || extra n) =
            (fun n => (outer n || extra n) || decide (n ∈ Stmt.definedVars s true)) := by
          funext n; simp only [Bool.or_assoc, Bool.or_comm (decide _) (extra _)]
        rw [heq] at h_inner
        exact h_inner

private theorem defUseWellFormed_outer_extend_stmt
    {outer extra : Expression.Ident → Bool} {s : Statement}
    (hwf : Stmt.defUseWellFormed outer s = Bool.true)
    (hext : ∀ n, extra n = Bool.true →
        n ∉ Stmt.modifiedVars s ∧ n ∉ Stmt.getVars s ∧
        n ∉ Stmt.definedVars s false) :
    Stmt.defUseWellFormed (fun n => outer n || extra n) s = Bool.true :=
  (defUseWellFormed_outer_extend_aux (Stmt.sizeOf s)).1 outer extra s
    (Nat.le_refl _) hwf hext

private theorem defUseWellFormed_outer_extend_block
    {outer extra : Expression.Ident → Bool} {bss : Statements}
    (hwf : Block.defUseWellFormed outer bss = Bool.true)
    (hext : ∀ n, extra n = Bool.true →
        n ∉ Block.modifiedVars bss ∧ n ∉ Block.getVars bss ∧
        n ∉ Block.definedVars bss false) :
    Block.defUseWellFormed (fun n => outer n || extra n) bss = Bool.true :=
  (defUseWellFormed_outer_extend_aux (Block.sizeOf bss)).2 outer extra bss
    (Nat.le_refl _) hwf hext

/-- Append decomposition for `Block.defUseWellFormed`. -/
private theorem defUseWellFormed_block_append
    (outer : Expression.Ident → Bool) (ss₁ ss₂ : Statements) :
    Block.defUseWellFormed outer (ss₁ ++ ss₂) = Bool.true ↔
      Block.defUseWellFormed outer ss₁ = Bool.true ∧
      Block.defUseWellFormed
        (fun n => outer n || decide (n ∈ Block.definedVars ss₁ true)) ss₂ = Bool.true := by
  induction ss₁ generalizing outer with
  | nil => simp [Block.definedVars, Block.defUseWellFormed]
  | cons s rest ih =>
    show Block.defUseWellFormed outer (s :: (rest ++ ss₂)) = Bool.true ↔ _
    constructor
    · intro h
      have ⟨h_s, h_rest⟩ := defUseWellFormed_cons h
      have ⟨h_rest', h_ss₂⟩ :=
        (ih (fun n => outer n || decide (n ∈ Stmt.definedVars s true))).mp h_rest
      refine ⟨?_, ?_⟩
      · unfold Block.defUseWellFormed
        simp only [Bool.and_eq_true]; exact ⟨h_s, h_rest'⟩
      · rw [defUseWellFormed_block_congr (fun n => ?_) ss₂]
        · exact h_ss₂
        · simp only [Block.definedVars, List.mem_append, Bool.or_assoc, Bool.decide_or]
    · intro ⟨h_left, h_right⟩
      have ⟨h_s, h_rest_left⟩ := defUseWellFormed_cons h_left
      apply defUseWellFormed_cons_intro h_s
      apply (ih (fun n => outer n || decide (n ∈ Stmt.definedVars s true))).mpr
      refine ⟨h_rest_left, ?_⟩
      rw [defUseWellFormed_block_congr (fun n => ?_) ss₂]
      · exact h_right
      · simp only [Block.definedVars, List.mem_append, Bool.or_assoc, Bool.decide_or]


/-- `Stmt.definedVars s true ⊆ Stmt.definedVars s false` for any statement. -/
private theorem stmt_definedVars_true_subset_false (s : Statement) (n : Expression.Ident)
    (h : n ∈ Stmt.definedVars s true) : n ∈ Stmt.definedVars s false := by
  match s with
  | .cmd c => simp [Stmt.definedVars] at h ⊢; exact h
  | .block .. => simp [Stmt.definedVars] at h
  | .ite .. => simp [Stmt.definedVars] at h
  | .loop .. => simp [Stmt.definedVars] at h
  | .exit .. => simp [Stmt.definedVars] at h
  | .funcDecl .. => simp [Stmt.definedVars] at h ⊢; exact h
  | .typeDecl .. => simp [Stmt.definedVars] at h

/-- Combined mutual induction: if `defUseWellFormed outer` holds and `n` is
    read or modified but not defined, then `outer n = true`. -/
private theorem defUseWellFormed_touched_notDef_aux (sz : Nat) :
    (∀ (outer : Expression.Ident → Bool) (s : Statement),
      Stmt.sizeOf s ≤ sz →
      Stmt.defUseWellFormed outer s = Bool.true →
      ∀ (n : Expression.Ident),
        (n ∈ Stmt.modifiedVars s ∨ n ∈ Stmt.getVars s) →
        n ∉ Stmt.definedVars s false →
        outer n = Bool.true) ∧
    (∀ (outer : Expression.Ident → Bool) (bss : Statements),
      Block.sizeOf bss ≤ sz →
      Block.defUseWellFormed outer bss = Bool.true →
      ∀ (n : Expression.Ident),
        (n ∈ Block.modifiedVars bss ∨ n ∈ Block.getVars bss) →
        n ∉ Block.definedVars bss false →
        outer n = Bool.true) := by
  induction sz with
  | zero =>
    refine ⟨?_, ?_⟩
    · intro outer s hsz; cases s <;> simp [Stmt.sizeOf] at hsz
    · intro outer bss hsz hwf n hn hnd
      match bss with
      | [] => simp [Block.modifiedVars, Block.getVars] at hn
      | s :: rest => simp [Block.sizeOf] at hsz
  | succ k ih =>
    obtain ⟨ih_stmt, ih_block⟩ := ih
    refine ⟨?_, ?_⟩
    · -- Stmt case
      intro outer s hsz hwf n hn hnd
      match s with
      | .cmd c =>
        unfold Stmt.defUseWellFormed at hwf
        simp only [Bool.and_eq_true] at hwf
        obtain ⟨⟨hgv, hmv⟩, _⟩ := hwf
        rw [List.all_eq_true] at hgv hmv
        simp only [Stmt.modifiedVars, Stmt.getVars] at hn
        rcases hn with hmod | hget
        · exact hmv n hmod
        · exact hgv n hget
      | .block l bss md =>
        simp only [Stmt.modifiedVars, Stmt.getVars, Stmt.definedVars,
          Bool.false_eq_true, ↓reduceIte] at hn hnd
        unfold Stmt.defUseWellFormed at hwf
        have hsz_bss : Block.sizeOf bss ≤ k := by simp [Stmt.sizeOf] at hsz; omega
        exact ih_block outer bss hsz_bss hwf n hn hnd
      | .ite cond tbss ebss md =>
        unfold Stmt.defUseWellFormed at hwf
        simp only [Bool.and_eq_true] at hwf
        obtain ⟨⟨hcond_all, htbss⟩, hebss⟩ := hwf
        rw [List.all_eq_true] at hcond_all
        simp only [Stmt.modifiedVars, Stmt.getVars, Stmt.definedVars,
          Bool.false_eq_true, ↓reduceIte, List.mem_append] at hn hnd
        have hnd_t : n ∉ Block.definedVars tbss false := fun h => hnd (Or.inl h)
        have hnd_e : n ∉ Block.definedVars ebss false := fun h => hnd (Or.inr h)
        have hsz_t : Block.sizeOf tbss ≤ k := by simp [Stmt.sizeOf] at hsz; omega
        have hsz_e : Block.sizeOf ebss ≤ k := by simp [Stmt.sizeOf] at hsz; omega
        rcases hn with (ht | he) | (hc | hgt) | hge
        · exact ih_block outer tbss hsz_t htbss n (Or.inl ht) hnd_t
        · exact ih_block outer ebss hsz_e hebss n (Or.inl he) hnd_e
        · exact hcond_all n hc
        · exact ih_block outer tbss hsz_t htbss n (Or.inr hgt) hnd_t
        · exact ih_block outer ebss hsz_e hebss n (Or.inr hge) hnd_e
      | .loop guard measure inv body md =>
        unfold Stmt.defUseWellFormed at hwf
        simp only [Bool.and_eq_true] at hwf
        obtain ⟨⟨⟨hguard_all, hmeas_all⟩, hinv_all⟩, hbody⟩ := hwf
        rw [List.all_eq_true] at hguard_all hmeas_all hinv_all
        simp only [Stmt.modifiedVars, Stmt.getVars, Stmt.definedVars,
          Bool.false_eq_true, ↓reduceIte, List.mem_append] at hn hnd
        have hsz_body : Block.sizeOf body ≤ k := by simp [Stmt.sizeOf] at hsz; omega
        rcases hn with hmod | ((hg | hm) | hi) | hb
        · exact ih_block outer body hsz_body hbody n (Or.inl hmod) hnd
        · exact hguard_all n hg
        · exact hmeas_all n hm
        · exact hinv_all n hi
        · exact ih_block outer body hsz_body hbody n (Or.inr hb) hnd
      | .exit l md =>
        simp [Stmt.modifiedVars, Stmt.getVars] at hn
      | .funcDecl decl md =>
        unfold Stmt.defUseWellFormed at hwf; simp at hwf
      | .typeDecl tc md =>
        simp [Stmt.modifiedVars, Stmt.getVars] at hn
    · -- Block case
      intro outer bss hsz hwf n hn hnd
      match bss with
      | [] =>
        simp [Block.modifiedVars, Block.getVars] at hn
      | s :: rest =>
        unfold Block.defUseWellFormed at hwf
        simp only [Bool.and_eq_true] at hwf
        obtain ⟨hwf_s, hwf_rest⟩ := hwf
        simp only [Block.modifiedVars, Block.getVars, Block.definedVars,
          List.mem_append] at hn hnd
        have hnd_s : n ∉ Stmt.definedVars s false := fun h => hnd (Or.inl h)
        have hnd_rest : n ∉ Block.definedVars rest false := fun h => hnd (Or.inr h)
        have hsz_s : Stmt.sizeOf s ≤ k := by simp [Block.sizeOf] at hsz; omega
        have hsz_rest : Block.sizeOf rest ≤ k := by
          simp [Block.sizeOf] at hsz; omega
        have hnd_s_true : n ∉ Stmt.definedVars s true :=
          fun h => hnd_s (stmt_definedVars_true_subset_false s n h)
        rcases hn with (hs | hr) | (hs | hr)
        · exact ih_stmt outer s hsz_s hwf_s n (Or.inl hs) hnd_s
        · have h_rest_result := ih_block
            (fun m => outer m || decide (m ∈ Stmt.definedVars s true))
            rest hsz_rest hwf_rest n (Or.inl hr) hnd_rest
          rw [Bool.or_eq_true] at h_rest_result
          rcases h_rest_result with h | h
          · exact h
          · rw [decide_eq_true_eq] at h; exact absurd h hnd_s_true
        · exact ih_stmt outer s hsz_s hwf_s n (Or.inr hs) hnd_s
        · have h_rest_result := ih_block
            (fun m => outer m || decide (m ∈ Stmt.definedVars s true))
            rest hsz_rest hwf_rest n (Or.inr hr) hnd_rest
          rw [Bool.or_eq_true] at h_rest_result
          rcases h_rest_result with h | h
          · exact h
          · rw [decide_eq_true_eq] at h; exact absurd h hnd_s_true

/-- If `Stmt.defUseWellFormed outer s = true` and `n` is read or modified in `s`
    but never defined in `s`, then `outer n = true`.  This is the fundamental
    link between def-use well-formedness and `readWritesDefined`. -/
private theorem defUseWellFormed_modGetVars_implies_outer
    {outer : Expression.Ident → Bool} {bss : Statements}
    (hwf : Block.defUseWellFormed outer bss = Bool.true)
    {n : Expression.Ident}
    (hn : n ∈ Block.modifiedVars bss ∨ n ∈ Block.getVars bss)
    (hnd : n ∉ Block.definedVars bss false) : outer n = Bool.true :=
  (defUseWellFormed_touched_notDef_aux (Block.sizeOf bss)).2
    outer bss (Nat.le_refl _) hwf n hn hnd

/-- Stmt-level: touched but not defined implies `outer n`. -/
private theorem defUseWellFormed_touched_notDef_implies_outer
    {outer : Expression.Ident → Bool} {s : Statement}
    (hwf : Stmt.defUseWellFormed outer s = Bool.true)
    {n : Expression.Ident}
    (hn : n ∈ Stmt.modifiedVars s ∨ n ∈ Stmt.getVars s)
    (hnd : n ∉ Stmt.definedVars s false) : outer n = Bool.true :=
  (defUseWellFormed_touched_notDef_aux (Stmt.sizeOf s)).1
    outer s (Nat.le_refl _) hwf n hn hnd

/-- `Block.definedVars bss true ⊆ Block.definedVars bss false`. -/
private theorem block_definedVars_true_subset_false (bss : Statements) (n : Expression.Ident)
    (h : n ∈ Block.definedVars bss true) : n ∈ Block.definedVars bss false := by
  induction bss with
  | nil => simp [Block.definedVars] at h
  | cons s rest ih =>
    simp only [Block.definedVars, List.mem_append] at h ⊢
    rcases h with hs | hr
    · left
      match s with
      | .cmd c => simpa [Stmt.definedVars] using hs
      | .block .. => simp [Stmt.definedVars] at hs  -- hs : False
      | .ite .. => simp [Stmt.definedVars] at hs    -- hs : False
      | .loop .. => simp [Stmt.definedVars] at hs   -- hs : False
      | .exit .. => simpa [Stmt.definedVars] using hs
      | .funcDecl .. => simpa [Stmt.definedVars] using hs
      | .typeDecl .. => simpa [Stmt.definedVars] using hs
    · exact .inr (ih hr)

/-- `BlockInitEnvWF bss` follows from `InitEnvWF (.block l bss md)`: the block
    has the same touched/defined vars as its inner statements. -/
private theorem InitEnvWF.toBlock_block {reserved : List String} {l : String}
    {bss : Statements} {md : MetaData Expression} {ρ : Env Expression}
    (h : InitEnvWF reserved (.block l bss md) ρ) :
    BlockInitEnvWF reserved bss ρ where
  readWritesDefined n hn hnd := by
    refine h.readWritesDefined n ?_ ?_
    · show n ∈ Stmt.touchedVars (.block l bss md)
      show n ∈ Stmt.modifiedOrDefinedVars (.block l bss md) true ++
              Stmt.getVars (.block l bss md)
      -- Stmt.touchedVars (.block l bss md) = Block.modifiedVars bss ++ Block.getVars bss
      -- Block.touchedVars bss = (Block.modifiedVars bss ++ Block.definedVars bss true) ++ Block.getVars bss
      -- Need: n ∉ Block.definedVars bss false → n ∉ Block.definedVars bss true
      show n ∈ Stmt.modifiedVars (.block l bss md) ++ Stmt.definedVars (.block l bss md) true ++
                Stmt.getVars (.block l bss md)
      simp only [Stmt.modifiedVars, Stmt.definedVars, Stmt.getVars, ite_true, List.append_nil]
      -- goal: n ∈ Block.modifiedVars bss ++ Block.getVars bss
      -- hn : n ∈ Block.touchedVars bss = (Block.modifiedVars bss ++ Block.definedVars bss true) ++ Block.getVars bss
      have hn' : n ∈ (Block.modifiedVars bss ++ Block.definedVars bss true) ++ Block.getVars bss := hn
      rcases List.mem_append.mp hn' with h1 | h2
      · rcases List.mem_append.mp h1 with hmod | hdef
        · exact List.mem_append_left _ hmod
        · -- n ∈ Block.definedVars bss true but n ∉ Block.definedVars bss false → contradiction
          exact absurd (block_definedVars_true_subset_false bss n hdef) hnd
      · exact List.mem_append_right _ h2
    · show n ∉ Stmt.definedVars (.block l bss md) false
      have heq : Stmt.definedVars (.block l bss md : Statement) false =
                 Block.definedVars bss false := by simp [Stmt.definedVars]
      rw [heq]; exact hnd
  defsUndefined n hn := h.defsUndefined n (by
    show n ∈ Stmt.definedVars (.block l bss md) false
    have heq : Stmt.definedVars (.block l bss md : Statement) false =
               Block.definedVars bss false := by simp [Stmt.definedVars]
    rw [heq]; exact hn)
  definedVarsNotReserved n hn := h.definedVarsNotReserved n (by
    show n ∈ Stmt.definedVars (.block l bss md) false
    have heq : Stmt.definedVars (.block l bss md : Statement) false =
               Block.definedVars bss false := by simp [Stmt.definedVars]
    rw [heq]; exact hn)
  reservedFresh := h.reservedFresh
  wfBool := h.wfBool
  wfVal  := h.wfVal
  wfVar  := h.wfVar
  evalCong := h.evalCong
  exprCongr := h.exprCongr
  defUseOk := by
    have hwf := h.defUseOk
    rw [defUseWellFormed_block] at hwf
    exact hwf

/-- For ite: `BlockInitEnvWF tss` follows from `InitEnvWF (.ite c tss ess md)`.
    Uses `defUseOk` to derive `readWritesDefined` without disjointness hypotheses. -/
private theorem InitEnvWF.toBlock_ite_left {reserved : List String}
    {c : ExprOrNondet Expression}
    {tss ess : Statements} {md : MetaData Expression} {ρ : Env Expression}
    (h : InitEnvWF reserved (.ite c tss ess md) ρ) :
    BlockInitEnvWF reserved tss ρ where
  readWritesDefined n hn hnd := by
    have hwf_tss : Block.defUseWellFormed (fun n => (ρ.store n).isSome) tss = Bool.true :=
      (defUseWellFormed_ite_branches h.defUseOk).1
    have hn_mg : n ∈ Block.modifiedVars tss ∨ n ∈ Block.getVars tss := by
      have hntouched : n ∈ Block.touchedVars tss := hn
      simp only [Block.touchedVars, Block.modifiedOrDefinedVars, List.mem_append] at hntouched
      rcases hntouched with (hm | hd) | hg
      · exact Or.inl hm
      · exact absurd (block_definedVars_true_subset_false tss n hd) hnd
      · exact Or.inr hg
    exact defUseWellFormed_modGetVars_implies_outer hwf_tss hn_mg hnd
  defsUndefined n hn := h.defsUndefined n (by
    show n ∈ Stmt.definedVars (.ite c tss ess md) false
    simp only [Stmt.definedVars, Bool.false_eq_true, ↓reduceIte, List.mem_append]; left; exact hn)
  definedVarsNotReserved n hn p hp := h.definedVarsNotReserved n (by
    show n ∈ Stmt.definedVars (.ite c tss ess md) false
    simp only [Stmt.definedVars, Bool.false_eq_true, ↓reduceIte, List.mem_append]; left; exact hn) p hp
  reservedFresh := h.reservedFresh
  wfBool := h.wfBool
  wfVal  := h.wfVal
  wfVar  := h.wfVar
  evalCong := h.evalCong
  exprCongr := h.exprCongr
  defUseOk := (defUseWellFormed_ite_branches h.defUseOk).1

private theorem InitEnvWF.toBlock_ite_right {reserved : List String}
    {c : ExprOrNondet Expression}
    {tss ess : Statements} {md : MetaData Expression} {ρ : Env Expression}
    (h : InitEnvWF reserved (.ite c tss ess md) ρ) :
    BlockInitEnvWF reserved ess ρ where
  readWritesDefined n hn hnd := by
    have hwf_ess : Block.defUseWellFormed (fun n => (ρ.store n).isSome) ess = Bool.true :=
      (defUseWellFormed_ite_branches h.defUseOk).2
    have hn_mg : n ∈ Block.modifiedVars ess ∨ n ∈ Block.getVars ess := by
      have hntouched : n ∈ Block.touchedVars ess := hn
      simp only [Block.touchedVars, Block.modifiedOrDefinedVars, List.mem_append] at hntouched
      rcases hntouched with (hm | hd) | hg
      · exact Or.inl hm
      · exact absurd (block_definedVars_true_subset_false ess n hd) hnd
      · exact Or.inr hg
    exact defUseWellFormed_modGetVars_implies_outer hwf_ess hn_mg hnd
  defsUndefined n hn := h.defsUndefined n (by
    show n ∈ Stmt.definedVars (.ite c tss ess md) false
    simp only [Stmt.definedVars, Bool.false_eq_true, ↓reduceIte, List.mem_append]; right; exact hn)
  definedVarsNotReserved n hn p hp := h.definedVarsNotReserved n (by
    show n ∈ Stmt.definedVars (.ite c tss ess md) false
    simp only [Stmt.definedVars, Bool.false_eq_true, ↓reduceIte, List.mem_append]; right; exact hn) p hp
  reservedFresh := h.reservedFresh
  wfBool := h.wfBool
  wfVal  := h.wfVal
  wfVar  := h.wfVar
  evalCong := h.evalCong
  exprCongr := h.exprCongr
  defUseOk := (defUseWellFormed_ite_branches h.defUseOk).2

/-- `InitEnvWF s` follows from `BlockInitEnvWF (s :: ss)`.
    Uses `defUseOk` to derive `readWritesDefined` without disjointness hypotheses. -/
private theorem BlockInitEnvWF.toStmt_head {reserved : List String} {s : Statement}
    {ss : Statements} {ρ : Env Expression}
    (h : BlockInitEnvWF reserved (s :: ss) ρ) :
    InitEnvWF reserved s ρ where
  readWritesDefined n hn hnd := by
    have hwf_s : Stmt.defUseWellFormed (fun n => (ρ.store n).isSome) s = Bool.true :=
      (defUseWellFormed_cons h.defUseOk).1
    have hn_mg : n ∈ Stmt.modifiedVars s ∨ n ∈ Stmt.getVars s := by
      have hntouched : n ∈ Stmt.touchedVars s := hn
      simp only [Stmt.touchedVars, Stmt.modifiedOrDefinedVars, List.mem_append] at hntouched
      rcases hntouched with (hm | hd) | hg
      · exact Or.inl hm
      · exact absurd (block_definedVars_true_subset_false [s] n (by simp [Block.definedVars]; exact hd)) (by simp [Block.definedVars]; exact hnd)
      · exact Or.inr hg
    exact defUseWellFormed_touched_notDef_implies_outer hwf_s hn_mg hnd
  defsUndefined n hn := h.defsUndefined n (by
    show n ∈ Block.definedVars (s :: ss) false
    simp only [Block.definedVars, List.mem_append]; left; exact hn)
  definedVarsNotReserved n hn p hp := h.definedVarsNotReserved n (by
    show n ∈ Block.definedVars (s :: ss) false
    simp only [Block.definedVars, List.mem_append]; left; exact hn) p hp
  reservedFresh := h.reservedFresh
  wfBool := h.wfBool
  wfVal  := h.wfVal
  wfVar  := h.wfVar
  evalCong := h.evalCong
  exprCongr := h.exprCongr
  defUseOk := (defUseWellFormed_cons h.defUseOk).1

/-- Any variable that becomes `isSome` after executing `s` (from `isNone` before)
    must be in `Stmt.definedVars s`. -/
private theorem cmd_definedVars_true_isSome_after
    {cmd : Command} {ρ₀ ρ₁ : Env Expression}
    (hstar : CoreStar π φ (.stmt (.cmd cmd) ρ₀) (.terminal ρ₁))
    (n : Expression.Ident)
    (hn : n ∈ Stmt.definedVars (.cmd cmd) true) :
    (ρ₁.store n).isSome := by
  -- The trace is one step: step_cmd heval then refl.
  -- For n ∈ definedVars (.cmd cmd) true, cmd must be .cmd (.init n ...).
  -- After eval_init/eval_init_unconstrained, InitState gives σ' n = .some v.
  match hstar with
  | .step _ _ _ (.step_cmd heval) hrest =>
    cases hrest with
    | refl =>
      simp only [Config.getEnv]
      cases heval with
      | cmd_sem hcmd =>
        simp [Stmt.definedVars, HasVarsImp.definedVars, Command.definedVars] at hn
        cases hcmd with
        | eval_init _ hinit _ =>
          cases hinit with
          | init _ hsome _ =>
            simp [Cmd.definedVars, List.mem_singleton] at hn
            subst hn; simp [hsome]
        | eval_init_unconstrained hinit _ =>
          cases hinit with
          | init _ hsome _ =>
            simp [Cmd.definedVars, List.mem_singleton] at hn
            subst hn; simp [hsome]
        | eval_set _ _ _ => simp [Cmd.definedVars] at hn
        | eval_set_nondet _ _ => simp [Cmd.definedVars] at hn
        | eval_assert_pass _ _ => simp [Cmd.definedVars] at hn
        | eval_assert_fail _ _ => simp [Cmd.definedVars] at hn
        | eval_assume _ _ => simp [Cmd.definedVars] at hn
        | eval_cover _ => simp [Cmd.definedVars] at hn
      | @call_sem _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
        simp [Stmt.definedVars, HasVarsImp.definedVars, Command.definedVars] at hn
    | step _ _ _ hstep _ => exact nomatch hstep

private theorem stmt_definedVars_true_isSome_after
    {s : Statement} {ρ₀ ρ₁ : Env Expression}
    (hstar : CoreStar π φ (.stmt s ρ₀) (.terminal ρ₁))
    (_hnofd : Stmt.noFuncDecl s = Bool.true)
    (_hdefsNone : ∀ n ∈ Stmt.definedVars s true, (ρ₀.store n).isNone)
    (n : Expression.Ident)
    (hn : n ∈ Stmt.definedVars s true) :
    (ρ₁.store n).isSome := by
  match s, hstar, hn with
  | .cmd _, hstar', hn' => exact cmd_definedVars_true_isSome_after (π := π) (φ := φ) hstar' n hn'
  | .block .., _, hn' => simp [Stmt.definedVars] at hn'
  | .ite .., _, hn' => simp [Stmt.definedVars] at hn'
  | .loop .., _, hn' => simp [Stmt.definedVars] at hn'
  | .exit .., _, hn' => simp [Stmt.definedVars] at hn'
  | .funcDecl .., _, _ => exact absurd _hnofd (by simp [Stmt.noFuncDecl])
  | .typeDecl .., _, hn' => simp [Stmt.definedVars] at hn'

/-- From `Block.defUseWellFormed outer ss = true` and `n ∈ Block.definedVars ss false`,
    conclude that `outer n = false`.  This is the def-side dual of
    `defUseWellFormed_modGetVars_implies_outer`: in a well-formed block, freshly-defined
    variables can't already be in the outer scope.  We prove it by mutual induction on
    statement/block size, mirroring `defUseWellFormed_touched_notDef_aux`. -/
private theorem defUseWellFormed_definedVars_notMem_outer_aux (sz : Nat) :
    (∀ (outer : Expression.Ident → Bool) (s : Statement),
      Stmt.sizeOf s ≤ sz →
      Stmt.defUseWellFormed outer s = Bool.true →
      ∀ (n : Expression.Ident),
        n ∈ Stmt.definedVars s false →
        outer n = Bool.false) ∧
    (∀ (outer : Expression.Ident → Bool) (bss : Statements),
      Block.sizeOf bss ≤ sz →
      Block.defUseWellFormed outer bss = Bool.true →
      ∀ (n : Expression.Ident),
        n ∈ Block.definedVars bss false →
        outer n = Bool.false) := by
  induction sz with
  | zero =>
    refine ⟨?_, ?_⟩
    · intro outer s hsz; cases s <;> simp [Stmt.sizeOf] at hsz
    · intro outer bss hsz hwf n hn
      match bss with
      | [] => simp [Block.definedVars] at hn
      | s :: rest => simp [Block.sizeOf] at hsz
  | succ k ih =>
    obtain ⟨ih_stmt, ih_block⟩ := ih
    refine ⟨?_, ?_⟩
    · -- Stmt case
      intro outer s hsz hwf n hn
      match s with
      | .cmd c =>
        unfold Stmt.defUseWellFormed at hwf
        simp only [Bool.and_eq_true] at hwf
        obtain ⟨_, hdefs⟩ := hwf
        rw [List.all_eq_true] at hdefs
        simp only [Stmt.definedVars, HasVarsImp.definedVars] at hn
        have := hdefs n hn
        simp only [decide_eq_true_eq] at this
        cases h : outer n
        · rfl
        · exact absurd h this
      | .block l bss md =>
        simp only [Stmt.definedVars, Bool.false_eq_true, ↓reduceIte] at hn
        unfold Stmt.defUseWellFormed at hwf
        have hsz_bss : Block.sizeOf bss ≤ k := by simp [Stmt.sizeOf] at hsz; omega
        exact ih_block outer bss hsz_bss hwf n hn
      | .ite cond tbss ebss md =>
        unfold Stmt.defUseWellFormed at hwf
        simp only [Bool.and_eq_true] at hwf
        obtain ⟨⟨_, htbss⟩, hebss⟩ := hwf
        simp only [Stmt.definedVars, Bool.false_eq_true, ↓reduceIte, List.mem_append] at hn
        have hsz_t : Block.sizeOf tbss ≤ k := by simp [Stmt.sizeOf] at hsz; omega
        have hsz_e : Block.sizeOf ebss ≤ k := by simp [Stmt.sizeOf] at hsz; omega
        rcases hn with ht | he
        · exact ih_block outer tbss hsz_t htbss n ht
        · exact ih_block outer ebss hsz_e hebss n he
      | .loop guard measure inv body md =>
        unfold Stmt.defUseWellFormed at hwf
        simp only [Bool.and_eq_true] at hwf
        obtain ⟨_, hbody⟩ := hwf
        simp only [Stmt.definedVars, Bool.false_eq_true, ↓reduceIte] at hn
        have hsz_body : Block.sizeOf body ≤ k := by simp [Stmt.sizeOf] at hsz; omega
        exact ih_block outer body hsz_body hbody n hn
      | .exit l md => simp [Stmt.definedVars] at hn
      | .funcDecl decl md =>
        unfold Stmt.defUseWellFormed at hwf; simp at hwf
      | .typeDecl tc md => simp [Stmt.definedVars] at hn
    · -- Block case
      intro outer bss hsz hwf n hn
      match bss with
      | [] => simp [Block.definedVars] at hn
      | s :: rest =>
        unfold Block.defUseWellFormed at hwf
        simp only [Bool.and_eq_true] at hwf
        obtain ⟨hwf_s, hwf_rest⟩ := hwf
        simp only [Block.definedVars, List.mem_append] at hn
        have hsz_s : Stmt.sizeOf s ≤ k := by simp [Block.sizeOf] at hsz; omega
        have hsz_rest : Block.sizeOf rest ≤ k := by simp [Block.sizeOf] at hsz; omega
        rcases hn with hs | hr
        · exact ih_stmt outer s hsz_s hwf_s n hs
        · -- n ∈ Block.definedVars rest false ⟹ extended-outer n = false
          have h_rest_result := ih_block
            (fun m => outer m || decide (m ∈ Stmt.definedVars s true))
            rest hsz_rest hwf_rest n hr
          simp only [Bool.or_eq_false_iff, decide_eq_false_iff_not] at h_rest_result
          exact h_rest_result.1

/-- Block-level: from `defUseWellFormed`, freshly-defined vars are not in the outer scope. -/
private theorem defUseWellFormed_block_definedVars_notMem_outer
    {outer : Expression.Ident → Bool} {bss : Statements}
    (hwf : Block.defUseWellFormed outer bss = Bool.true)
    {n : Expression.Ident}
    (hn : n ∈ Block.definedVars bss false) : outer n = Bool.false :=
  (defUseWellFormed_definedVars_notMem_outer_aux (Block.sizeOf bss)).2
    outer bss (Nat.le_refl _) hwf n hn

/-! ### Configuration-level isNone invariant

For loops, we need a star-trace argument that handles iteration.  The key
invariant: at every config `c` reachable from `.stmt (.loop ..) ρ₀`, the
"refresh value" of `n` at `c` (computed by ignoring inner block scopes) is
`none`.  More precisely, every enclosing block in `c` has `σ_parent n = none`,
and the innermost env has `.store n = none` UNLESS we're inside a block scope
that will project it away.

We use a simpler invariant based on `outerInv`'s structure: track that
`(σ_outer n) = none` (where `σ_outer` is the loop's parent context) AND
every block scope in `c` has its `σ_parent n = none`.  If those hold, then
when blocks pop (via `step_block_done`), the result `projectStore σ_parent _ n`
is `none`. -/

/-- "n is none-anchored at c":
    `(c.getEnv.store n).isNone` AND every enclosing block in `c` has
    `σ_parent n = none`.  This is the invariant we propagate through trace
    induction for the loop case. -/
private def isNoneAnchored (n : Expression.Ident) : CC → Prop
  | .stmt _ ρ => (ρ.store n).isNone
  | .stmts _ ρ => (ρ.store n).isNone
  | .terminal ρ => (ρ.store n).isNone
  | .exiting _ ρ => (ρ.store n).isNone
  | .block _ σ_parent inner => (σ_parent n).isNone ∧ isNoneAnchored n inner
  | .seq inner _ => isNoneAnchored n inner

/-- `isNoneAnchored n c` implies `(c.getEnv.store n).isNone`. -/
private theorem isNoneAnchored_implies_isNone (n : Expression.Ident) (c : CC)
    (h : isNoneAnchored n c) : (c.getEnv.store n).isNone := by
  match c with
  | .stmt _ _ => exact h
  | .stmts _ _ => exact h
  | .terminal _ => exact h
  | .exiting _ _ => exact h
  | .block _ _ inner =>
    obtain ⟨_, hinner⟩ := h
    show (inner.getEnv.store n).isNone
    exact isNoneAnchored_implies_isNone n inner hinner
  | .seq inner _ =>
    show (inner.getEnv.store n).isNone
    exact isNoneAnchored_implies_isNone n inner h

/-- Single-step preserves `isNoneAnchored n` when `n` is outside the
    "writable" surface: not in `c₁`'s `Stmt.modifiedVars` (modifications) and
    `n` is also not init'd at the current step.  In particular, for any
    statement where the modifiedVars covers all writes (excluding scoped inits),
    `isNoneAnchored` is preserved. -/
private theorem step_preserves_isNoneAnchored
    {n : Expression.Ident} {a b : CC}
    (hstep : StepStmt Expression (EvalCommand π φ) (EvalPureFunc φ) a b)
    (hinv : isNoneAnchored n a)
    (hnoWrite : n ∉ Config.touchedVarsSet a) :
    isNoneAnchored n b := by
  induction hstep with
  | step_cmd heval =>
    -- a = .stmt (.cmd c) ρ, b = .terminal ρ' with ρ'.store = σ'
    -- hnoWrite: n ∉ Stmt.modifiedVars (.cmd c) ++ Stmt.definedVars (.cmd c) false
    -- Use evalCommand_store_frame_stmt: σ' n = ρ.store n.
    simp only [isNoneAnchored, Config.getEnv] at hinv ⊢
    have hmod : n ∉ Stmt.modifiedVars (.cmd ‹Command›) :=
      fun hmem => hnoWrite (by
        simp only [Config.touchedVarsSet, List.mem_append]; exact .inl hmem)
    have hdef : n ∉ Stmt.definedVars (.cmd ‹Command›) false :=
      fun hmem => hnoWrite (by
        simp only [Config.touchedVarsSet, List.mem_append]; exact .inr hmem)
    have hframe := evalCommand_store_frame_stmt (π := π) (φ := φ) heval hmod hdef
    rw [Option.isNone_iff_eq_none]
    rw [hframe]
    exact Option.isNone_iff_eq_none.mp hinv
  | step_block =>
    -- a = .stmt (.block l ss md) ρ, b = .block (.some l) ρ.store (.stmts ss ρ)
    -- hinv : (ρ.store n).isNone
    -- goal isNoneAnchored n b = ⟨(ρ.store n).isNone, isNoneAnchored n (.stmts ss ρ)⟩
    simp only [isNoneAnchored] at hinv ⊢
    exact ⟨hinv, hinv⟩
  | step_ite_true _ _ =>
    simp only [isNoneAnchored] at hinv ⊢
    exact ⟨hinv, hinv⟩
  | step_ite_false _ _ =>
    simp only [isNoneAnchored] at hinv ⊢
    exact ⟨hinv, hinv⟩
  | step_ite_nondet_true =>
    simp only [isNoneAnchored] at hinv ⊢
    exact ⟨hinv, hinv⟩
  | step_ite_nondet_false =>
    simp only [isNoneAnchored] at hinv ⊢
    exact ⟨hinv, hinv⟩
  | step_loop_enter _ _ _ _ _ =>
    -- a = .stmt (.loop ..) ρ, b = .seq (.block .none ρ.store (.stmts body ρ')) [loop]
    -- where ρ' = { ρ with hasFailure := ... }, so ρ'.store = ρ.store.
    -- hinv : (ρ.store n).isNone.  goal: isNoneAnchored n b = isNoneAnchored n (.block ...) = ⟨(ρ.store n).isNone, (ρ'.store n).isNone⟩
    simp only [isNoneAnchored] at hinv ⊢
    exact ⟨hinv, hinv⟩
  | step_loop_exit _ _ _ _ =>
    -- b = .terminal { ρ with hasFailure := ... }
    simp only [isNoneAnchored] at hinv ⊢
    exact hinv
  | step_loop_nondet_enter _ _ =>
    simp only [isNoneAnchored] at hinv ⊢
    exact ⟨hinv, hinv⟩
  | step_loop_nondet_exit _ _ =>
    simp only [isNoneAnchored] at hinv ⊢
    exact hinv
  | step_exit =>
    simp only [isNoneAnchored] at hinv ⊢
    exact hinv
  | step_funcDecl =>
    simp only [isNoneAnchored, Config.getEnv] at hinv ⊢
    exact hinv
  | step_typeDecl =>
    simp only [isNoneAnchored] at hinv ⊢
    exact hinv
  | step_stmts_nil =>
    simp only [isNoneAnchored] at hinv ⊢
    exact hinv
  | step_stmts_cons =>
    simp only [isNoneAnchored] at hinv ⊢
    exact hinv
  | step_seq_inner _ ih =>
    simp only [isNoneAnchored] at hinv ⊢
    exact ih hinv (fun hmem => hnoWrite (by
      simp only [Config.touchedVarsSet, List.mem_append]
      left; left; exact hmem))
  | step_seq_done =>
    simp only [isNoneAnchored] at hinv ⊢
    exact hinv
  | step_seq_exit =>
    simp only [isNoneAnchored] at hinv ⊢
    exact hinv
  | step_block_body _ ih =>
    simp only [isNoneAnchored] at hinv ⊢
    obtain ⟨hpar, hinner⟩ := hinv
    refine ⟨hpar, ih hinner ?_⟩
    simp only [Config.touchedVarsSet] at hnoWrite
    exact hnoWrite
  | step_block_done =>
    -- a = .block l σ_parent (.terminal ρ'), hinv = ⟨(σ_parent n).isNone, (ρ'.store n).isNone⟩
    -- b = .terminal { ρ' with store := projectStore σ_parent ρ'.store }
    -- goal: ((projectStore σ_parent ρ'.store) n).isNone
    simp only [isNoneAnchored, Config.getEnv] at hinv ⊢
    obtain ⟨hpar, _⟩ := hinv
    simp only [projectStore]
    rw [if_neg (by rw [Option.not_isSome_iff_eq_none]; exact Option.isNone_iff_eq_none.mp hpar)]
    rfl
  | step_block_exit_match _ =>
    simp only [isNoneAnchored, Config.getEnv] at hinv ⊢
    obtain ⟨hpar, _⟩ := hinv
    simp only [projectStore]
    rw [if_neg (by rw [Option.not_isSome_iff_eq_none]; exact Option.isNone_iff_eq_none.mp hpar)]
    rfl
  | step_block_exit_mismatch _ =>
    simp only [isNoneAnchored, Config.getEnv] at hinv ⊢
    obtain ⟨hpar, _⟩ := hinv
    simp only [projectStore]
    rw [if_neg (by rw [Option.not_isSome_iff_eq_none]; exact Option.isNone_iff_eq_none.mp hpar)]
    rfl

/-- Star version of `step_preserves_isNoneAnchored`. -/
private theorem stmt_terminal_preserves_isNone
    {s : Statement} {ρ₀ ρ₁ : Env Expression}
    (hstar : CoreStar π φ (.stmt s ρ₀) (.terminal ρ₁))
    (hnofd : Stmt.noFuncDecl s = Bool.true)
    (n : Expression.Ident)
    (hnone : (ρ₀.store n).isNone)
    (hnmod : n ∉ Stmt.modifiedVars s)
    (hndef_true : n ∉ Stmt.definedVars s true) :
    (ρ₁.store n).isNone := by
  match s with
  | .cmd c =>
    -- For .cmd, definedVars true = definedVars false, so we use existing frame.
    have hndef_false : n ∉ Stmt.definedVars (.cmd c) false := by
      simpa [Stmt.definedVars] using hndef_true
    have hxnot : n ∉ Config.touchedVarsSet (.stmt (.cmd c) ρ₀) := by
      simp only [Config.touchedVarsSet, List.mem_append]
      rintro (hmod | hdef)
      · exact hnmod hmod
      · exact hndef_false hdef
    have hframe := star_preserves_store_outside_touchedVars_isNone (π := π) (φ := φ)
      hstar n (by simpa [Config.getEnv] using hnone) hxnot
    simp only [Config.getEnv] at hframe
    rw [Option.isNone_iff_eq_none, hframe]
    exact Option.isNone_iff_eq_none.mp hnone
  | .block l bss md =>
    -- Trace: step_block + (block_reaches_terminal: inner reaches terminal/exiting,
    -- ρ₁ = projectStore ρ₀.store ρ_inner.store).  In both projection cases,
    -- (projectStore ρ₀.store ρ_inner.store n) = if (ρ₀.store n).isSome then ... else none.
    -- Since hnone : (ρ₀.store n).isNone, the result is `none`.
    cases hstar with
    | step _ mid _ h1 r1 =>
      cases h1
      -- mid = .block (.some l) ρ₀.store (.stmts bss ρ₀)
      match block_reaches_terminal (P := Expression)
          (EvalCmd := EvalCommand π φ) (extendEval := EvalPureFunc φ) r1 with
      | .inl ⟨ρ_inner, _, heq⟩ =>
        rw [heq]
        show (projectStore ρ₀.store ρ_inner.store n).isNone
        simp only [projectStore]
        rw [if_neg (by rw [Option.not_isSome_iff_eq_none]; exact Option.isNone_iff_eq_none.mp hnone)]
        rfl
      | .inr ⟨_, ρ_inner, _, heq⟩ =>
        rw [heq]
        show (projectStore ρ₀.store ρ_inner.store n).isNone
        simp only [projectStore]
        rw [if_neg (by rw [Option.not_isSome_iff_eq_none]; exact Option.isNone_iff_eq_none.mp hnone)]
        rfl
  | .ite c tss ess md =>
    -- Trace begins with step_ite_*, leading to .block .none ρ₀.store (.stmts ?? ρ₀).
    -- Same projection argument as for .block.
    cases hstar with
    | step _ mid _ h1 r1 =>
      cases h1 with
      | step_ite_true _ _ | step_ite_false _ _ | step_ite_nondet_true | step_ite_nondet_false =>
        match block_reaches_terminal (P := Expression)
            (EvalCmd := EvalCommand π φ) (extendEval := EvalPureFunc φ) r1 with
        | .inl ⟨ρ_inner, _, heq⟩ =>
          rw [heq]
          show (projectStore ρ₀.store ρ_inner.store n).isNone
          simp only [projectStore]
          rw [if_neg (by rw [Option.not_isSome_iff_eq_none]; exact Option.isNone_iff_eq_none.mp hnone)]
          rfl
        | .inr ⟨_, ρ_inner, _, heq⟩ =>
          rw [heq]
          show (projectStore ρ₀.store ρ_inner.store n).isNone
          simp only [projectStore]
          rw [if_neg (by rw [Option.not_isSome_iff_eq_none]; exact Option.isNone_iff_eq_none.mp hnone)]
          rfl
  | .loop g m inv body md =>
    -- For loops, the trace either:
    --   (a) takes step_loop_exit immediately: store unchanged.
    --   (b) takes step_loop_enter, leading to a seq with a block-wrapped body.
    --       The body's iteration runs in `.block .none ρ_iter.store ...`; the
    --       block-exit projection drops `n` to `none` since `(ρ_iter.store n).isNone`.
    --       The recursive [loop] then runs from the projected env, where `n`
    --       remains `none`.  Trace-length induction over `ReflTransT`.
    have hstarT := reflTrans_to_T hstar
    -- Strong induction on trace length.
    suffices ∀ (n_steps : Nat) (ρ₀ ρ₁ : Env Expression),
        (ρ₀.store n).isNone →
        ∀ (h : ReflTransT (StepStmt Expression (EvalCommand π φ) (EvalPureFunc φ))
            (.stmt (.loop g m inv body md) ρ₀) (.terminal ρ₁)),
          h.len ≤ n_steps → (ρ₁.store n).isNone by
      exact this hstarT.len ρ₀ ρ₁ hnone hstarT (Nat.le_refl _)
    clear hstar hstarT ρ₀ ρ₁ hnone
    intro n_steps
    induction n_steps with
    | zero =>
      intro ρ₀ ρ₁ _ hT hlen
      match hT, hlen with
      | .step _ _ _ _ _, hlen => simp [ReflTransT.len] at hlen
    | succ k ih =>
      intro ρ₀ ρ₁ hnone₀ hT hlen
      -- Case-split on the first step of the loop trace.
      match hT with
      | .step _ _ _ hstep1 hrest =>
        cases hstep1 with
        | step_loop_exit _ _ _ _ =>
          -- ρ₁ = { ρ₀ with hasFailure := ρ₀.hasFailure || ... }, store unchanged.
          match hrest with
          | .refl _ => exact hnone₀
          | .step _ _ _ h _ => exact nomatch h
        | step_loop_nondet_exit _ _ =>
          match hrest with
          | .refl _ => exact hnone₀
          | .step _ _ _ h _ => exact nomatch h
        | step_loop_enter _ _ _ _ _ =>
          -- successor is .seq (.block .none ρ₀.store (.stmts body ρ₀'))
          --                     [.loop (.det g) m inv body md].
          have hlen_rest : hrest.len ≤ k := by simp only [ReflTransT.len] at hlen; omega
          have ⟨ρ_mid, hT_block, hT_tail, hlen_split⟩ := seqT_reaches_terminal hrest
          have ⟨ρ_inner, ⟨hT_inner, hlen_inner⟩, heq⟩ := blockT_none_reaches_terminal π φ hT_block
          have hnone_mid : (ρ_mid.store n).isNone := by
            rw [heq]
            show (projectStore ρ₀.store ρ_inner.store n).isNone
            simp only [projectStore]
            rw [if_neg (by rw [Option.not_isSome_iff_eq_none]; exact Option.isNone_iff_eq_none.mp hnone₀)]
            rfl
          match hT_tail, hlen_split with
          | .step _ _ _ .step_stmts_cons hrest', hlen_split =>
            have hlen_rest' : hrest'.len < hrest.len := by
              simp only [ReflTransT.len] at hlen_split ⊢; omega
            have ⟨ρ_mid', hT_loop', hT_nil, hlen_split'⟩ := seqT_reaches_terminal hrest'
            have hρ_eq : ρ_mid' = ρ₁ := by
              match hT_nil with
              | .step _ _ _ .step_stmts_nil hrr =>
                match hrr with
                | .refl _ => rfl
                | .step _ _ _ h _ => exact nomatch h
            subst hρ_eq
            have hlen_loop : hT_loop'.len ≤ k := by omega
            exact ih ρ_mid ρ_mid' hnone_mid hT_loop' hlen_loop
        | step_loop_nondet_enter _ _ =>
          have hlen_rest : hrest.len ≤ k := by simp only [ReflTransT.len] at hlen; omega
          have ⟨ρ_mid, hT_block, hT_tail, hlen_split⟩ := seqT_reaches_terminal hrest
          have ⟨ρ_inner, ⟨hT_inner, hlen_inner⟩, heq⟩ := blockT_none_reaches_terminal π φ hT_block
          have hnone_mid : (ρ_mid.store n).isNone := by
            rw [heq]
            show (projectStore ρ₀.store ρ_inner.store n).isNone
            simp only [projectStore]
            rw [if_neg (by rw [Option.not_isSome_iff_eq_none]; exact Option.isNone_iff_eq_none.mp hnone₀)]
            rfl
          match hT_tail, hlen_split with
          | .step _ _ _ .step_stmts_cons hrest', hlen_split =>
            have hlen_rest' : hrest'.len < hrest.len := by
              simp only [ReflTransT.len] at hlen_split ⊢; omega
            have ⟨ρ_mid', hT_loop', hT_nil, hlen_split'⟩ := seqT_reaches_terminal hrest'
            have hρ_eq : ρ_mid' = ρ₁ := by
              match hT_nil with
              | .step _ _ _ .step_stmts_nil hrr =>
                match hrr with
                | .refl _ => rfl
                | .step _ _ _ h _ => exact nomatch h
            subst hρ_eq
            have hlen_loop : hT_loop'.len ≤ k := by omega
            exact ih ρ_mid ρ_mid' hnone_mid hT_loop' hlen_loop
  | .exit l md =>
    -- .exit cannot reach .terminal: it always reaches .exiting.
    exfalso
    cases hstar with
    | step _ _ _ h1 r1 =>
      cases h1
      cases r1 with
      | step _ _ _ h2 _ => cases h2
  | .funcDecl decl md => exact absurd hnofd (by simp [Stmt.noFuncDecl])
  | .typeDecl tc md =>
    -- Trace = step_typeDecl + refl, ρ₁ = ρ₀.
    cases hstar with
    | step _ _ _ h1 r1 =>
      cases h1
      cases r1 with
      | refl => exact hnone
      | step _ _ _ h2 _ => cases h2

/-- For compound `s` (`.block`/`.ite`/`.loop`), terminal trace preserves
    `(ρ₀.store n).isNone` regardless of `n`'s status in `modifiedVars`/
    `definedVars`.  The argument: each of these begins with a step that wraps
    the inner body in `.block .none ρ₀.store ...`, and the block-exit projection
    drops `n` to `none` since `(ρ₀.store n).isNone`.  For `.loop`, this
    extends through trace-length induction. -/
private theorem stmt_compound_terminal_preserves_isNone
    {s : Statement} {ρ₀ ρ₁ : Env Expression}
    (hstar : CoreStar π φ (.stmt s ρ₀) (.terminal ρ₁))
    (hcompound : ∀ c, s ≠ .cmd c) (hnoexit : ∀ l md, s ≠ .exit l md)
    (hnofd : Stmt.noFuncDecl s = Bool.true)
    (n : Expression.Ident)
    (hnone : (ρ₀.store n).isNone) :
    (ρ₁.store n).isNone := by
  match s with
  | .cmd c => exact absurd rfl (hcompound c)
  | .exit l md => exact absurd rfl (hnoexit l md)
  | .funcDecl _ _ => exact absurd hnofd (by simp [Stmt.noFuncDecl])
  | .typeDecl tc md =>
    cases hstar with
    | step _ _ _ h1 r1 =>
      cases h1
      cases r1 with
      | refl => exact hnone
      | step _ _ _ h2 _ => cases h2
  | .block l bss md =>
    cases hstar with
    | step _ mid _ h1 r1 =>
      cases h1
      match block_reaches_terminal (P := Expression)
          (EvalCmd := EvalCommand π φ) (extendEval := EvalPureFunc φ) r1 with
      | .inl ⟨ρ_inner, _, heq⟩ =>
        rw [heq]
        show (projectStore ρ₀.store ρ_inner.store n).isNone
        simp only [projectStore]
        rw [if_neg (by rw [Option.not_isSome_iff_eq_none]; exact Option.isNone_iff_eq_none.mp hnone)]
        rfl
      | .inr ⟨_, ρ_inner, _, heq⟩ =>
        rw [heq]
        show (projectStore ρ₀.store ρ_inner.store n).isNone
        simp only [projectStore]
        rw [if_neg (by rw [Option.not_isSome_iff_eq_none]; exact Option.isNone_iff_eq_none.mp hnone)]
        rfl
  | .ite c tss ess md =>
    cases hstar with
    | step _ mid _ h1 r1 =>
      cases h1 with
      | step_ite_true _ _ | step_ite_false _ _ | step_ite_nondet_true | step_ite_nondet_false =>
        match block_reaches_terminal (P := Expression)
            (EvalCmd := EvalCommand π φ) (extendEval := EvalPureFunc φ) r1 with
        | .inl ⟨ρ_inner, _, heq⟩ =>
          rw [heq]
          show (projectStore ρ₀.store ρ_inner.store n).isNone
          simp only [projectStore]
          rw [if_neg (by rw [Option.not_isSome_iff_eq_none]; exact Option.isNone_iff_eq_none.mp hnone)]
          rfl
        | .inr ⟨_, ρ_inner, _, heq⟩ =>
          rw [heq]
          show (projectStore ρ₀.store ρ_inner.store n).isNone
          simp only [projectStore]
          rw [if_neg (by rw [Option.not_isSome_iff_eq_none]; exact Option.isNone_iff_eq_none.mp hnone)]
          rfl
  | .loop g m inv body md =>
    have hstarT := reflTrans_to_T hstar
    suffices ∀ (n_steps : Nat) (ρ₀ ρ₁ : Env Expression),
        (ρ₀.store n).isNone →
        ∀ (h : ReflTransT (StepStmt Expression (EvalCommand π φ) (EvalPureFunc φ))
            (.stmt (.loop g m inv body md) ρ₀) (.terminal ρ₁)),
          h.len ≤ n_steps → (ρ₁.store n).isNone by
      exact this hstarT.len ρ₀ ρ₁ hnone hstarT (Nat.le_refl _)
    clear hstar hstarT ρ₀ ρ₁ hnone
    intro n_steps
    induction n_steps with
    | zero =>
      intro ρ₀ ρ₁ _ hT hlen
      match hT, hlen with
      | .step _ _ _ _ _, hlen => simp [ReflTransT.len] at hlen
    | succ k ih =>
      intro ρ₀ ρ₁ hnone₀ hT hlen
      match hT with
      | .step _ _ _ hstep1 hrest =>
        cases hstep1 with
        | step_loop_exit _ _ _ _ =>
          match hrest with
          | .refl _ => exact hnone₀
          | .step _ _ _ h _ => exact nomatch h
        | step_loop_nondet_exit _ _ =>
          match hrest with
          | .refl _ => exact hnone₀
          | .step _ _ _ h _ => exact nomatch h
        | step_loop_enter _ _ _ _ _ =>
          have hlen_rest : hrest.len ≤ k := by simp only [ReflTransT.len] at hlen; omega
          have ⟨ρ_mid, hT_block, hT_tail, hlen_split⟩ := seqT_reaches_terminal hrest
          have ⟨ρ_inner, ⟨hT_inner, hlen_inner⟩, heq⟩ := blockT_none_reaches_terminal π φ hT_block
          have hnone_mid : (ρ_mid.store n).isNone := by
            rw [heq]
            show (projectStore ρ₀.store ρ_inner.store n).isNone
            simp only [projectStore]
            rw [if_neg (by rw [Option.not_isSome_iff_eq_none]; exact Option.isNone_iff_eq_none.mp hnone₀)]
            rfl
          match hT_tail, hlen_split with
          | .step _ _ _ .step_stmts_cons hrest', hlen_split =>
            have hlen_rest' : hrest'.len < hrest.len := by
              simp only [ReflTransT.len] at hlen_split ⊢; omega
            have ⟨ρ_mid', hT_loop', hT_nil, hlen_split'⟩ := seqT_reaches_terminal hrest'
            have hρ_eq : ρ_mid' = ρ₁ := by
              match hT_nil with
              | .step _ _ _ .step_stmts_nil hrr =>
                match hrr with
                | .refl _ => rfl
                | .step _ _ _ h _ => exact nomatch h
            subst hρ_eq
            have hlen_loop : hT_loop'.len ≤ k := by omega
            exact ih ρ_mid ρ_mid' hnone_mid hT_loop' hlen_loop
        | step_loop_nondet_enter _ _ =>
          have hlen_rest : hrest.len ≤ k := by simp only [ReflTransT.len] at hlen; omega
          have ⟨ρ_mid, hT_block, hT_tail, hlen_split⟩ := seqT_reaches_terminal hrest
          have ⟨ρ_inner, ⟨hT_inner, hlen_inner⟩, heq⟩ := blockT_none_reaches_terminal π φ hT_block
          have hnone_mid : (ρ_mid.store n).isNone := by
            rw [heq]
            show (projectStore ρ₀.store ρ_inner.store n).isNone
            simp only [projectStore]
            rw [if_neg (by rw [Option.not_isSome_iff_eq_none]; exact Option.isNone_iff_eq_none.mp hnone₀)]
            rfl
          match hT_tail, hlen_split with
          | .step _ _ _ .step_stmts_cons hrest', hlen_split =>
            have hlen_rest' : hrest'.len < hrest.len := by
              simp only [ReflTransT.len] at hlen_split ⊢; omega
            have ⟨ρ_mid', hT_loop', hT_nil, hlen_split'⟩ := seqT_reaches_terminal hrest'
            have hρ_eq : ρ_mid' = ρ₁ := by
              match hT_nil with
              | .step _ _ _ .step_stmts_nil hrr =>
                match hrr with
                | .refl _ => rfl
                | .step _ _ _ h _ => exact nomatch h
            subst hρ_eq
            have hlen_loop : hT_loop'.len ≤ k := by omega
            exact ih ρ_mid ρ_mid' hnone_mid hT_loop' hlen_loop

/-! ### Note: The old `_disjoint` bridges (cons_head_disjoint, ite_left_disjoint,
    ite_right_disjoint) have been removed. The `toBlock_ite_left/right` and
    `toStmt_head` lemmas now use `defUseOk` directly via
    `defUseWellFormed_modGetVars_implies_outer`, eliminating the need for
    disjointness hypotheses entirely. -/

/-- `BlockInitEnvWF ss ρ₁` follows from `BlockInitEnvWF (s :: ss) ρ₀` after `s`
    ran from `ρ₀` to `ρ₁`, using the block's own `defUseOk` to discharge the
    side conditions.  This avoids the need for callers to supply a `hdisj`
    hypothesis or a `hnewVars_in_def` proof. -/
private theorem BlockInitEnvWF.toBlock_tail_via_defUseOk {reserved : List String}
    {s : Statement} {ss : Statements} {ρ₀ ρ₁ : Env Expression}
    (h : BlockInitEnvWF reserved (s :: ss) ρ₀)
    (hstar : CoreStar π φ (.stmt s ρ₀) (.terminal ρ₁))
    (hnofd_s : Stmt.noFuncDecl s = Bool.true) :
    BlockInitEnvWF reserved ss ρ₁ where
  readWritesDefined n hn hnd := by
    -- n ∈ Block.touchedVars ss, n ∉ Block.definedVars ss false → (ρ₁.store n).isSome.
    -- defUseOk on (s :: ss) extends with definedVars s true for tail.  So tail's
    -- well-formedness against (fun m => (ρ₀.store m).isSome || decide (m ∈ defVars s true)).
    have ⟨_, htail_def⟩ := defUseWellFormed_cons h.defUseOk
    have hmod_or_get :
        n ∈ Block.modifiedVars ss ∨ n ∈ Block.getVars ss := by
      simp only [Block.touchedVars, Block.modifiedOrDefinedVars, List.mem_append] at hn
      rcases hn with ((hm | hd_true) | hg)
      · exact .inl hm
      · exact absurd (block_definedVars_true_subset_false ss n hd_true) hnd
      · exact .inr hg
    -- Apply: tail well-formedness gives extended-outer n = true.
    have houter :
        ((ρ₀.store n).isSome || decide (n ∈ Stmt.definedVars s true)) = Bool.true :=
      defUseWellFormed_modGetVars_implies_outer htail_def hmod_or_get hnd
    rw [Bool.or_eq_true] at houter
    rcases houter with h₀ | hd_true
    · -- (ρ₀.store n).isSome - propagated by trace.
      have := stmt_star_preserves_isSome (π := π) (φ := φ) s ρ₀ _ hstar n h₀
      simpa [Config.getEnv] using this
    · -- n ∈ Stmt.definedVars s true: head's def made it isSome.
      have hmem : n ∈ Stmt.definedVars s true := by
        simp only [decide_eq_true_eq] at hd_true; exact hd_true
      have hdefsNone : ∀ m ∈ Stmt.definedVars s true, (ρ₀.store m).isNone := fun m hm =>
        h.defsUndefined m (by
          simp only [Block.definedVars, List.mem_append]; left
          exact stmt_definedVars_true_subset_false s m hm)
      exact stmt_definedVars_true_isSome_after (π := π) (φ := φ) hstar hnofd_s hdefsNone n hmem
  defsUndefined n hn := by
    -- n ∈ Block.definedVars ss false → (ρ₁.store n).isNone.
    -- From `defUseOk` on tail, extended-outer n = false, i.e. (ρ₀.store n).isNone
    -- AND n ∉ Stmt.definedVars s true.
    have ⟨hhead_def, htail_def⟩ := defUseWellFormed_cons h.defUseOk
    have houter_false :
        ((ρ₀.store n).isSome || decide (n ∈ Stmt.definedVars s true)) = Bool.false :=
      defUseWellFormed_block_definedVars_notMem_outer htail_def hn
    rw [Bool.or_eq_false_iff] at houter_false
    obtain ⟨hsome_false, hd_false⟩ := houter_false
    have hnone₀ : (ρ₀.store n).isNone := by
      cases hx : ρ₀.store n <;> simp_all
    have hndef_true : n ∉ Stmt.definedVars s true := by
      simp only [decide_eq_false_iff_not] at hd_false; exact hd_false
    -- Case-split on n ∈ Stmt.definedVars s false.
    by_cases hn_def_s : n ∈ Stmt.definedVars s false
    · -- n is inner-defined in compound s.  The compound-exit projection scrubs
      -- n back to none: stmt_compound_terminal_preserves_isNone requires only
      -- (ρ₀.store n).isNone.  s must be compound since for .cmd, def_true = def_false.
      apply stmt_compound_terminal_preserves_isNone (π := π) (φ := φ) hstar
      · intro c heq; subst heq
        simp only [Stmt.definedVars] at hn_def_s hndef_true
        exact hndef_true hn_def_s
      · intro l md heq; subst heq
        simp only [Stmt.definedVars] at hn_def_s
        exact List.not_mem_nil hn_def_s
      · exact hnofd_s
      · exact hnone₀
    · -- n ∉ Stmt.definedVars s false: then we can derive n ∉ Stmt.modifiedVars s
      -- (else defUseOk forces outer = true, contradicting hnone₀).
      have hnmod : n ∉ Stmt.modifiedVars s := by
        intro hmod
        have houter_true : ((ρ₀.store n).isSome) = Bool.true :=
          defUseWellFormed_touched_notDef_implies_outer hhead_def (.inl hmod) hn_def_s
        have heq : ρ₀.store n = none := Option.isNone_iff_eq_none.mp hnone₀
        rw [heq] at houter_true
        cases houter_true
      exact stmt_terminal_preserves_isNone (π := π) (φ := φ) hstar hnofd_s n hnone₀ hnmod hndef_true
  definedVarsNotReserved n hn p hp := h.definedVarsNotReserved n (by
    show n ∈ Block.definedVars (s :: ss) false
    simp only [Block.definedVars, List.mem_append]; right; exact hn) p hp
  reservedFresh n hsome₁ p hp := by
    by_cases hsome₀ : (ρ₀.store n).isSome
    · exact h.reservedFresh n hsome₀ p hp
    · have hnone : (ρ₀.store n).isNone := Option.not_isSome_iff_eq_none.mp hsome₀ ▸ rfl
      -- Need: n ∈ Stmt.definedVars s true (to apply head's definedVarsNotReserved-style).
      -- If (ρ₁.store n).isSome but (ρ₀.store n).isNone, then by no-fresh-creation outside
      -- definedVars, n must be in Stmt.definedVars s true (transitively).
      -- This is `stmt_definedVars_true_or_isNone_after`: its converse direction.
      -- Approach: split on n ∈ Stmt.definedVars s true.
      by_cases hn_def_true : n ∈ Stmt.definedVars s true
      · apply h.definedVarsNotReserved n _ p hp
        show n ∈ Block.definedVars (s :: ss) false
        simp only [Block.definedVars, List.mem_append]; left
        exact stmt_definedVars_true_subset_false s n hn_def_true
      · -- (ρ₁.store n).isSome but (ρ₀.store n).isNone and n ∉ Stmt.definedVars s true.
        -- Goal: contradiction.  Strategy: show (ρ₁.store n).isNone by case-split on
        -- n ∈ Stmt.definedVars s false.
        exfalso
        have ⟨hhead_def, _⟩ := defUseWellFormed_cons h.defUseOk
        have hres : (ρ₁.store n).isNone := by
          by_cases hn_def_s : n ∈ Stmt.definedVars s false
          · -- Inner-scoped def in compound s: projection scrubs n back to none.
            apply stmt_compound_terminal_preserves_isNone (π := π) (φ := φ) hstar
            · intro c heq; subst heq
              simp only [Stmt.definedVars] at hn_def_s hn_def_true
              exact hn_def_true hn_def_s
            · intro l md heq; subst heq
              simp only [Stmt.definedVars] at hn_def_s
              exact List.not_mem_nil hn_def_s
            · exact hnofd_s
            · exact hnone
          · have hnmod : n ∉ Stmt.modifiedVars s := by
              intro hmod
              have houter_true : ((ρ₀.store n).isSome) = Bool.true :=
                defUseWellFormed_touched_notDef_implies_outer hhead_def (.inl hmod) hn_def_s
              have heq : ρ₀.store n = none := Option.isNone_iff_eq_none.mp hnone
              rw [heq] at houter_true
              cases houter_true
            exact stmt_terminal_preserves_isNone (π := π) (φ := φ) hstar hnofd_s n hnone hnmod hn_def_true
        rw [Option.isNone_iff_eq_none] at hres
        rw [hres] at hsome₁
        cases hsome₁
  wfBool := by
    have heval : ρ₁.eval = ρ₀.eval :=
      smallStep_noFuncDecl_preserves_eval Expression (EvalCommand π φ) (EvalPureFunc φ)
        s ρ₀ ρ₁ hnofd_s hstar
    rw [heval]; exact h.wfBool
  wfVal := by
    have heval : ρ₁.eval = ρ₀.eval :=
      smallStep_noFuncDecl_preserves_eval Expression (EvalCommand π φ) (EvalPureFunc φ)
        s ρ₀ ρ₁ hnofd_s hstar
    rw [heval]; exact h.wfVal
  wfVar := by
    have heval : ρ₁.eval = ρ₀.eval :=
      smallStep_noFuncDecl_preserves_eval Expression (EvalCommand π φ) (EvalPureFunc φ)
        s ρ₀ ρ₁ hnofd_s hstar
    rw [heval]; exact h.wfVar
  evalCong := by
    have heval : ρ₁.eval = ρ₀.eval :=
      smallStep_noFuncDecl_preserves_eval Expression (EvalCommand π φ) (EvalPureFunc φ)
        s ρ₀ ρ₁ hnofd_s hstar
    rw [heval]; exact h.evalCong
  exprCongr := by
    have heval : ρ₁.eval = ρ₀.eval :=
      smallStep_noFuncDecl_preserves_eval Expression (EvalCommand π φ) (EvalPureFunc φ)
        s ρ₀ ρ₁ hnofd_s hstar
    rw [heval]; exact h.exprCongr
  defUseOk := by
    have ⟨_, htail⟩ := defUseWellFormed_cons h.defUseOk
    rw [defUseWellFormed_block_congr (fun n => ?_) ss] at htail
    · exact htail
    · have hdefsNone : ∀ m ∈ Stmt.definedVars s true, (ρ₀.store m).isNone := fun m hm =>
        h.defsUndefined m (by
          simp only [Block.definedVars, List.mem_append]; left
          exact stmt_definedVars_true_subset_false s m hm)
      cases h₀ : (ρ₀.store n).isSome
      case true =>
        simp only [Bool.true_or]
        have := stmt_star_preserves_isSome (π := π) (φ := φ) s ρ₀ _ hstar n h₀
        simpa [Config.getEnv] using this
      case false =>
        simp only [Bool.false_or]
        have hnone₀ : (ρ₀.store n).isNone := by
          cases hx : ρ₀.store n <;> simp_all
        cases hd : decide (n ∈ Stmt.definedVars s true)
        case true =>
          have hmem : n ∈ Stmt.definedVars s true := by
            simp [decide_eq_true_eq] at hd; exact hd
          exact (stmt_definedVars_true_isSome_after (π := π) (φ := φ) hstar hnofd_s hdefsNone n hmem).symm
        case false =>
          -- (ρ₀.store n).isNone ∧ n ∉ Stmt.definedVars s true → goal: false = (ρ₁.store n).isSome
          have hnotmem : n ∉ Stmt.definedVars s true := by
            simp [decide_eq_true_eq] at hd; exact hd
          apply Eq.symm
          have ⟨hhead_def, _⟩ := defUseWellFormed_cons h.defUseOk
          have hres : (ρ₁.store n).isNone := by
            by_cases hn_def_s : n ∈ Stmt.definedVars s false
            · -- Inner-scoped def in compound s: projection scrubs n back to none.
              apply stmt_compound_terminal_preserves_isNone (π := π) (φ := φ) hstar
              · intro c heq; subst heq
                simp only [Stmt.definedVars] at hn_def_s hnotmem
                exact hnotmem hn_def_s
              · intro l md heq; subst heq
                simp only [Stmt.definedVars] at hn_def_s
                exact List.not_mem_nil hn_def_s
              · exact hnofd_s
              · exact hnone₀
            · have hnmod : n ∉ Stmt.modifiedVars s := by
                intro hmod
                have houter_true : ((ρ₀.store n).isSome) = Bool.true :=
                  defUseWellFormed_touched_notDef_implies_outer hhead_def (.inl hmod) hn_def_s
                have heq : ρ₀.store n = none := Option.isNone_iff_eq_none.mp hnone₀
                rw [heq] at houter_true
                cases houter_true
              exact stmt_terminal_preserves_isNone (π := π) (φ := φ) hstar hnofd_s n hnone₀ hnmod hnotmem
          cases h_eq : (ρ₁.store n).isSome with
          | true => rw [Option.isNone_iff_eq_none] at hres; rw [hres] at h_eq; cases h_eq
          | false => rfl

/-! ## Simulation -/

/-- The prefix that loop-elim claims for its fresh names. Defined here (early)
    so that `simulation`'s and `canfail_simulation`'s signatures can refer to it.
    Any caller invoking `loopElim_overapproximatesAggressive` must include this
    in `reserved`. -/
def loopElimReservedPrefixSig : String := "$__loop"

set_option maxHeartbeats 400000 in
private theorem simulation
    (hwf_ext : WFEvalExtension φ) (sz : Nat)
    (reserved : List String)
    (h_loop_reserved : loopElimReservedPrefixSig ∈ reserved) :
    -- Statement level
    (∀ (σ : LoopElimState) (st : Statement),
      Stmt.sizeOf st ≤ sz →
      Stmt.noFuncDecl st = Bool.true →
      stmtOk σ st →
      ∀ (ρ₀ : Env Expression),
        InitEnvWF reserved st ρ₀ →
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
        BlockInitEnvWF reserved bss ρ₀ →
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
        InitEnvWF reserved st ρ₀ →
        Transform.CanFail (LangCore π φ) st ρ₀ →
        Transform.CanFail (LangCore π φ) (stmtResult σ st) ρ₀)
    ∧
    -- Block CanFail preservation
    (∀ (σ : LoopElimState) (bss : Statements),
      Block.sizeOf bss ≤ sz →
      Block.noFuncDecl bss = Bool.true →
      blockOk σ bss →
      ∀ (ρ₀ : Env Expression),
        BlockInitEnvWF reserved bss ρ₀ →
        CanFailBlock π φ bss ρ₀ →
        CanFailBlock π φ (blockResult σ bss) ρ₀) := by
  induction sz with
  | zero =>
    refine ⟨fun σ st hsz _ _ => ?_, fun σ bss hsz _ _ => ?_,
            fun σ st hsz _ _ => ?_, fun σ bss hsz _ _ => ?_⟩
    · -- Statement-level correctness at sz = 0: no statement has sizeOf 0
      match st with
      | .cmd _ => exact absurd hsz (by simp [Stmt.sizeOf])
      | .block .. => exact absurd hsz (by simp [Stmt.sizeOf])
      | .ite .. => exact absurd hsz (by simp [Stmt.sizeOf])
      | .loop .. => exact absurd hsz (by simp [Stmt.sizeOf])
      | .exit .. => exact absurd hsz (by simp [Stmt.sizeOf])
      | .funcDecl .. => exact absurd hsz (by simp [Stmt.sizeOf])
      | .typeDecl .. => exact absurd hsz (by simp [Stmt.sizeOf])
    · -- Block-level correctness at sz = 0: only [] possible
      match bss with
      | [] =>
        intro ρ₀ _
        rw [blockResult_nil]
        exact ⟨fun ρ' h => .inr (fun _ => h), fun lbl ρ' h => .inr (fun _ => h)⟩
      | _ :: _ => exact absurd hsz (by simp [Block.sizeOf])
    · -- Statement-level CanFail at sz = 0
      match st with
      | .cmd _ => exact absurd hsz (by simp [Stmt.sizeOf])
      | .block .. => exact absurd hsz (by simp [Stmt.sizeOf])
      | .ite .. => exact absurd hsz (by simp [Stmt.sizeOf])
      | .loop .. => exact absurd hsz (by simp [Stmt.sizeOf])
      | .exit .. => exact absurd hsz (by simp [Stmt.sizeOf])
      | .funcDecl .. => exact absurd hsz (by simp [Stmt.sizeOf])
      | .typeDecl .. => exact absurd hsz (by simp [Stmt.sizeOf])
    · -- Block-level CanFail at sz = 0
      match bss with
      | [] =>
        intro ρ₀ _ hcf
        rw [blockResult_nil]
        exact hcf
      | _ :: _ => exact absurd hsz (by simp [Block.sizeOf])
  | succ n ih =>
    refine ⟨?stmt_corr, ?block_corr, ?stmt_cf, ?block_cf⟩
    case stmt_corr =>
      intro σ st hsz hnofd hok ρ₀ hswf
      refine ⟨?term_branch, ?exit_branch⟩
      case term_branch =>
        intro ρ' hreach
        match st with
        | .cmd c =>
          rw [stmtResult_cmd]; exact .inr (fun _ => hreach)
        | .exit l md =>
          -- .exit cannot reach .terminal: it always reaches .exiting
          exact False.elim (by
            cases hreach with
            | step _ _ _ h1 r1 =>
              cases h1 with
              | step_exit =>
                cases r1 with
                | step _ _ _ h2 _ => cases h2)
        | .funcDecl d md =>
          rw [stmtResult_funcDecl]; exact .inr (fun _ => hreach)
        | .typeDecl tc md =>
          rw [stmtResult_typeDecl]; exact .inr (fun _ => hreach)
        | .block l bss md =>
          rw [stmtResult_block]
          have hnofd_bss : Block.noFuncDecl bss = Bool.true := by
            simp [Stmt.noFuncDecl] at hnofd; exact hnofd
          have hsz_bss : Block.sizeOf bss ≤ n := by
            simp [Stmt.sizeOf] at hsz; omega
          -- Use block_reaches_terminal_refined to dispatch
          cases hreach with
          | step _ _ _ h1 r1 =>
            cases h1 with
            | step_block =>
              -- r1 : CoreStar π φ (.block (some l) ρ₀.store (.stmts bss ρ₀)) (.terminal ρ')
              obtain ⟨ρ_inner, hinner_or, hρ'eq⟩ := block_reaches_terminal_refined π φ r1
              cases hinner_or with
              | inl hterm_inner =>
                -- bss terminates at ρ_inner
                have hsim_bss := ih.2.1 σ bss hsz_bss hnofd_bss (stmtOk_block_inner hok) ρ₀
                  (InitEnvWF.toBlock_block hswf)
                match hsim_bss.1 ρ_inner hterm_inner with
                | .inl hcf =>
                  exact .inl (canFailBlock_to_canFail_block π φ l _ md ρ₀ hcf)
                | .inr hok_bss =>
                  refine .inr (fun hnf => ?_)
                  have hnf_inner : ρ_inner.hasFailure = Bool.false := by
                    -- ρ' = projectStore ... preserves hasFailure
                    subst hρ'eq; simp at hnf; exact hnf
                  have hreach_target := hok_bss hnf_inner
                  -- block_wrap_terminal applied to hreach_target gives .terminal {ρ_inner with store := projectStore ρ₀.store ρ_inner.store} = ρ'
                  rw [hρ'eq]
                  exact block_wrap_terminal π φ l _ md ρ₀ ρ_inner hreach_target
              | inr hexit_inner =>
                -- bss exits at l (matching) at ρ_inner
                have hsim_bss := ih.2.1 σ bss hsz_bss hnofd_bss (stmtOk_block_inner hok) ρ₀
                  (InitEnvWF.toBlock_block hswf)
                match hsim_bss.2 l ρ_inner hexit_inner with
                | .inl hcf =>
                  exact .inl (canFailBlock_to_canFail_block π φ l _ md ρ₀ hcf)
                | .inr hok_bss =>
                  refine .inr (fun hnf => ?_)
                  have hnf_inner : ρ_inner.hasFailure = Bool.false := by
                    subst hρ'eq; simp at hnf; exact hnf
                  have hreach_target := hok_bss hnf_inner
                  rw [hρ'eq]
                  exact block_wrap_exiting_match π φ l _ md ρ₀ ρ_inner hreach_target
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
          -- Ite simulation: branches now scoped via .block .none; needs unwrapping.
          cases hreach with
          | step _ _ _ h1 r1 =>
            cases h1 with
            | step_ite_true hcond hwfb' =>
              have r1T := reflTrans_to_T r1
              have ⟨ρ_inner, ⟨hterm_T, _⟩, heq⟩ :=
                blockT_none_reaches_terminal (π := π) (φ := φ) r1T
              have hterm := reflTransT_to_prop hterm_T
              have hsim_tss := ih.2.1 σ tss hsz_tss hnofd_tss (stmtOk_ite_left hok) ρ₀
                (InitEnvWF.toBlock_ite_left hswf)
              match hsim_tss.1 ρ_inner hterm with
              | .inl hcf =>
                obtain ⟨cfg, hfail, hreach_cf⟩ := hcf
                exact .inl ⟨.block .none ρ₀.store cfg,
                  by show cfg.getEnv.hasFailure = Bool.true; exact hfail,
                  .step _ _ _ (.step_ite_true hcond hwfb')
                    (block_inner_star Expression (EvalCommand π φ) (EvalPureFunc φ)
                      _ _ .none ρ₀.store hreach_cf)⟩
              | .inr hok_tss =>
                refine .inr (fun hnf => ?_)
                have hnf_inner : ρ_inner.hasFailure = Bool.false := by
                  subst heq; simp at hnf; exact hnf
                have hreach_target := hok_tss hnf_inner
                subst heq
                exact .step _ _ _ (.step_ite_true hcond hwfb')
                  (ReflTrans_Transitive _ _ _ _
                    (block_inner_star Expression (EvalCommand π φ) (EvalPureFunc φ)
                      _ _ .none ρ₀.store hreach_target)
                    (.step _ _ _ .step_block_done (.refl _)))
            | step_ite_false hcond hwfb' =>
              have r1T := reflTrans_to_T r1
              have ⟨ρ_inner, ⟨hterm_T, _⟩, heq⟩ :=
                blockT_none_reaches_terminal (π := π) (φ := φ) r1T
              have hterm := reflTransT_to_prop hterm_T
              have hsim_ess := ih.2.1 (blockPostState σ tss) ess hsz_ess hnofd_ess
                (stmtOk_ite_right hok) ρ₀ (InitEnvWF.toBlock_ite_right hswf)
              match hsim_ess.1 ρ_inner hterm with
              | .inl hcf =>
                obtain ⟨cfg, hfail, hreach_cf⟩ := hcf
                exact .inl ⟨.block .none ρ₀.store cfg,
                  by show cfg.getEnv.hasFailure = Bool.true; exact hfail,
                  .step _ _ _ (.step_ite_false hcond hwfb')
                    (block_inner_star Expression (EvalCommand π φ) (EvalPureFunc φ)
                      _ _ .none ρ₀.store hreach_cf)⟩
              | .inr hok_ess =>
                refine .inr (fun hnf => ?_)
                have hnf_inner : ρ_inner.hasFailure = Bool.false := by
                  subst heq; simp at hnf; exact hnf
                have hreach_target := hok_ess hnf_inner
                subst heq
                exact .step _ _ _ (.step_ite_false hcond hwfb')
                  (ReflTrans_Transitive _ _ _ _
                    (block_inner_star Expression (EvalCommand π φ) (EvalPureFunc φ)
                      _ _ .none ρ₀.store hreach_target)
                    (.step _ _ _ .step_block_done (.refl _)))
            | step_ite_nondet_true =>
              have r1T := reflTrans_to_T r1
              have ⟨ρ_inner, ⟨hterm_T, _⟩, heq⟩ :=
                blockT_none_reaches_terminal (π := π) (φ := φ) r1T
              have hterm := reflTransT_to_prop hterm_T
              have hsim_tss := ih.2.1 σ tss hsz_tss hnofd_tss (stmtOk_ite_left hok) ρ₀
                (InitEnvWF.toBlock_ite_left hswf)
              match hsim_tss.1 ρ_inner hterm with
              | .inl hcf =>
                obtain ⟨cfg, hfail, hreach_cf⟩ := hcf
                exact .inl ⟨.block .none ρ₀.store cfg,
                  by show cfg.getEnv.hasFailure = Bool.true; exact hfail,
                  .step _ _ _ .step_ite_nondet_true
                    (block_inner_star Expression (EvalCommand π φ) (EvalPureFunc φ)
                      _ _ .none ρ₀.store hreach_cf)⟩
              | .inr hok_tss =>
                refine .inr (fun hnf => ?_)
                have hnf_inner : ρ_inner.hasFailure = Bool.false := by
                  subst heq; simp at hnf; exact hnf
                have hreach_target := hok_tss hnf_inner
                subst heq
                exact .step _ _ _ .step_ite_nondet_true
                  (ReflTrans_Transitive _ _ _ _
                    (block_inner_star Expression (EvalCommand π φ) (EvalPureFunc φ)
                      _ _ .none ρ₀.store hreach_target)
                    (.step _ _ _ .step_block_done (.refl _)))
            | step_ite_nondet_false =>
              have r1T := reflTrans_to_T r1
              have ⟨ρ_inner, ⟨hterm_T, _⟩, heq⟩ :=
                blockT_none_reaches_terminal (π := π) (φ := φ) r1T
              have hterm := reflTransT_to_prop hterm_T
              have hsim_ess := ih.2.1 (blockPostState σ tss) ess hsz_ess hnofd_ess
                (stmtOk_ite_right hok) ρ₀ (InitEnvWF.toBlock_ite_right hswf)
              match hsim_ess.1 ρ_inner hterm with
              | .inl hcf =>
                obtain ⟨cfg, hfail, hreach_cf⟩ := hcf
                exact .inl ⟨.block .none ρ₀.store cfg,
                  by show cfg.getEnv.hasFailure = Bool.true; exact hfail,
                  .step _ _ _ .step_ite_nondet_false
                    (block_inner_star Expression (EvalCommand π φ) (EvalPureFunc φ)
                      _ _ .none ρ₀.store hreach_cf)⟩
              | .inr hok_ess =>
                refine .inr (fun hnf => ?_)
                have hnf_inner : ρ_inner.hasFailure = Bool.false := by
                  subst heq; simp at hnf; exact hnf
                have hreach_target := hok_ess hnf_inner
                subst heq
                exact .step _ _ _ .step_ite_nondet_false
                  (ReflTrans_Transitive _ _ _ _
                    (block_inner_star Expression (EvalCommand π φ) (EvalPureFunc φ)
                      _ _ .none ρ₀.store hreach_target)
                    (.step _ _ _ .step_block_done (.refl _)))
        | .loop guardE measure inv body md =>
          -- LOOP TERMINAL case.
          by_cases hnf' : ρ'.hasFailure = Bool.true
          · -- ρ'.hasFailure = true ⇒ Or.inr's premise is false, giving us a
            -- vacuous implication.
            refine .inr (fun hnf => ?_)
            exfalso; rw [hnf'] at hnf; cases hnf
          · -- ρ'.hasFailure = false.
            have hnf'' : ρ'.hasFailure = Bool.false := by
              cases hh : ρ'.hasFailure
              · rfl
              · exact absurd hh hnf'
            -- Derive ρ₀.hasFailure = false (backwards from ρ').
            have hnf₀ : ρ₀.hasFailure = Bool.false :=
              hasFailure_false_backwards (π := π) (φ := φ) hreach hnf''
            -- noFuncDecl on body
            have hnofd_body : Block.noFuncDecl body = Bool.true := by
              simp [Stmt.noFuncDecl] at hnofd; exact hnofd
            -- Derive `hm_old_fresh : ρ₀.store m_old_ident = none` from
            -- `hreserved`.  The reserved-name check on `ρ₀.store` says any
            -- defined name does NOT have prefix `"$__loop"`; since
            -- `m_old_ident.name = "$__loop_measure_<n>"` clearly has that
            -- prefix, `m_old_ident` cannot be defined at ρ₀.
            have hm_old_fresh : ρ₀.store (HasIdent.ident (P := Expression)
                s!"$__loop_measure_{(StringGenState.gen "loop" σ.gen).fst}") = none := by
              -- Apply hreserved: any defined name does NOT have prefix "$__loop".
              -- Since "$__loop_measure_<n>" has that prefix, it's undefined.
              have hpref : loopElimReservedPrefixSig.toList.isPrefixOf
                  (HasIdent.ident (P := Expression)
                    s!"$__loop_measure_{(StringGenState.gen "loop" σ.gen).fst}").name.toList
                  = Bool.true := by
                show loopElimReservedPrefixSig.toList.isPrefixOf
                  (("$__loop" ++ "_measure_" ++
                    (StringGenState.gen "loop" σ.gen).fst).toList) = Bool.true
                rw [String.toList_append, String.toList_append]
                show loopElimReservedPrefixSig.toList.isPrefixOf
                  (loopElimReservedPrefixSig.toList ++ "_measure_".toList ++
                    (StringGenState.gen "loop" σ.gen).fst.toList) = Bool.true
                rw [List.append_assoc]
                exact isPrefixOf_append_self _ _
              cases h : ρ₀.store (HasIdent.ident (P := Expression)
                  s!"$__loop_measure_{(StringGenState.gen "loop" σ.gen).fst}") with
              | none => rfl
              | some _ =>
                exfalso
                have hsome : (ρ₀.store (HasIdent.ident (P := Expression)
                    s!"$__loop_measure_{(StringGenState.gen "loop" σ.gen).fst}")).isSome := by
                  rw [h]; rfl
                exact hswf.reservedFresh _ hsome loopElimReservedPrefixSig
                  h_loop_reserved hpref
            let _ := hm_old_fresh
            -- Obtain the target's structural decomposition.
            obtain ⟨loop_label, first_iter_label, first_iter_body, then_branch,
                    htgt_eq, hfib_eq⟩ := stmtResult_loop_struct σ guardE measure inv body md hok
            -- Extract `hinv_bool` (each invariant evaluates to tt or ff at ρ₀)
            -- from any of the 4 first-step cases of `hreach`.  This boolean-
            -- valuedness fact is what enables the VC1-failure dichotomy below.
            have hinv_bool : ∀ le ∈ inv,
                ρ₀.eval ρ₀.store le.2 = some HasBool.tt ∨
                ρ₀.eval ρ₀.store le.2 = some HasBool.ff := by
              cases hreach with
              | step _ _ _ h1 _ =>
                cases h1 with
                | step_loop_exit _ hib _ _ => exact hib
                | step_loop_enter _ hib _ _ _ => exact hib
                | step_loop_nondet_exit hib _ => exact hib
                | step_loop_nondet_enter hib _ => exact hib
            -- Now we can split on whether all invariants are tt at ρ₀.
            -- The failure path closes via VC1 (assert canFails); the all-tt
            -- path is left as a focused leaf.
            rw [htgt_eq]
            by_cases hall_tt : ∀ le ∈ inv, ρ₀.eval ρ₀.store le.2 = some HasBool.tt
            · refine .inr (fun _hnf_unused => ?_)
              -- Re-derive hnf'' (already in scope) for clarity in the goal.
              have hnf'_eq : ρ'.hasFailure = Bool.false := hnf''
              suffices h_enter_case : ∀ {hasInvFailure : Bool},
                  hasInvFailure = Bool.false →
                  CoreStar π φ
                    (.seq (.block .none ρ₀.store
                      (.stmts body
                        ({ ρ₀ with hasFailure := ρ₀.hasFailure || hasInvFailure } : Env Expression)))
                      [.loop guardE measure inv body md])
                    (.terminal ρ') →
                  CoreStar π φ (.stmt (.block loop_label
                    [.block first_iter_label first_iter_body {},
                     .ite guardE then_branch [] {}] {}) ρ₀)
                    (.terminal ρ') by
                cases hreach with
                | step _ _ _ h1 hrest =>
                  cases h1 with
                  | step_loop_exit hg_ff hib hff_iff hwfb' =>
                    -- Zero-iter det.  ρ' must equal the terminal env produced
                    -- by step_loop_exit, which is `{ρ₀ with hasFailure := _||_}`.
                    -- We avoid naming `hasInvFailure` by working at the env
                    -- level: same eval, same store, same hasFailure (= false).
                    have hρ'_eq : ρ' = ρ₀ := by
                      have hρ'_raw : ∃ b : Bool,
                          ρ' = { ρ₀ with hasFailure := ρ₀.hasFailure || b } := by
                        cases hrest with
                        | refl _ => exact ⟨_, rfl⟩
                        | step _ _ _ h _ => cases h
                      obtain ⟨b, hraw⟩ := hρ'_raw
                      rw [hraw]
                      have hb_eq : b = Bool.false := by
                        cases b
                        · rfl
                        · exfalso
                          have : ρ'.hasFailure = Bool.true := by
                            rw [hraw, hnf₀]; rfl
                          rw [hnf''] at this; cases this
                      subst hb_eq
                      exact env_or_false_eq ρ₀
                    rw [hρ'_eq]
                    -- Build target trace: outer block wraps the inner stmts list.
                    let loop_num := (StringGenState.gen "loop" σ.gen).fst
                    let invSuffix : Nat → String → String := fun i lbl =>
                      if lbl.isEmpty then toString i else s!"{i}_{lbl}"
                    let mkAssertLabel : Nat → String → String := fun i lbl =>
                      s!"{loopElimAssertPrefix}{loop_num}_entry_invariant_{invSuffix i lbl}"
                    let mkAssumeLabel : Nat → String → String := fun i lbl =>
                      s!"{loopElimAssumePrefix}{loop_num}_entry_invariant_{invSuffix i lbl}"
                    have hwfb := hswf.wfBool
                    have h_asserts :=
                      stmts_mapIdx_assert_terminal π φ inv ρ₀ md mkAssertLabel hwfb hall_tt
                    have h_assumes :=
                      stmts_mapIdx_assume_terminal π φ inv ρ₀ md mkAssumeLabel hwfb hall_tt
                    have h_fib_run : CoreStar π φ (.stmts first_iter_body ρ₀) (.terminal ρ₀) := by
                      rw [hfib_eq]
                      exact stmts_concat_terminal π φ _ _ ρ₀ ρ₀ ρ₀ h_asserts h_assumes
                    have h_fib_block : CoreStar π φ
                        (.stmt (.block first_iter_label first_iter_body {}) ρ₀)
                        (.terminal ρ₀) := by
                      have h := block_wrap_terminal π φ first_iter_label
                        first_iter_body {} ρ₀ ρ₀ h_fib_run
                      rw [projectStore_self_env] at h; exact h
                    -- Step 2: ite guard is ff at ρ₀, take else (empty [] via block), terminate.
                    have h_ite := ite_det_false_empty_terminal (π := π) (φ := φ)
                      _ then_branch {} ρ₀ hg_ff hwfb'
                    have h_stmts : CoreStar π φ (.stmts [.block first_iter_label
                        first_iter_body {}, .ite _ then_branch [] {}] ρ₀)
                        (.terminal ρ₀) :=
                      ReflTrans_Transitive _ _ _ _
                        (stmts_cons_step Expression (EvalCommand π φ) (EvalPureFunc φ)
                          _ _ ρ₀ ρ₀ h_fib_block)
                        (ReflTrans_Transitive _ _ _ _
                          (stmts_cons_step Expression (EvalCommand π φ) (EvalPureFunc φ)
                            _ _ ρ₀ ρ₀ h_ite)
                          (.step _ _ _ .step_stmts_nil (.refl _)))
                    have h_outer := block_wrap_terminal π φ loop_label _ {} ρ₀ ρ₀ h_stmts
                    rw [projectStore_self_env] at h_outer
                    exact h_outer
                  | step_loop_enter _ _ _ _ _ =>
                    -- ≥1-iter det.  Derive hasInvFailure = false and apply
                    -- h_enter_case directly with hrest.
                    have hh := hasFailure_false_backwards (π := π) (φ := φ) hrest hnf''
                    -- hh has form `(ρ₀.hasFailure || hasInvFailure✝) = Bool.false`.
                    have hnif := loop_step_hasInvFailure_false_of_or
                      (by simpa [Config.getEnv] using hh)
                    exact h_enter_case hnif hrest
                  | step_loop_nondet_exit hib hff_iff =>
                    -- Zero-iter nondet: derive ρ' = ρ₀ without naming hasInvFailure.
                    have hρ'_eq : ρ' = ρ₀ := by
                      have hρ'_raw : ∃ b : Bool,
                          ρ' = { ρ₀ with hasFailure := ρ₀.hasFailure || b } := by
                        cases hrest with
                        | refl _ => exact ⟨_, rfl⟩
                        | step _ _ _ h _ => cases h
                      obtain ⟨b, hraw⟩ := hρ'_raw
                      rw [hraw]
                      have hb_eq : b = Bool.false := by
                        cases b
                        · rfl
                        · exfalso
                          have : ρ'.hasFailure = Bool.true := by
                            rw [hraw, hnf₀]; rfl
                          rw [hnf''] at this; cases this
                      subst hb_eq
                      exact env_or_false_eq ρ₀
                    rw [hρ'_eq]
                    let loop_num := (StringGenState.gen "loop" σ.gen).fst
                    let invSuffix : Nat → String → String := fun i lbl =>
                      if lbl.isEmpty then toString i else s!"{i}_{lbl}"
                    let mkAssertLabel : Nat → String → String := fun i lbl =>
                      s!"{loopElimAssertPrefix}{loop_num}_entry_invariant_{invSuffix i lbl}"
                    let mkAssumeLabel : Nat → String → String := fun i lbl =>
                      s!"{loopElimAssumePrefix}{loop_num}_entry_invariant_{invSuffix i lbl}"
                    have hwfb := hswf.wfBool
                    have h_asserts :=
                      stmts_mapIdx_assert_terminal π φ inv ρ₀ md mkAssertLabel hwfb hall_tt
                    have h_assumes :=
                      stmts_mapIdx_assume_terminal π φ inv ρ₀ md mkAssumeLabel hwfb hall_tt
                    have h_fib_run : CoreStar π φ (.stmts first_iter_body ρ₀) (.terminal ρ₀) := by
                      rw [hfib_eq]
                      exact stmts_concat_terminal π φ _ _ ρ₀ ρ₀ ρ₀ h_asserts h_assumes
                    have h_fib_block : CoreStar π φ
                        (.stmt (.block first_iter_label first_iter_body {}) ρ₀)
                        (.terminal ρ₀) := by
                      have h := block_wrap_terminal π φ first_iter_label
                        first_iter_body {} ρ₀ ρ₀ h_fib_run
                      rw [projectStore_self_env] at h; exact h
                    -- Nondet ite: take else (= [] via block), terminate at ρ₀.
                    have h_ite := ite_nondet_false_empty_terminal (π := π) (φ := φ)
                      then_branch {} ρ₀
                    have h_stmts : CoreStar π φ (.stmts [.block first_iter_label
                        first_iter_body {}, .ite _ then_branch [] {}] ρ₀)
                        (.terminal ρ₀) :=
                      ReflTrans_Transitive _ _ _ _
                        (stmts_cons_step Expression (EvalCommand π φ) (EvalPureFunc φ)
                          _ _ ρ₀ ρ₀ h_fib_block)
                        (ReflTrans_Transitive _ _ _ _
                          (stmts_cons_step Expression (EvalCommand π φ) (EvalPureFunc φ)
                            _ _ ρ₀ ρ₀ h_ite)
                          (.step _ _ _ .step_stmts_nil (.refl _)))
                    have h_outer := block_wrap_terminal π φ loop_label _ {} ρ₀ ρ₀ h_stmts
                    rw [projectStore_self_env] at h_outer
                    exact h_outer
                  | step_loop_nondet_enter _ _ =>
                    -- ≥1-iter nondet.
                    have hh := hasFailure_false_backwards (π := π) (φ := φ) hrest hnf''
                    have hnif := loop_step_hasInvFailure_false_of_or
                      (by simpa [Config.getEnv] using hh)
                    exact h_enter_case hnif hrest
              sorry
            · -- VC1 failure path: some invariant evaluates to ff at ρ₀.
              -- The target's first_iter_block contains entry-asserts on each
              -- invariant; one of these will canFail.  Works for both det and
              -- nondet (and both 0-iter and ≥1-iter).
              refine .inl ?_
              have hsome_ff := not_all_tt_implies_some_ff inv ρ₀ hinv_bool hall_tt
              let loop_num := (StringGenState.gen "loop" σ.gen).fst
              let invSuffix : Nat → String → String := fun i lbl =>
                if lbl.isEmpty then toString i else s!"{i}_{lbl}"
              let mkAssertLabel : Nat → String → String := fun i lbl =>
                s!"{loopElimAssertPrefix}{loop_num}_entry_invariant_{invSuffix i lbl}"
              let mkAssumeLabel : Nat → String → String := fun i lbl =>
                s!"{loopElimAssumePrefix}{loop_num}_entry_invariant_{invSuffix i lbl}"
              let asserts : Statements := inv.mapIdx fun i le =>
                Stmt.cmd (HasPassiveCmds.assert (P := Expression)
                  (mkAssertLabel i le.1) le.2 md)
              let assumes : Statements := inv.mapIdx fun i le =>
                Stmt.cmd (HasPassiveCmds.assume (P := Expression)
                  (mkAssumeLabel i le.1) le.2 md)
              have hcf_asserts : CanFailBlock π φ asserts ρ₀ :=
                stmts_mapIdx_assert_canFail π φ inv ρ₀ md mkAssertLabel hswf.wfBool
                  hnf₀ hinv_bool hsome_ff
              have hcf_fib : CanFailBlock π φ (asserts ++ assumes) ρ₀ :=
                canFailBlock_append_left π φ asserts assumes ρ₀ hcf_asserts
              have hfib : first_iter_body = asserts ++ assumes := hfib_eq
              -- Build canFail on the inner block (first_iter_block alone).
              have hcf_first_block : Transform.CanFail (LangCore π φ)
                  (.block first_iter_label first_iter_body {}) ρ₀ := by
                rw [hfib]
                exact canFailBlock_to_canFail_block π φ first_iter_label _ {} ρ₀ hcf_fib
              -- Apply outer block + head-to-block in one shot, letting Lean
              -- unify the rest of the inner statement list against the goal.
              refine canFailBlock_to_canFail_block π φ loop_label _ {} ρ₀
                (canFail_head_to_block π φ
                  (.block first_iter_label first_iter_body {}) _ ρ₀ hcf_first_block)
      case exit_branch =>
        intro lbl ρ' hreach
        match st with
        | .cmd c =>
          -- .cmd cannot reach .exiting
          rw [stmtResult_cmd]
          exfalso
          cases hreach with
          | step _ _ _ h1 r1 =>
            cases h1 with
            | step_cmd _ =>
              cases r1 with
              | step _ _ _ h2 _ => cases h2
        | .exit l md =>
          rw [stmtResult_exit]
          -- .exit l md reaches .exiting l ρ₀ (and lbl = l, ρ' = ρ₀)
          exact .inr (fun _ => hreach)
        | .funcDecl d md =>
          rw [stmtResult_funcDecl]
          exfalso
          cases hreach with
          | step _ _ _ h1 r1 =>
            cases h1 with
            | step_funcDecl =>
              cases r1 with
              | step _ _ _ h2 _ => cases h2
        | .typeDecl tc md =>
          rw [stmtResult_typeDecl]
          exfalso
          cases hreach with
          | step _ _ _ h1 r1 =>
            cases h1 with
            | step_typeDecl =>
              cases r1 with
              | step _ _ _ h2 _ => cases h2
        | .block l bss md =>
          rw [stmtResult_block]
          have hnofd_bss : Block.noFuncDecl bss = Bool.true := by
            simp [Stmt.noFuncDecl] at hnofd; exact hnofd
          have hsz_bss : Block.sizeOf bss ≤ n := by
            simp [Stmt.sizeOf] at hsz; omega
          cases hreach with
          | step _ _ _ h1 r1 =>
            cases h1 with
            | step_block =>
              obtain ⟨ρ_inner, hne, hexit_inner, hρ'eq⟩ := block_reaches_exiting_refined π φ r1
              have hsim_bss := ih.2.1 σ bss hsz_bss hnofd_bss (stmtOk_block_inner hok) ρ₀
                (InitEnvWF.toBlock_block hswf)
              match hsim_bss.2 lbl ρ_inner hexit_inner with
              | .inl hcf =>
                exact .inl (canFailBlock_to_canFail_block π φ l _ md ρ₀ hcf)
              | .inr hok_bss =>
                refine .inr (fun hnf => ?_)
                have hnf_inner : ρ_inner.hasFailure = Bool.false := by
                  subst hρ'eq; simp at hnf; exact hnf
                have hreach_target := hok_bss hnf_inner
                rw [hρ'eq]
                exact block_wrap_exiting_mismatch π φ l _ md lbl ρ₀ ρ_inner hne hreach_target
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
          | step _ _ _ h1 r1 =>
            cases h1 with
            | step_ite_true hcond hwfb' =>
              have ⟨ρ_inner, hexit_inner, heq⟩ :=
                block_none_reaches_exiting_some (π := π) (φ := φ) r1
              have hsim_tss := ih.2.1 σ tss hsz_tss hnofd_tss (stmtOk_ite_left hok) ρ₀
                (InitEnvWF.toBlock_ite_left hswf)
              match hsim_tss.2 lbl ρ_inner hexit_inner with
              | .inl hcf =>
                obtain ⟨cfg, hfail, hreach_cf⟩ := hcf
                exact .inl ⟨.block .none ρ₀.store cfg,
                  by show cfg.getEnv.hasFailure = Bool.true; exact hfail,
                  .step _ _ _ (.step_ite_true hcond hwfb')
                    (block_inner_star Expression (EvalCommand π φ) (EvalPureFunc φ)
                      _ _ .none ρ₀.store hreach_cf)⟩
              | .inr hok_tss =>
                refine .inr (fun hnf => ?_)
                have hnf_inner : ρ_inner.hasFailure = Bool.false := by
                  subst heq; simp at hnf; exact hnf
                have hreach_target := hok_tss hnf_inner
                subst heq
                exact .step _ _ _ (.step_ite_true hcond hwfb')
                  (ReflTrans_Transitive _ _ _ _
                    (block_inner_star Expression (EvalCommand π φ) (EvalPureFunc φ)
                      _ _ .none ρ₀.store hreach_target)
                    (.step _ _ _ (.step_block_exit_mismatch (fun h => nomatch h)) (.refl _)))
            | step_ite_false hcond hwfb' =>
              have ⟨ρ_inner, hexit_inner, heq⟩ :=
                block_none_reaches_exiting_some (π := π) (φ := φ) r1
              have hsim_ess := ih.2.1 (blockPostState σ tss) ess hsz_ess hnofd_ess
                (stmtOk_ite_right hok) ρ₀ (InitEnvWF.toBlock_ite_right hswf)
              match hsim_ess.2 lbl ρ_inner hexit_inner with
              | .inl hcf =>
                obtain ⟨cfg, hfail, hreach_cf⟩ := hcf
                exact .inl ⟨.block .none ρ₀.store cfg,
                  by show cfg.getEnv.hasFailure = Bool.true; exact hfail,
                  .step _ _ _ (.step_ite_false hcond hwfb')
                    (block_inner_star Expression (EvalCommand π φ) (EvalPureFunc φ)
                      _ _ .none ρ₀.store hreach_cf)⟩
              | .inr hok_ess =>
                refine .inr (fun hnf => ?_)
                have hnf_inner : ρ_inner.hasFailure = Bool.false := by
                  subst heq; simp at hnf; exact hnf
                have hreach_target := hok_ess hnf_inner
                subst heq
                exact .step _ _ _ (.step_ite_false hcond hwfb')
                  (ReflTrans_Transitive _ _ _ _
                    (block_inner_star Expression (EvalCommand π φ) (EvalPureFunc φ)
                      _ _ .none ρ₀.store hreach_target)
                    (.step _ _ _ (.step_block_exit_mismatch (fun h => nomatch h)) (.refl _)))
            | step_ite_nondet_true =>
              have ⟨ρ_inner, hexit_inner, heq⟩ :=
                block_none_reaches_exiting_some (π := π) (φ := φ) r1
              have hsim_tss := ih.2.1 σ tss hsz_tss hnofd_tss (stmtOk_ite_left hok) ρ₀
                (InitEnvWF.toBlock_ite_left hswf)
              match hsim_tss.2 lbl ρ_inner hexit_inner with
              | .inl hcf =>
                obtain ⟨cfg, hfail, hreach_cf⟩ := hcf
                exact .inl ⟨.block .none ρ₀.store cfg,
                  by show cfg.getEnv.hasFailure = Bool.true; exact hfail,
                  .step _ _ _ .step_ite_nondet_true
                    (block_inner_star Expression (EvalCommand π φ) (EvalPureFunc φ)
                      _ _ .none ρ₀.store hreach_cf)⟩
              | .inr hok_tss =>
                refine .inr (fun hnf => ?_)
                have hnf_inner : ρ_inner.hasFailure = Bool.false := by
                  subst heq; simp at hnf; exact hnf
                have hreach_target := hok_tss hnf_inner
                subst heq
                exact .step _ _ _ .step_ite_nondet_true
                  (ReflTrans_Transitive _ _ _ _
                    (block_inner_star Expression (EvalCommand π φ) (EvalPureFunc φ)
                      _ _ .none ρ₀.store hreach_target)
                    (.step _ _ _ (.step_block_exit_mismatch (fun h => nomatch h)) (.refl _)))
            | step_ite_nondet_false =>
              have ⟨ρ_inner, hexit_inner, heq⟩ :=
                block_none_reaches_exiting_some (π := π) (φ := φ) r1
              have hsim_ess := ih.2.1 (blockPostState σ tss) ess hsz_ess hnofd_ess
                (stmtOk_ite_right hok) ρ₀ (InitEnvWF.toBlock_ite_right hswf)
              match hsim_ess.2 lbl ρ_inner hexit_inner with
              | .inl hcf =>
                obtain ⟨cfg, hfail, hreach_cf⟩ := hcf
                exact .inl ⟨.block .none ρ₀.store cfg,
                  by show cfg.getEnv.hasFailure = Bool.true; exact hfail,
                  .step _ _ _ .step_ite_nondet_false
                    (block_inner_star Expression (EvalCommand π φ) (EvalPureFunc φ)
                      _ _ .none ρ₀.store hreach_cf)⟩
              | .inr hok_ess =>
                refine .inr (fun hnf => ?_)
                have hnf_inner : ρ_inner.hasFailure = Bool.false := by
                  subst heq; simp at hnf; exact hnf
                have hreach_target := hok_ess hnf_inner
                subst heq
                exact .step _ _ _ .step_ite_nondet_false
                  (ReflTrans_Transitive _ _ _ _
                    (block_inner_star Expression (EvalCommand π φ) (EvalPureFunc φ)
                      _ _ .none ρ₀.store hreach_target)
                    (.step _ _ _ (.step_block_exit_mismatch (fun h => nomatch h)) (.refl _)))
        | .loop guard measure inv body md =>
          -- LOOP exiting case: see strategy in agent context
          sorry
    case block_corr =>
      intro σ bss hsz hnofd hok ρ₀ hswf
      refine ⟨?bterm, ?bexit⟩
      case bterm =>
        intro ρ' hreach
        match bss with
        | [] =>
          rw [blockResult_nil]
          exact .inr (fun _ => hreach)
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
          | step _ _ _ h1 r1 =>
            cases h1 with
            | step_stmts_cons =>
              -- r1 : CoreStar π φ (.seq (.stmt s ρ₀) ss) (.terminal ρ')
              obtain ⟨ρ₁, hterm_s, hreach_ss⟩ := seq_reaches_terminal (P := Expression)
                (EvalCmd := EvalCommand π φ) (extendEval := EvalPureFunc φ) r1
              have hswf_s : InitEnvWF reserved s ρ₀ :=
                BlockInitEnvWF.toStmt_head hswf
              have hsim_s := ih.1 σ s hsz_s hnofd_s (blockOk_cons_left hok) ρ₀ hswf_s
              match hsim_s.1 ρ₁ hterm_s with
              | .inl hcf_s =>
                exact .inl (canFail_head_to_block π φ (stmtResult σ s) _ ρ₀ hcf_s)
              | .inr hok_s =>
                by_cases hnf₁ : ρ₁.hasFailure = Bool.true
                · refine .inl ?_
                  have hcf_src_s : Transform.CanFail (LangCore π φ) s ρ₀ :=
                    ⟨.terminal ρ₁, by show ρ₁.hasFailure = Bool.true; exact hnf₁, hterm_s⟩
                  have hcf_tgt_s := ih.2.2.1 σ s hsz_s hnofd_s (blockOk_cons_left hok) ρ₀
                    hswf_s hcf_src_s
                  exact canFail_head_to_block π φ _ _ ρ₀ hcf_tgt_s
                · have hnf₁' : ρ₁.hasFailure = Bool.false := by
                    cases h : ρ₁.hasFailure <;> simp_all
                  have htgt_s := hok_s hnf₁'
                  have hsim_ss := ih.2.1 (stmtPostState σ s) ss hsz_ss hnofd_ss
                    (blockOk_cons_right hok) ρ₁
                    (BlockInitEnvWF.toBlock_tail_via_defUseOk (π := π) (φ := φ) hswf hterm_s hnofd_s)
                  match hsim_ss.1 ρ' hreach_ss with
                  | .inl hcf_ss =>
                    refine .inl ?_
                    obtain ⟨cfg2, hf2, hr2⟩ := hcf_ss
                    refine ⟨cfg2, hf2, ?_⟩
                    exact ReflTrans_Transitive _ _ _ _
                      (stmts_cons_step Expression (EvalCommand π φ) (EvalPureFunc φ)
                        (stmtResult σ s) (blockResult (stmtPostState σ s) ss) ρ₀ ρ₁ htgt_s)
                      hr2
                  | .inr hok_ss =>
                    refine .inr (fun hnf => ?_)
                    have hnf_ss := hok_ss hnf
                    exact ReflTrans_Transitive _ _ _ _
                      (stmts_cons_step Expression (EvalCommand π φ) (EvalPureFunc φ)
                        (stmtResult σ s) (blockResult (stmtPostState σ s) ss) ρ₀ ρ₁ htgt_s)
                      hnf_ss
      case bexit =>
        intro lbl ρ' hreach
        match bss with
        | [] =>
          -- empty stmts can't reach .exiting
          exfalso
          cases hreach with
          | step _ _ _ h1 r1 =>
            cases h1 with
            | step_stmts_nil =>
              cases r1 with
              | step _ _ _ h2 _ => cases h2
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
          | step _ _ _ h1 r1 =>
            cases h1 with
            | step_stmts_cons =>
              -- The seq either: head exits, or head terminates and tail exits
              match seq_reaches_exiting (P := Expression)
                (EvalCmd := EvalCommand π φ) (extendEval := EvalPureFunc φ) r1 with
              | .inl hexit_s =>
                -- head exits at lbl
                have hsim_s := ih.1 σ s hsz_s hnofd_s (blockOk_cons_left hok) ρ₀
                  (BlockInitEnvWF.toStmt_head hswf)
                match hsim_s.2 lbl ρ' hexit_s with
                | .inl hcf_s =>
                  exact .inl (canFail_head_to_block π φ _ _ ρ₀ hcf_s)
                | .inr hok_s =>
                  refine .inr (fun hnf => ?_)
                  exact stmts_cons_exiting π φ _ _ lbl ρ₀ ρ' (hok_s hnf)
              | .inr ⟨ρ₁, hterm_s, hexit_ss⟩ =>
                -- head terminates at ρ₁, tail exits
                have hswf_s := BlockInitEnvWF.toStmt_head hswf
                have hsim_s := ih.1 σ s hsz_s hnofd_s (blockOk_cons_left hok) ρ₀ hswf_s
                match hsim_s.1 ρ₁ hterm_s with
                | .inl hcf_s =>
                  exact .inl (canFail_head_to_block π φ _ _ ρ₀ hcf_s)
                | .inr hok_s =>
                  by_cases hnf₁ : ρ₁.hasFailure = Bool.true
                  · refine .inl ?_
                    have hcf_src_s : Transform.CanFail (LangCore π φ) s ρ₀ :=
                      ⟨.terminal ρ₁, by show ρ₁.hasFailure = Bool.true; exact hnf₁, hterm_s⟩
                    have hswf_s := BlockInitEnvWF.toStmt_head hswf
                    have hcf_tgt_s := ih.2.2.1 σ s hsz_s hnofd_s (blockOk_cons_left hok) ρ₀
                      hswf_s hcf_src_s
                    exact canFail_head_to_block π φ _ _ ρ₀ hcf_tgt_s
                  · have hnf₁' : ρ₁.hasFailure = Bool.false := by
                      cases h : ρ₁.hasFailure <;> simp_all
                    have htgt_s := hok_s hnf₁'
                    have hsim_ss := ih.2.1 (stmtPostState σ s) ss hsz_ss hnofd_ss
                      (blockOk_cons_right hok) ρ₁
                      (BlockInitEnvWF.toBlock_tail_via_defUseOk (π := π) (φ := φ) hswf hterm_s hnofd_s)
                    match hsim_ss.2 lbl ρ' hexit_ss with
                    | .inl hcf_ss =>
                      refine .inl ?_
                      obtain ⟨cfg2, hf2, hr2⟩ := hcf_ss
                      refine ⟨cfg2, hf2, ?_⟩
                      exact ReflTrans_Transitive _ _ _ _
                        (stmts_cons_step Expression (EvalCommand π φ) (EvalPureFunc φ)
                          (stmtResult σ s) (blockResult (stmtPostState σ s) ss) ρ₀ ρ₁ htgt_s)
                        hr2
                    | .inr hok_ss =>
                      refine .inr (fun hnf => ?_)
                      have hnf_ss := hok_ss hnf
                      exact ReflTrans_Transitive _ _ _ _
                        (stmts_cons_step Expression (EvalCommand π φ) (EvalPureFunc φ)
                          (stmtResult σ s) (blockResult (stmtPostState σ s) ss) ρ₀ ρ₁ htgt_s)
                        hnf_ss
    case stmt_cf =>
      -- Statement-level CanFail preservation: same pattern as canfail_simulation
      intro σ st hsz hnofd hok ρ₀ hswf hcf
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
            have ⟨cfg', hfail'', hreach'⟩ := ih.2.2.2 σ bss hsz_bss hnofd_bss
              (stmtOk_block_inner hok) ρ₀ (InitEnvWF.toBlock_block hswf)
              ⟨inner_cfg, hfail', hinner⟩
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
            have ⟨inner_cfg, hfail', hinner⟩ := block_canfail_to_inner r1 hfail
            have ⟨cfg', hfail'', hreach'⟩ := ih.2.2.2 σ tss hsz_tss hnofd_tss
              (stmtOk_ite_left hok) ρ₀ (InitEnvWF.toBlock_ite_left hswf)
              ⟨inner_cfg, hfail', hinner⟩
            exact ⟨.block .none ρ₀.store cfg',
              by show cfg'.getEnv.hasFailure = Bool.true; exact hfail'',
              .step _ _ _ (.step_ite_true hcond hwfb')
                (block_inner_star Expression (EvalCommand π φ) (EvalPureFunc φ)
                  _ _ .none ρ₀.store hreach')⟩
          | step_ite_false hcond hwfb' =>
            have ⟨inner_cfg, hfail', hinner⟩ := block_canfail_to_inner r1 hfail
            have ⟨cfg', hfail'', hreach'⟩ := ih.2.2.2 (blockPostState σ tss) ess hsz_ess
              hnofd_ess (stmtOk_ite_right hok) ρ₀ (InitEnvWF.toBlock_ite_right hswf)
              ⟨inner_cfg, hfail', hinner⟩
            exact ⟨.block .none ρ₀.store cfg',
              by show cfg'.getEnv.hasFailure = Bool.true; exact hfail'',
              .step _ _ _ (.step_ite_false hcond hwfb')
                (block_inner_star Expression (EvalCommand π φ) (EvalPureFunc φ)
                  _ _ .none ρ₀.store hreach')⟩
          | step_ite_nondet_true =>
            have ⟨inner_cfg, hfail', hinner⟩ := block_canfail_to_inner r1 hfail
            have ⟨cfg', hfail'', hreach'⟩ := ih.2.2.2 σ tss hsz_tss hnofd_tss
              (stmtOk_ite_left hok) ρ₀ (InitEnvWF.toBlock_ite_left hswf)
              ⟨inner_cfg, hfail', hinner⟩
            exact ⟨.block .none ρ₀.store cfg',
              by show cfg'.getEnv.hasFailure = Bool.true; exact hfail'',
              .step _ _ _ .step_ite_nondet_true
                (block_inner_star Expression (EvalCommand π φ) (EvalPureFunc φ)
                  _ _ .none ρ₀.store hreach')⟩
          | step_ite_nondet_false =>
            have ⟨inner_cfg, hfail', hinner⟩ := block_canfail_to_inner r1 hfail
            have ⟨cfg', hfail'', hreach'⟩ := ih.2.2.2 (blockPostState σ tss) ess hsz_ess
              hnofd_ess (stmtOk_ite_right hok) ρ₀ (InitEnvWF.toBlock_ite_right hswf)
              ⟨inner_cfg, hfail', hinner⟩
            exact ⟨.block .none ρ₀.store cfg',
              by show cfg'.getEnv.hasFailure = Bool.true; exact hfail'',
              .step _ _ _ .step_ite_nondet_false
                (block_inner_star Expression (EvalCommand π φ) (EvalPureFunc φ)
                  _ _ .none ρ₀.store hreach')⟩
      | .loop guardE measure inv body md =>
        -- Statement CanFail for loop.  Strategy:
        --   * If ρ₀ already has failure, the transformed loop is CanFail at refl.
        --   * Otherwise, invert `hreach`'s first step to extract `hinv_bool`
        --     (each invariant is tt or ff at ρ₀).
        --   * Case-split on `hall_tt`:
        --     - Not all tt (some inv is ff): VC1 path.  The target's
        --       `first_iter_block` begins with entry-asserts on each invariant;
        --       the failing one drives `stmts_mapIdx_assert_canFail` lifted
        --       through the outer wrapper blocks.
        --     - All tt: trace must continue past step_loop_*_exit (which would
        --       leave ρ₀ unchanged on hasFailure if hasInvFailure=false) into
        --       step_loop_*_enter's body trace.
        by_cases hnf₀ : ρ₀.hasFailure = Bool.true
        · exact ⟨.stmt (stmtResult σ (.loop guardE measure inv body md)) ρ₀,
            by show ρ₀.hasFailure = Bool.true; exact hnf₀, .refl _⟩
        · have hnf₀' : ρ₀.hasFailure = Bool.false := by
            cases h : ρ₀.hasFailure
            · rfl
            · exact absurd h hnf₀
          -- Extract `hinv_bool` from any of the 4 first-step cases.
          have hinv_bool : ∀ le ∈ inv,
              ρ₀.eval ρ₀.store le.2 = some HasBool.tt ∨
              ρ₀.eval ρ₀.store le.2 = some HasBool.ff := by
            cases hreach with
            | refl =>
              -- cfg = .stmt loop ρ₀, getEnv = ρ₀.  hasFailure = false (hnf₀'),
              -- contradicting hfail.
              exfalso
              have : ρ₀.hasFailure = Bool.true := hfail
              rw [hnf₀'] at this; cases this
            | step _ _ _ h1 _ =>
              cases h1 with
              | step_loop_exit _ hib _ _ => exact hib
              | step_loop_enter _ hib _ _ _ => exact hib
              | step_loop_nondet_exit hib _ => exact hib
              | step_loop_nondet_enter hib _ => exact hib
          -- Obtain target's structural decomposition.
          obtain ⟨loop_label, first_iter_label, first_iter_body, then_branch,
                  htgt_eq, hfib_eq⟩ :=
            stmtResult_loop_struct σ guardE measure inv body md hok
          rw [htgt_eq]
          by_cases hall_tt : ∀ le ∈ inv, ρ₀.eval ρ₀.store le.2 = some HasBool.tt
          · -- All-tt path: source's failure must come from body's iteration
            -- (since step_loop_*_exit doesn't fail when all invs are tt).
            -- Mutual-recursion residual: closed by future work.
            sorry
          · -- VC1 failure path: some inv is ff at ρ₀.
            have hsome_ff := not_all_tt_implies_some_ff inv ρ₀ hinv_bool hall_tt
            let loop_num := (StringGenState.gen "loop" σ.gen).fst
            let invSuffix : Nat → String → String := fun i lbl =>
              if lbl.isEmpty then toString i else s!"{i}_{lbl}"
            let mkAssertLabel : Nat → String → String := fun i lbl =>
              s!"{loopElimAssertPrefix}{loop_num}_entry_invariant_{invSuffix i lbl}"
            let mkAssumeLabel : Nat → String → String := fun i lbl =>
              s!"{loopElimAssumePrefix}{loop_num}_entry_invariant_{invSuffix i lbl}"
            let asserts : Statements := inv.mapIdx fun i le =>
              Stmt.cmd (HasPassiveCmds.assert (P := Expression)
                (mkAssertLabel i le.1) le.2 md)
            let assumes : Statements := inv.mapIdx fun i le =>
              Stmt.cmd (HasPassiveCmds.assume (P := Expression)
                (mkAssumeLabel i le.1) le.2 md)
            have hcf_asserts : CanFailBlock π φ asserts ρ₀ :=
              stmts_mapIdx_assert_canFail π φ inv ρ₀ md mkAssertLabel hswf.wfBool
                hnf₀' hinv_bool hsome_ff
            have hcf_fib : CanFailBlock π φ (asserts ++ assumes) ρ₀ :=
              canFailBlock_append_left π φ asserts assumes ρ₀ hcf_asserts
            have hfib : first_iter_body = asserts ++ assumes := hfib_eq
            have hcf_first_block : Transform.CanFail (LangCore π φ)
                (.block first_iter_label first_iter_body {}) ρ₀ := by
              rw [hfib]
              exact canFailBlock_to_canFail_block π φ first_iter_label _ {} ρ₀ hcf_fib
            exact canFailBlock_to_canFail_block π φ loop_label _ {} ρ₀
              (canFail_head_to_block π φ
                (.block first_iter_label first_iter_body {}) _ ρ₀ hcf_first_block)
    case block_cf =>
      intro σ bss hsz hnofd hok ρ₀ hswf hcf
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
              have ⟨kcfg, hkf, hkstar⟩ := ih.2.2.1 σ s hsz_s hnofd_s
                (blockOk_cons_left hok) ρ₀ (BlockInitEnvWF.toStmt_head hswf)
                ⟨cfg', hf', hstar'⟩
              exact canFail_head_to_block π φ (stmtResult σ s)
                (blockResult (stmtPostState σ s) ss) ρ₀ ⟨kcfg, hkf, hkstar⟩
            | .inr ⟨ρ₁, hterm_s, cfg', hf', hstar_rest⟩ =>
              have hsim_s := ih.1 σ s hsz_s hnofd_s (blockOk_cons_left hok) ρ₀
                (BlockInitEnvWF.toStmt_head hswf)
              match hsim_s.1 ρ₁ hterm_s with
              | .inl hcf_s =>
                exact canFail_head_to_block π φ (stmtResult σ s)
                  (blockResult (stmtPostState σ s) ss) ρ₀ hcf_s
              | .inr hok_s =>
                by_cases hnf₁ : ρ₁.hasFailure = Bool.true
                · have hcf_src_s : Transform.CanFail (LangCore π φ) s ρ₀ :=
                    ⟨.terminal ρ₁, by show ρ₁.hasFailure = Bool.true; exact hnf₁, hterm_s⟩
                  have hcf_tgt_s := ih.2.2.1 σ s hsz_s hnofd_s
                    (blockOk_cons_left hok) ρ₀ (BlockInitEnvWF.toStmt_head hswf) hcf_src_s
                  exact canFail_head_to_block π φ (stmtResult σ s)
                    (blockResult (stmtPostState σ s) ss) ρ₀ hcf_tgt_s
                · have hnf₁' : ρ₁.hasFailure = Bool.false := by
                    cases h : ρ₁.hasFailure <;> simp_all
                  have htgt_s := hok_s hnf₁'
                  have ⟨kcfg2, hkf2, hkstar2⟩ := ih.2.2.2 (stmtPostState σ s) ss hsz_ss hnofd_ss
                    (blockOk_cons_right hok) ρ₁
                    (BlockInitEnvWF.toBlock_tail_via_defUseOk (π := π) (φ := φ) hswf hterm_s hnofd_s)
                    ⟨cfg', hf', hstar_rest⟩
                  exact canFail_tail_to_block π φ (stmtResult σ s)
                    (blockResult (stmtPostState σ s) ss) ρ₀ ρ₁ htgt_s ⟨kcfg2, hkf2, hkstar2⟩

private theorem canfail_simulation
    (hwf_ext : WFEvalExtension φ) (sz : Nat)
    (reserved : List String)
    (h_loop_reserved : loopElimReservedPrefixSig ∈ reserved) :
    (∀ (σ : LoopElimState) (st : Statement),
      Stmt.sizeOf st ≤ sz →
      stmtOk σ st →
      Stmt.noFuncDecl st = Bool.true →
      ∀ (ρ₀ : Env Expression),
        InitEnvWF reserved st ρ₀ →
        Transform.CanFail (LangCore π φ) st ρ₀ →
        Transform.CanFail (LangCore π φ) (stmtResult σ st) ρ₀)
    ∧
    (∀ (σ : LoopElimState) (bss : Statements),
      Block.sizeOf bss ≤ sz →
      blockOk σ bss →
      Block.noFuncDecl bss = Bool.true →
      ∀ (ρ₀ : Env Expression),
        BlockInitEnvWF reserved bss ρ₀ →
        CanFailBlock π φ bss ρ₀ →
        CanFailBlock π φ (blockResult σ bss) ρ₀) := by
  have hsim := simulation π φ hwf_ext sz reserved h_loop_reserved
  exact ⟨fun σ st hsz hok hnofd ρ₀ hswf hcf =>
           hsim.2.2.1 σ st hsz hnofd hok ρ₀ hswf hcf,
         fun σ bss hsz hok hnofd ρ₀ hswf hcf =>
           hsim.2.2.2 σ bss hsz hnofd hok ρ₀ hswf hcf⟩

/-! ## Top-level theorem -/

/-- The prefix that loop-elim claims for its fresh names. Any caller invoking
    `loopElim_overapproximatesAggressive` must include this in `reserved`. -/
def loopElimReservedPrefix : String := "$__loop"

/-- Havoc-only command lists have empty `Block.definedVars`. -/
private theorem definedVars_havoc_map (xs : List Expression.Ident)
    (md : MetaData Expression) :
    @Block.definedVars Expression Command _
        (xs.map (fun n => Stmt.cmd (HasHavoc.havoc n md))) false = [] := by
  induction xs with
  | nil => simp [Block.definedVars]
  | cons x rest ih =>
    simp only [List.map_cons, Block.definedVars]
    rw [ih]
    show @Stmt.definedVars Expression Command _ (Stmt.cmd (HasHavoc.havoc x md : Command)) false ++ [] = []
    simp [Stmt.definedVars, HasVarsImp.definedVars, HasHavoc.havoc, Command.definedVars, Cmd.definedVars]

/-- A `mapIdx` of asserts has empty `Block.definedVars`. -/
private theorem definedVars_mapIdx_assert
    (inv : List (String × Expression.Expr)) (md : MetaData Expression)
    (label : Nat → (String × Expression.Expr) → String) :
    @Block.definedVars Expression Command _
      (inv.mapIdx fun i le =>
        Stmt.cmd (HasPassiveCmds.assert (label i le) le.2 md)) false = [] := by
  induction inv generalizing label with
  | nil => simp [List.mapIdx_nil, Block.definedVars]
  | cons x rest ih =>
    rw [List.mapIdx_cons]
    simp only [Block.definedVars]
    rw [ih]
    show @Stmt.definedVars Expression Command _ (Stmt.cmd (HasPassiveCmds.assert (label 0 x) x.2 md : Command)) false ++ [] = []
    simp [Stmt.definedVars, HasVarsImp.definedVars, HasPassiveCmds.assert,
      Command.definedVars, Cmd.definedVars]

/-- A `mapIdx` of assumes has empty `Block.definedVars`. -/
private theorem definedVars_mapIdx_assume
    (inv : List (String × Expression.Expr)) (md : MetaData Expression)
    (label : Nat → (String × Expression.Expr) → String) :
    @Block.definedVars Expression Command _
      (inv.mapIdx fun i le =>
        Stmt.cmd (HasPassiveCmds.assume (label i le) le.2 md)) false = [] := by
  induction inv generalizing label with
  | nil => simp [List.mapIdx_nil, Block.definedVars]
  | cons x rest ih =>
    rw [List.mapIdx_cons]
    simp only [Block.definedVars]
    rw [ih]
    show @Stmt.definedVars Expression Command _ (Stmt.cmd (HasPassiveCmds.assume (label 0 x) x.2 md : Command)) false ++ [] = []
    simp [Stmt.definedVars, HasVarsImp.definedVars, HasPassiveCmds.assume,
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
    Block.modifiedOrDefinedVars (ss₁ ++ ss₂) false =
      (Block.modifiedVars ss₁ ++ Block.modifiedVars ss₂) ++
      (Block.definedVars ss₁ false ++ Block.definedVars ss₂ false) := by
  simp only [Block.modifiedOrDefinedVars, block_modifiedVars_append, block_definedVars_append]

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
private theorem modifiedVars_havoc_map (xs : List Expression.Ident)
    (md : MetaData Expression) :
    @Block.modifiedVars Expression Command _
        (xs.map (fun n => Stmt.cmd (HasHavoc.havoc n md))) = xs := by
  induction xs with
  | nil => simp [Block.modifiedVars]
  | cons x rest ih =>
    simp only [List.map_cons, Block.modifiedVars]
    rw [ih]
    show @Stmt.modifiedVars Expression Command _ (Stmt.cmd (HasHavoc.havoc x md : Command)) ++ rest = x :: rest
    simp [Stmt.modifiedVars, HasVarsImp.modifiedVars, HasHavoc.havoc, Command.modifiedVars, Cmd.modifiedVars]

private theorem modifiedOrDefinedVars_havoc_map (xs : List Expression.Ident)
    (md : MetaData Expression) :
    @Block.modifiedOrDefinedVars Expression Command _
        (xs.map (fun n => Stmt.cmd (HasHavoc.havoc n md))) false = xs := by
  show Block.modifiedVars _ ++ Block.definedVars _ false = xs
  rw [modifiedVars_havoc_map xs md, definedVars_havoc_map xs md, List.append_nil]

/-- A `mapIdx` of asserts has empty `Block.modifiedOrDefinedVars`. -/
private theorem modifiedVars_mapIdx_assert
    (inv : List (String × Expression.Expr)) (md : MetaData Expression)
    (label : Nat → (String × Expression.Expr) → String) :
    @Block.modifiedVars Expression Command _
      (inv.mapIdx fun i le =>
        Stmt.cmd (HasPassiveCmds.assert (label i le) le.2 md)) = [] := by
  induction inv generalizing label with
  | nil => simp [List.mapIdx_nil, Block.modifiedVars]
  | cons x rest ih =>
    rw [List.mapIdx_cons]
    simp only [Block.modifiedVars]
    rw [ih]
    show @Stmt.modifiedVars Expression Command _ (Stmt.cmd (HasPassiveCmds.assert (label 0 x) x.2 md : Command)) ++ [] = []
    simp [Stmt.modifiedVars, HasVarsImp.modifiedVars, HasPassiveCmds.assert,
      Command.modifiedVars, Cmd.modifiedVars]

private theorem modifiedOrDefinedVars_mapIdx_assert
    (inv : List (String × Expression.Expr)) (md : MetaData Expression)
    (label : Nat → (String × Expression.Expr) → String) :
    @Block.modifiedOrDefinedVars Expression Command _
      (inv.mapIdx fun i le =>
        Stmt.cmd (HasPassiveCmds.assert (label i le) le.2 md)) false = [] := by
  show Block.modifiedVars _ ++ Block.definedVars _ false = []
  rw [modifiedVars_mapIdx_assert inv md label, definedVars_mapIdx_assert inv md label]
  rfl

/-- A `mapIdx` of assumes has empty `Block.modifiedOrDefinedVars`. -/
private theorem modifiedVars_mapIdx_assume
    (inv : List (String × Expression.Expr)) (md : MetaData Expression)
    (label : Nat → (String × Expression.Expr) → String) :
    @Block.modifiedVars Expression Command _
      (inv.mapIdx fun i le =>
        Stmt.cmd (HasPassiveCmds.assume (label i le) le.2 md)) = [] := by
  induction inv generalizing label with
  | nil => simp [List.mapIdx_nil, Block.modifiedVars]
  | cons x rest ih =>
    rw [List.mapIdx_cons]
    simp only [Block.modifiedVars]
    rw [ih]
    show @Stmt.modifiedVars Expression Command _ (Stmt.cmd (HasPassiveCmds.assume (label 0 x) x.2 md : Command)) ++ [] = []
    simp [Stmt.modifiedVars, HasVarsImp.modifiedVars, HasPassiveCmds.assume,
      Command.modifiedVars, Cmd.modifiedVars]

private theorem modifiedOrDefinedVars_mapIdx_assume
    (inv : List (String × Expression.Expr)) (md : MetaData Expression)
    (label : Nat → (String × Expression.Expr) → String) :
    @Block.modifiedOrDefinedVars Expression Command _
      (inv.mapIdx fun i le =>
        Stmt.cmd (HasPassiveCmds.assume (label i le) le.2 md)) false = [] := by
  show Block.modifiedVars _ ++ Block.definedVars _ false = []
  rw [modifiedVars_mapIdx_assume inv md label, definedVars_mapIdx_assume inv md label]
  rfl

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

/-! ### Unfolded variants of mapIdx lemmas

The lemmas above use `HasPassiveCmds.assert/assume` in the LHS. When `dsimp`
normalizes terms to use the underlying `CmdExt.cmd (Cmd.assert/assume ...)`
form (which can happen via `simp only [HasPassiveCmds.assert]` or transitive
unfolding), these LHS patterns no longer match. The unfolded variants below
mirror the originals with `CmdExt.cmd (Cmd.assert/assume ...)` in the LHS, so
they work regardless of which form the simp normal form chooses. -/

private theorem mem_definedVars_stmtResult_loop
    (σ : LoopElimState)
    (guard : ExprOrNondet Expression)
    (measure : Option Expression.Expr)
    (inv : List (String × Expression.Expr))
    (body : Statements) (md : MetaData Expression)
    (hok : stmtOk σ (.loop guard measure inv body md))
    (n : Expression.Ident)
    (hn : n ∈ Stmt.definedVars (stmtResult σ (.loop guard measure inv body md)) false) :
    n ∈ Block.definedVars body false ∨
    loopElimReservedPrefix.toList.isPrefixOf n.name.toList := by
  -- Wrap the conclusion in an existential over the loop_num, so that `cases h`
  -- can unify and `rfl` can close the equation in each branch.
  suffices h_suff :
    ∃ (loop_num : String) (s' : Statement),
      stmtResult σ (.loop guard measure inv body md) = s' ∧
      ∀ m, m ∈ Stmt.definedVars s' false →
        m ∈ Block.definedVars body false ∨
        m = (⟨"$__loop_measure_" ++ loop_num, ()⟩ : Expression.Ident) by
    obtain ⟨loop_num, s', hs'_eq, hs'_prop⟩ := h_suff
    rw [hs'_eq] at hn
    rcases hs'_prop n hn with h_body | h_meas
    · exact .inl h_body
    · subst h_meas
      exact .inr (loopElimReservedPrefix_isPrefixOf_measure _)
  -- Unfold stmtResult for the loop case to expose the monadic match.
  change ∃ (loop_num : String) (s' : Statement),
    (match (stmtRun σ (.loop guard measure inv body md)).fst with
      | .ok (_, s'') => s'' | .error _ => default) = s' ∧
    ∀ m, m ∈ Stmt.definedVars s' false →
      m ∈ Block.definedVars body false ∨
      m = (⟨"$__loop_measure_" ++ loop_num, ()⟩ : Expression.Ident)
  have hok' := hok
  unfold stmtOk at hok'
  match h : (stmtRun σ (.loop guard measure inv body md)).fst with
  | .error e => simp [h, Except.isOk, Except.toBool] at hok'
  | .ok (b, s') =>
    simp only [h]
    -- Reduce the monadic computation to expose case splits on guard/measure.
    dsimp only [stmtRun, StateT.run, ExceptT.run, Stmt.removeLoopsM, removeLoopsLoopCase, buildLoopOutput, buildLoopPassive, buildArbitraryIterFacts, buildArbitraryIterAssumes, buildExitStateAssumes, buildHavocBlock, buildFirstIterFacts, buildEntryInvariants, buildEntryInvariantAssumes, buildInvAssumes, buildMaintainInvariants, buildExitInvariantAssumes, buildGuardParts, buildTerminationStmtsSome, hasLabelConflict, numAssertAssumesForLoop, invSuffix, measureOldIdent,
      bind, pure, ExceptT.bind, ExceptT.pure, ExceptT.mk, ExceptT.bindCont,
      ExceptT.lift, StateT.bind, StateT.pure,
      Functor.map, liftM, monadLift, MonadLift.monadLift,
      modify, MonadState.modifyGet, StateT.modifyGet, StateT.map,
      genLoopNum, bumpStat] at h
    -- Dispatch each branch:
    -- - Happy paths: `cases h` unifies the pair, then we analyze definedVars.
    -- - Error paths: `contradiction` (since hok' rules out .error results).
    repeat (first
      | (cases h; exact
          ⟨(StringGenState.gen "loop" σ.gen).fst, _, rfl, fun m hm => by
            simp only [Stmt.definedVars, Bool.false_eq_true, ↓reduceIte, Block.definedVars,
              block_definedVars_append false, List.append_nil] at hm
            repeat rw [definedVars_havoc_map] at hm
            repeat rw [definedVars_mapIdx_assert] at hm
            repeat rw [definedVars_mapIdx_assume] at hm
            simp only [HasVarsImp.definedVars, HasPassiveCmds.assert,
              HasPassiveCmds.assume, HasInit.init, HasIdent.ident,
              Command.definedVars, Cmd.definedVars,
              List.append_nil, List.nil_append, List.mem_append,
              List.not_mem_nil, false_or, or_false, List.mem_singleton] at hm
            first
              | exact .inl hm
              | exact .inr hm
              | (rcases hm with h1 | h1 <;> first | exact .inl h1 | exact .inr h1)
              | (rcases hm with h1 | h1 | h1 <;> first | exact .inl h1 | exact .inr h1)
              | (rcases hm with h1 | h1 | h1 | h1 <;> first | exact .inl h1 | exact .inr h1)
              | (rcases hm with h1 | h1 | h1 | h1 | h1 <;> first | exact .inl h1 | exact .inr h1)⟩)
      | contradiction
      | (split at h; skip))
    -- Close residual goal: the `.det g, some m` case where `h` still has
    -- `StateT.pure ... .bind ...` wrapping the freshness check.
    -- We use `unfold` + the same split/cases/contradiction cycle.
    all_goals (first | contradiction | (
      unfold StateT.pure at h
      dsimp only [StateT.bind, StateT.map, ExceptT.bindCont, ExceptT.bind,
        ExceptT.pure, ExceptT.mk, ExceptT.lift, bind, pure,
        Functor.map, MonadState.modifyGet, StateT.modifyGet,
        MonadStateOf.modifyGet, bumpStat, modify, genLoopNum] at h
      repeat (first
        | (cases h; exact
            ⟨(StringGenState.gen "loop" σ.gen).fst, _, rfl, fun m hm => by
              simp only [Stmt.definedVars, Bool.false_eq_true, ↓reduceIte, Block.definedVars,
                block_definedVars_append false, List.append_nil] at hm
              repeat rw [definedVars_havoc_map] at hm
              repeat rw [definedVars_mapIdx_assert] at hm
              repeat rw [definedVars_mapIdx_assume] at hm
              simp only [HasVarsImp.definedVars, HasPassiveCmds.assert,
                HasPassiveCmds.assume, HasInit.init, HasIdent.ident,
                Command.definedVars, Cmd.definedVars,
                List.append_nil, List.nil_append, List.mem_append,
                List.not_mem_nil, false_or, or_false, List.mem_singleton] at hm
              first
                | exact .inl hm
                | exact .inr hm
                | (rcases hm with h1 | h1 <;> first | exact .inl h1 | exact .inr h1)
                | (rcases hm with h1 | h1 | h1 <;> first | exact .inl h1 | exact .inr h1)
                | (rcases hm with h1 | h1 | h1 | h1 <;> first | exact .inl h1 | exact .inr h1)
                | (rcases hm with h1 | h1 | h1 | h1 | h1 <;> first | exact .inl h1 | exact .inr h1)⟩)
        | contradiction
        | (split at h; skip))
      all_goals (first | contradiction | (
        obtain ⟨_, rfl⟩ := h
        exact ⟨(StringGenState.gen "loop" σ.gen).fst, _, rfl, fun m hm => by
          simp only [Stmt.definedVars, Bool.false_eq_true, ↓reduceIte, Block.definedVars,
            block_definedVars_append (ex := Bool.false), List.append_nil] at hm
          repeat rw [definedVars_havoc_map] at hm
          repeat rw [definedVars_mapIdx_assert] at hm
          repeat rw [definedVars_mapIdx_assume] at hm
          simp only [HasVarsImp.definedVars, HasPassiveCmds.assert,
            HasPassiveCmds.assume, HasInit.init, HasIdent.ident,
            Command.definedVars, Cmd.definedVars,
            List.append_nil, List.nil_append, List.mem_append,
            List.not_mem_nil, false_or, or_false, List.mem_singleton] at hm
          first
            | exact .inl hm
            | exact .inr hm
            | (rcases hm with h1 | h1 <;> first | exact .inl h1 | exact .inr h1)
            | (rcases hm with h1 | h1 | h1 <;> first | exact .inl h1 | exact .inr h1)
            | (rcases hm with h1 | h1 | h1 | h1 <;> first | exact .inl h1 | exact .inr h1)
            | (rcases hm with h1 | h1 | h1 | h1 | h1 <;> first | exact .inl h1 | exact .inr h1)⟩))))

/-! Every name newly defined by the transform either was already a defined var
    of the source statement, or starts with the reserved `loopElimReservedPrefix`. -/
mutual
private theorem mem_definedVars_stmtResult
    (σ : LoopElimState) (s : Statement) (hok : stmtOk σ s) (n : Expression.Ident)
    (hn : n ∈ Stmt.definedVars (stmtResult σ s) false) :
    n ∈ Stmt.definedVars s false ∨
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
    have hn' : n ∈ Block.definedVars (blockResult σ bss) false := by
      simpa [Stmt.definedVars] using hn
    have := mem_definedVars_blockResult σ bss (stmtOk_block_inner hok) n hn'
    rcases this with h | h
    · exact .inl (by simpa [Stmt.definedVars] using h)
    · exact .inr h
  | .ite c tss ess md =>
    rw [stmtResult_ite] at hn
    have hn' : n ∈ Block.definedVars (blockResult σ tss) false ++
                   Block.definedVars (blockResult (blockPostState σ tss) ess) false := by
      simpa [Stmt.definedVars] using hn
    rcases List.mem_append.mp hn' with h | h
    · rcases mem_definedVars_blockResult σ tss (stmtOk_ite_left hok) n h with h | h
      · exact .inl (by simpa [Stmt.definedVars] using List.mem_append_left _ h)
      · exact .inr h
    · rcases mem_definedVars_blockResult (blockPostState σ tss) ess
                (stmtOk_ite_right hok) n h with h | h
      · exact .inl (by simpa [Stmt.definedVars] using List.mem_append_right _ h)
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
    (hn : n ∈ Block.definedVars (blockResult σ bss) false) :
    n ∈ Block.definedVars bss false ∨
    loopElimReservedPrefix.toList.isPrefixOf n.name.toList := by
  match bss with
  | [] =>
    rw [blockResult_nil] at hn
    simp [Block.definedVars] at hn
  | s :: rest =>
    rw [blockResult_cons] at hn
    have hn' : n ∈ Stmt.definedVars (stmtResult σ s) false ++
                   Block.definedVars (blockResult (stmtPostState σ s) rest) false := by
      simpa [Block.definedVars] using hn
    rcases List.mem_append.mp hn' with h | h
    · rcases mem_definedVars_stmtResult σ s (blockOk_cons_left hok) n h with h | h
      · exact .inl (by simpa [Block.definedVars] using List.mem_append_left _ h)
      · exact .inr h
    · rcases mem_definedVars_blockResult (stmtPostState σ s) rest
              (blockOk_cons_right hok) n h with h | h
      · exact .inl (by simpa [Block.definedVars] using List.mem_append_right _ h)
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
    (hn : n ∈ Block.definedVars body false) :
    n ∈ Stmt.definedVars (stmtResult σ (.loop guard measure inv body md)) false := by
  suffices h_suff :
    ∃ (loop_num : String) (s' : Statement),
      stmtResult σ (.loop guard measure inv body md) = s' ∧
      ∀ m, m ∈ Block.definedVars body false → m ∈ Stmt.definedVars s' false by
    obtain ⟨_, s', hs'_eq, hs'_prop⟩ := h_suff
    rw [hs'_eq]
    exact hs'_prop n hn
  change ∃ (loop_num : String) (s' : Statement),
    (match (stmtRun σ (.loop guard measure inv body md)).fst with
      | .ok (_, s'') => s'' | .error _ => default) = s' ∧
    ∀ m, m ∈ Block.definedVars body false → m ∈ Stmt.definedVars s' false
  have hok' := hok
  unfold stmtOk at hok'
  match h : (stmtRun σ (.loop guard measure inv body md)).fst with
  | .error e => simp [h, Except.isOk, Except.toBool] at hok'
  | .ok (b, s') =>
    simp only [h]
    dsimp only [stmtRun, StateT.run, ExceptT.run, Stmt.removeLoopsM, removeLoopsLoopCase, buildLoopOutput, buildLoopPassive, buildArbitraryIterFacts, buildArbitraryIterAssumes, buildExitStateAssumes, buildHavocBlock, buildFirstIterFacts, buildEntryInvariants, buildEntryInvariantAssumes, buildInvAssumes, buildMaintainInvariants, buildExitInvariantAssumes, buildGuardParts, buildTerminationStmtsSome, hasLabelConflict, numAssertAssumesForLoop, invSuffix, measureOldIdent,
      bind, pure, ExceptT.bind, ExceptT.pure, ExceptT.mk, ExceptT.bindCont,
      ExceptT.lift, StateT.bind, StateT.pure,
      Functor.map, liftM, monadLift, MonadLift.monadLift,
      modify, MonadState.modifyGet, StateT.modifyGet, StateT.map,
      genLoopNum, bumpStat] at h
    repeat (first
      | (cases h; exact
          ⟨(StringGenState.gen "loop" σ.gen).fst, _, rfl, fun m hm => by
            simp only [Stmt.definedVars, Bool.false_eq_true, ↓reduceIte, Block.definedVars,
              block_definedVars_append false, List.append_nil]
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
    -- Close residual goal: the `.det g, some m` case where `h` still has
    -- `StateT.pure ... .bind ...` wrapping the freshness check.
    all_goals (first | contradiction | (
      unfold StateT.pure at h
      dsimp only [StateT.bind, StateT.map, ExceptT.bindCont, ExceptT.bind,
        ExceptT.pure, ExceptT.mk, ExceptT.lift, bind, pure,
        Functor.map, MonadState.modifyGet, StateT.modifyGet,
        MonadStateOf.modifyGet, bumpStat, modify, genLoopNum] at h
      repeat (first
        | (cases h; exact
            ⟨(StringGenState.gen "loop" σ.gen).fst, _, rfl, fun m hm => by
              simp only [Stmt.definedVars, Bool.false_eq_true, ↓reduceIte, Block.definedVars,
                block_definedVars_append false, List.append_nil]
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
      all_goals (first | contradiction | (
        obtain ⟨_, rfl⟩ := h
        exact ⟨(StringGenState.gen "loop" σ.gen).fst, _, rfl, fun m hm => by
          simp only [Stmt.definedVars, Bool.false_eq_true, ↓reduceIte, Block.definedVars,
            block_definedVars_append (ex := Bool.false), List.append_nil]
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
            | exact .inr (.inr (.inr hm))⟩))))

-- The transform preserves `definedVars` (the source's defined vars are a
-- subset of the transform's defined vars), assuming the transform succeeds.
mutual
private theorem definedVars_subset_stmtResult
    (σ : LoopElimState) (s : Statement) (hok : stmtOk σ s)
    (n : Expression.Ident)
    (hn : n ∈ Stmt.definedVars s false) :
    n ∈ Stmt.definedVars (stmtResult σ s) false := by
  match s with
  | .cmd c => rw [stmtResult_cmd]; exact hn
  | .exit l md => rw [stmtResult_exit]; exact hn
  | .funcDecl d md => rw [stmtResult_funcDecl]; exact hn
  | .typeDecl tc md => rw [stmtResult_typeDecl]; exact hn
  | .block l bss md =>
    rw [stmtResult_block]
    simp only [Stmt.definedVars]
    have h : n ∈ Block.definedVars bss false := by simpa [Stmt.definedVars] using hn
    exact definedVars_subset_blockResult σ bss (stmtOk_block_inner hok) n h
  | .ite c tss ess md =>
    rw [stmtResult_ite]
    simp only [Stmt.definedVars]
    have h : n ∈ Block.definedVars tss false ++ Block.definedVars ess false := by
      simpa [Stmt.definedVars] using hn
    rcases List.mem_append.mp h with ht | he
    · exact List.mem_append_left _
        (definedVars_subset_blockResult σ tss (stmtOk_ite_left hok) n ht)
    · exact List.mem_append_right _
        (definedVars_subset_blockResult (blockPostState σ tss) ess
          (stmtOk_ite_right hok) n he)
  | .loop guard measure inv body md =>
    have h : n ∈ Block.definedVars body false := by simpa [Stmt.definedVars] using hn
    exact definedVars_subset_stmtResult_loop σ guard measure inv body md hok n h

private theorem definedVars_subset_blockResult
    (σ : LoopElimState) (ss : Statements) (hok : blockOk σ ss)
    (n : Expression.Ident)
    (hn : n ∈ Block.definedVars ss false) :
    n ∈ Block.definedVars (blockResult σ ss) false := by
  match ss with
  | [] => exact hn
  | s :: rest =>
    rw [blockResult_cons]
    simp only [Block.definedVars]
    have h : n ∈ Stmt.definedVars s false ++ Block.definedVars rest false := by
      simpa [Block.definedVars] using hn
    rcases List.mem_append.mp h with hs | hr
    · exact List.mem_append_left _
        (definedVars_subset_stmtResult σ s (blockOk_cons_left hok) n hs)
    · exact List.mem_append_right _
        (definedVars_subset_blockResult (stmtPostState σ s) rest
          (blockOk_cons_right hok) n hr)
end

/-! ### Focused lemmas about each loop-elim builder.

These lemmas characterize the modified/defined/get vars of each builder,
making it possible to prove memberships about the loop-elim output by
composing piece-wise facts rather than running through a giant `dsimp`
+ `cases h` chain. -/

/-- `Block.modifiedVars` of the entry-invariants list (asserts) is empty. -/
private theorem modifiedVars_buildEntryInvariants
    (loop_num : String) (invariants : List (String × Expression.Expr))
    (md : MetaData Expression) :
    Block.modifiedVars (Imperative.LoopElim.buildEntryInvariants (P := Expression) (C := Command)
      loop_num invariants md) = [] := by
  unfold Imperative.LoopElim.buildEntryInvariants
  exact modifiedVars_mapIdx_assert _ _ _

/-- `Block.definedVars` of the entry-invariants list (asserts) is empty. -/
private theorem definedVars_buildEntryInvariants
    (loop_num : String) (invariants : List (String × Expression.Expr))
    (md : MetaData Expression) :
    Block.definedVars (Imperative.LoopElim.buildEntryInvariants (P := Expression) (C := Command)
      loop_num invariants md) false = [] := by
  unfold Imperative.LoopElim.buildEntryInvariants
  exact definedVars_mapIdx_assert _ _ _

/-- `Block.getVars` of the entry-invariants list (asserts) is the flatMap of
    invariant-expression vars. -/
private theorem getVars_buildEntryInvariants
    (loop_num : String) (invariants : List (String × Expression.Expr))
    (md : MetaData Expression) :
    Block.getVars (Imperative.LoopElim.buildEntryInvariants (P := Expression) (C := Command)
      loop_num invariants md) =
    invariants.flatMap (fun lp => HasVarsPure.getVars lp.2) := by
  unfold Imperative.LoopElim.buildEntryInvariants
  exact getVars_mapIdx_assert _ _ _

/-- `Block.modifiedVars` of the entry-invariant-assumes list is empty. -/
private theorem modifiedVars_buildEntryInvariantAssumes
    (loop_num : String) (invariants : List (String × Expression.Expr))
    (md : MetaData Expression) :
    Block.modifiedVars (Imperative.LoopElim.buildEntryInvariantAssumes (P := Expression) (C := Command)
      loop_num invariants md) = [] := by
  unfold Imperative.LoopElim.buildEntryInvariantAssumes
  exact modifiedVars_mapIdx_assume _ _ _

private theorem definedVars_buildEntryInvariantAssumes
    (loop_num : String) (invariants : List (String × Expression.Expr))
    (md : MetaData Expression) :
    Block.definedVars (Imperative.LoopElim.buildEntryInvariantAssumes (P := Expression) (C := Command)
      loop_num invariants md) false = [] := by
  unfold Imperative.LoopElim.buildEntryInvariantAssumes
  exact definedVars_mapIdx_assume _ _ _

private theorem getVars_buildEntryInvariantAssumes
    (loop_num : String) (invariants : List (String × Expression.Expr))
    (md : MetaData Expression) :
    Block.getVars (Imperative.LoopElim.buildEntryInvariantAssumes (P := Expression) (C := Command)
      loop_num invariants md) =
    invariants.flatMap (fun lp => HasVarsPure.getVars lp.2) := by
  unfold Imperative.LoopElim.buildEntryInvariantAssumes
  exact getVars_mapIdx_assume _ _ _

/-- `Block.modifiedVars` of inv-assumes is empty. -/
private theorem getVars_boolNotFunc_opExpr_eq_nil :
    Lambda.LExpr.LExpr.getVars
      (T := Core.CoreLParams.mono)
      (@Lambda.boolNotFunc Core.CoreLParams).opExpr = [] := rfl

/-- Membership in `getVars (HasNot.not g)` implies membership in `getVars g`,
    for the Core.Expression.  This handles every shape of `g` since the
    `HasNot.not` instance only matches `boolConst true`/`boolConst false`
    explicitly and falls through to a `boolNotFunc` application otherwise. -/
private theorem mem_getVars_not_subset
    {g : Core.Expression.Expr} {m : Core.Expression.Ident}
    (hm : m ∈ Lambda.LExpr.LExpr.getVars (HasNot.not g)) :
    m ∈ Lambda.LExpr.LExpr.getVars g := by
  match g, hm with
  | .const _ (.boolConst Bool.true), hm =>
      simp [Lambda.LExpr.LExpr.getVars] at hm
  | .const _ (.boolConst Bool.false), hm =>
      simp [Lambda.LExpr.LExpr.getVars] at hm
  | .const _ (.intConst _), hm =>
      simp [Lambda.LExpr.LExpr.getVars,
            getVars_boolNotFunc_opExpr_eq_nil] at hm
  | .const _ (.strConst _), hm =>
      simp [Lambda.LExpr.LExpr.getVars,
            getVars_boolNotFunc_opExpr_eq_nil] at hm
  | .const _ (.realConst _), hm =>
      simp [Lambda.LExpr.LExpr.getVars,
            getVars_boolNotFunc_opExpr_eq_nil] at hm
  | .const _ (.bitvecConst _ _), hm =>
      simp [Lambda.LExpr.LExpr.getVars,
            getVars_boolNotFunc_opExpr_eq_nil] at hm
  | .op _ _ _, hm =>
      simp [Lambda.LExpr.LExpr.getVars,
            getVars_boolNotFunc_opExpr_eq_nil] at hm
  | .bvar _ _, hm =>
      simp [Lambda.LExpr.LExpr.getVars,
            getVars_boolNotFunc_opExpr_eq_nil] at hm
  | .fvar md₁ name ty, hm =>
      change m ∈ Lambda.LExpr.LExpr.getVars
        (Lambda.LExpr.app () (@Lambda.boolNotFunc Core.CoreLParams).opExpr
          (Lambda.LExpr.fvar md₁ name ty)) at hm
      simp [Lambda.LExpr.LExpr.getVars,
            getVars_boolNotFunc_opExpr_eq_nil] at hm
      simp [Lambda.LExpr.LExpr.getVars, hm]
  | .abs md₁ pn ty body, hm =>
      change m ∈ Lambda.LExpr.LExpr.getVars
        (Lambda.LExpr.app () (@Lambda.boolNotFunc Core.CoreLParams).opExpr
          (Lambda.LExpr.abs md₁ pn ty body)) at hm
      simp [Lambda.LExpr.LExpr.getVars,
            getVars_boolNotFunc_opExpr_eq_nil] at hm
      simp [Lambda.LExpr.LExpr.getVars]; exact hm
  | .quant md₁ k pn ty tr body, hm =>
      change m ∈ Lambda.LExpr.LExpr.getVars
        (Lambda.LExpr.app () (@Lambda.boolNotFunc Core.CoreLParams).opExpr
          (Lambda.LExpr.quant md₁ k pn ty tr body)) at hm
      simp [Lambda.LExpr.LExpr.getVars,
            getVars_boolNotFunc_opExpr_eq_nil] at hm
      simp [Lambda.LExpr.LExpr.getVars]; exact hm
  | .app md₁ f e, hm =>
      change m ∈ Lambda.LExpr.LExpr.getVars
        (Lambda.LExpr.app () (@Lambda.boolNotFunc Core.CoreLParams).opExpr
          (Lambda.LExpr.app md₁ f e)) at hm
      simp [Lambda.LExpr.LExpr.getVars,
            getVars_boolNotFunc_opExpr_eq_nil] at hm
      simp [Lambda.LExpr.LExpr.getVars]; exact hm
  | .ite md₁ c t e, hm =>
      change m ∈ Lambda.LExpr.LExpr.getVars
        (Lambda.LExpr.app () (@Lambda.boolNotFunc Core.CoreLParams).opExpr
          (Lambda.LExpr.ite md₁ c t e)) at hm
      simp [Lambda.LExpr.LExpr.getVars,
            getVars_boolNotFunc_opExpr_eq_nil] at hm
      simp [Lambda.LExpr.LExpr.getVars]; exact hm
  | .eq md₁ e1 e2, hm =>
      change m ∈ Lambda.LExpr.LExpr.getVars
        (Lambda.LExpr.app () (@Lambda.boolNotFunc Core.CoreLParams).opExpr
          (Lambda.LExpr.eq md₁ e1 e2)) at hm
      simp [Lambda.LExpr.LExpr.getVars,
            getVars_boolNotFunc_opExpr_eq_nil] at hm
      simp [Lambda.LExpr.LExpr.getVars]; exact hm

/-- `getVars (HasIntOrder.lt a b)` decomposes into `getVars a` ∪ `getVars b`
    (since `HasIntOrder.lt a b = .app () (.app () Core.intLtOp a) b`). -/
private theorem mem_getVars_lt_split
    {a b : Core.Expression.Expr} {m : Core.Expression.Ident}
    (hm : m ∈ Lambda.LExpr.LExpr.getVars
            (HasIntOrder.lt a b : Core.Expression.Expr)) :
    m ∈ Lambda.LExpr.LExpr.getVars a ∨ m ∈ Lambda.LExpr.LExpr.getVars b := by
  simp [Lambda.LExpr.LExpr.getVars, Core.intLtOp,
        Lambda.WFLFunc.opExpr, Lambda.LFunc.opExpr] at hm
  cases hm with
  | inl h => left; exact h
  | inr h => right; exact h

/-- `getVars` of the integer literal `0` is empty. -/
private theorem getVars_zero_eq_nil :
    Lambda.LExpr.LExpr.getVars (HasIntOrder.zero : Core.Expression.Expr) = [] := by
  simp [Lambda.LExpr.LExpr.getVars]

/-- `getVars (HasFvar.mkFvar v) = [v]`. -/
private theorem getVars_mkFvar_eq
    (v : Core.Expression.Ident) :
    Lambda.LExpr.LExpr.getVars
      (HasFvar.mkFvar v : Core.Expression.Expr) = [v] := by
  simp [Lambda.LExpr.LExpr.getVars]

/-- Helper for `mem_touchedVars_stmtResult_loop`'s residual abstract-`s'`
    branch.  Given the un-dsimp'd `h : (stmtRun σ ...).fst = .ok (b, s')`,
    we can derive `s' = .block ll [.block fil fib {}, .ite guard tb [] {}] {}`
    via `stmtResult_loop_struct` and then dispatch `m ∈ Stmt.touchedVars s'`
    to one of the source-touched pieces or the output-defined `m_old` name. -/
private theorem mem_touchedVars_stmtResult_loop_aux
    (σ : LoopElimState)
    (guard : ExprOrNondet Expression)
    (measure : Option Expression.Expr)
    (inv : List (String × Expression.Expr))
    (body : Statements) (md : MetaData Expression)
    (hok : stmtOk σ (.loop guard measure inv body md))
    (b : Bool) (s' : Statement)
    (h : (stmtRun σ (.loop guard measure inv body md)).fst = .ok (b, s'))
    (m : Expression.Ident)
    (hm : m ∈ Stmt.touchedVars s') :
    m ∈ Stmt.definedVars s' false ∨
    m ∈ Stmt.touchedVars (.loop guard measure inv body md) := by
  dsimp only [stmtRun, StateT.run, ExceptT.run, Stmt.removeLoopsM, removeLoopsLoopCase,
    buildLoopOutput, buildLoopPassive, buildArbitraryIterFacts, buildArbitraryIterAssumes,
    buildExitStateAssumes, buildHavocBlock, buildFirstIterFacts, buildEntryInvariants,
    buildEntryInvariantAssumes, buildInvAssumes, buildMaintainInvariants,
    buildExitInvariantAssumes, buildGuardParts, buildTerminationStmtsSome,
    hasLabelConflict, numAssertAssumesForLoop, invSuffix, measureOldIdent,
    bind, pure, ExceptT.bind, ExceptT.pure, ExceptT.mk, ExceptT.bindCont,
    ExceptT.lift, StateT.bind, StateT.pure,
    Functor.map, liftM, monadLift, MonadLift.monadLift,
    modify, MonadState.modifyGet, StateT.modifyGet, StateT.map,
    genLoopNum, bumpStat] at h
  repeat (first
    | (cases h
       simp only [Stmt.touchedVars, Block.touchedVars,
         Stmt.modifiedOrDefinedVars, Stmt.modifiedVars, Stmt.getVars, Stmt.definedVars,
         Block.modifiedOrDefinedVars, Block.modifiedVars, Block.getVars, Block.definedVars,
         block_modifiedOrDefinedVars_append, block_modifiedVars_append, block_getVars_append, block_definedVars_append,
         Bool.false_eq_true, ↓reduceIte, ite_true, ite_false,
         List.append_nil, List.nil_append,
         List.mem_append, List.not_mem_nil, List.mem_singleton,
         false_or, or_false] at hm ⊢
       repeat rw [modifiedOrDefinedVars_havoc_map'] at hm
       repeat rw [modifiedVars_havoc_map'] at hm
       repeat rw [getVars_havoc_map'] at hm
       repeat rw [definedVars_havoc_map'] at hm
       repeat rw [modifiedOrDefinedVars_mapIdx_assert'] at hm
       repeat rw [modifiedVars_mapIdx_assert'] at hm
       repeat rw [getVars_mapIdx_assert'] at hm
       repeat rw [definedVars_mapIdx_assert'] at hm
       repeat rw [modifiedOrDefinedVars_mapIdx_assume'] at hm
       repeat rw [modifiedVars_mapIdx_assume'] at hm
       repeat rw [getVars_mapIdx_assume'] at hm
       repeat rw [definedVars_mapIdx_assume'] at hm
       repeat rw [modifiedOrDefinedVars_havoc_map']
       repeat rw [modifiedVars_havoc_map']
       repeat rw [getVars_havoc_map']
       repeat rw [definedVars_havoc_map']
       repeat rw [modifiedOrDefinedVars_mapIdx_assert']
       repeat rw [modifiedVars_mapIdx_assert']
       repeat rw [getVars_mapIdx_assert']
       repeat rw [definedVars_mapIdx_assert']
       repeat rw [modifiedOrDefinedVars_mapIdx_assume']
       repeat rw [modifiedVars_mapIdx_assume']
       repeat rw [getVars_mapIdx_assume']
       repeat rw [definedVars_mapIdx_assume']
       simp only [HasVarsImp.definedVars, HasVarsImp.modifiedVars,
         HasVarsPure.getVars,
         HasPassiveCmds.assert, HasPassiveCmds.assume,
         HasInit.init, HasIdent.ident, HasHavoc.havoc,
         Command.definedVars, Command.modifiedVars, Command.getVars,
         Cmd.definedVars, Cmd.modifiedVars, Cmd.getVars,
         ExprOrNondet.getVars,
         List.append_nil, List.nil_append,
         List.mem_append, List.not_mem_nil, List.mem_singleton,
         false_or, or_false] at hm ⊢
       try simp only [List.mem_filter, decide_eq_true_eq] at hm
       repeat first
         | exact .inr (Or.inl hm)
         | exact .inr (Or.inr hm)
         | exact .inr (Or.inl (Or.inl hm))
         | exact .inr (Or.inl (Or.inr hm))
         | exact .inr (Or.inr (Or.inl hm))
         | exact .inr (Or.inr (Or.inr hm))
         | exact .inl hm
         | exact .inl (Or.inl hm)
         | exact .inl (Or.inr hm)
         | exact .inl (Or.inl (Or.inl hm))
         | exact .inl (Or.inr (Or.inl hm))
         | exact .inl (Or.inr (Or.inr hm))
         | (rcases hm with hm | hm)
         | (subst hm; exact .inl (by simp [Stmt.definedVars, Block.definedVars,
             block_definedVars_append, definedVars_havoc_map,
             definedVars_mapIdx_assert, definedVars_mapIdx_assume,
             HasVarsImp.definedVars, HasInit.init, HasIdent.ident,
             Command.definedVars, Cmd.definedVars]))
         | exact absurd hm (List.not_mem_nil _)
       done)
    | contradiction
    | (split at h; skip))
  -- Close residual goals (cases where h still has StateT.pure wrapping)
  all_goals (first | contradiction | (
    unfold StateT.pure at h
    dsimp only [StateT.bind, StateT.map, ExceptT.bindCont, ExceptT.bind,
      ExceptT.pure, ExceptT.mk, ExceptT.lift, bind, pure,
      Functor.map, MonadState.modifyGet, StateT.modifyGet,
      MonadStateOf.modifyGet, bumpStat, modify, genLoopNum] at h
    repeat (first
      | (cases h
         simp only [Stmt.touchedVars, Block.touchedVars,
           Stmt.modifiedOrDefinedVars, Stmt.modifiedVars, Stmt.getVars, Stmt.definedVars,
           Block.modifiedOrDefinedVars, Block.modifiedVars, Block.getVars, Block.definedVars,
           block_modifiedOrDefinedVars_append, block_modifiedVars_append, block_getVars_append, block_definedVars_append,
           Bool.false_eq_true, ↓reduceIte, ite_true, ite_false,
           List.append_nil, List.nil_append,
           List.mem_append, List.not_mem_nil, List.mem_singleton,
           false_or, or_false] at hm ⊢
         repeat rw [modifiedOrDefinedVars_havoc_map'] at hm
         repeat rw [modifiedVars_havoc_map'] at hm
         repeat rw [getVars_havoc_map'] at hm
         repeat rw [definedVars_havoc_map'] at hm
         repeat rw [modifiedOrDefinedVars_mapIdx_assert'] at hm
         repeat rw [modifiedVars_mapIdx_assert'] at hm
         repeat rw [getVars_mapIdx_assert'] at hm
         repeat rw [definedVars_mapIdx_assert'] at hm
         repeat rw [modifiedOrDefinedVars_mapIdx_assume'] at hm
         repeat rw [modifiedVars_mapIdx_assume'] at hm
         repeat rw [getVars_mapIdx_assume'] at hm
         repeat rw [definedVars_mapIdx_assume'] at hm
         repeat rw [modifiedOrDefinedVars_havoc_map']
         repeat rw [modifiedVars_havoc_map']
         repeat rw [getVars_havoc_map']
         repeat rw [definedVars_havoc_map']
         repeat rw [modifiedOrDefinedVars_mapIdx_assert']
         repeat rw [modifiedVars_mapIdx_assert']
         repeat rw [getVars_mapIdx_assert']
         repeat rw [definedVars_mapIdx_assert']
         repeat rw [modifiedOrDefinedVars_mapIdx_assume']
         repeat rw [modifiedVars_mapIdx_assume']
         repeat rw [getVars_mapIdx_assume']
         repeat rw [definedVars_mapIdx_assume']
         simp only [HasVarsImp.definedVars, HasVarsImp.modifiedVars, HasVarsPure.getVars,
           HasPassiveCmds.assert, HasPassiveCmds.assume,
           HasInit.init, HasIdent.ident, HasHavoc.havoc,
           Command.definedVars, Command.modifiedVars, Command.getVars,
           Cmd.definedVars, Cmd.modifiedVars, Cmd.getVars,
           ExprOrNondet.getVars,
           List.append_nil, List.nil_append, List.mem_append, List.not_mem_nil,
           List.mem_singleton, false_or, or_false] at hm ⊢
         try simp only [List.mem_filter, decide_eq_true_eq] at hm
         repeat first
           | exact .inr (Or.inl hm)
           | exact .inr (Or.inr hm)
           | exact .inr (Or.inl (Or.inl hm))
           | exact .inr (Or.inl (Or.inr hm))
           | exact .inr (Or.inr (Or.inl hm))
           | exact .inr (Or.inr (Or.inr hm))
           | exact .inl hm
           | exact .inl (Or.inl hm)
           | exact .inl (Or.inr hm)
           | exact .inl (Or.inl (Or.inl hm))
           | exact .inl (Or.inr (Or.inl hm))
           | exact .inl (Or.inr (Or.inr hm))
           | (rcases hm with hm | hm)
           | (subst hm; exact .inl (by simp [Stmt.definedVars, Block.definedVars,
               block_definedVars_append, definedVars_havoc_map,
               definedVars_mapIdx_assert, definedVars_mapIdx_assume,
               HasVarsImp.definedVars, HasInit.init, HasIdent.ident,
               Command.definedVars, Cmd.definedVars]))
           | exact absurd hm (List.not_mem_nil _)
         done)
      | contradiction
      | (split at h; skip))))
  -- Third level: handle cases via obtain ⟨_, rfl⟩ := h
  all_goals (first | contradiction | (
    obtain ⟨_, rfl⟩ := h
    simp only [Stmt.touchedVars, Block.touchedVars,
      Stmt.modifiedOrDefinedVars, Stmt.modifiedVars, Stmt.getVars, Stmt.definedVars,
      Block.modifiedOrDefinedVars, Block.modifiedVars, Block.getVars, Block.definedVars,
      block_modifiedOrDefinedVars_append, block_modifiedVars_append, block_getVars_append, block_definedVars_append,
      Bool.false_eq_true, ↓reduceIte, ite_true, ite_false,
      List.append_nil, List.nil_append, List.mem_append, List.not_mem_nil,
      List.mem_singleton, false_or, or_false] at hm ⊢
    -- Use unprimed lemmas here (HasPassiveCmds.assert form preserved)
    repeat rw [modifiedOrDefinedVars_havoc_map] at hm
    repeat rw [modifiedVars_havoc_map] at hm
    repeat rw [getVars_havoc_map] at hm
    repeat rw [definedVars_havoc_map] at hm
    repeat rw [modifiedOrDefinedVars_mapIdx_assert] at hm
    repeat rw [modifiedVars_mapIdx_assert] at hm
    repeat rw [getVars_mapIdx_assert] at hm
    repeat rw [definedVars_mapIdx_assert] at hm
    repeat rw [modifiedOrDefinedVars_mapIdx_assume] at hm
    repeat rw [modifiedVars_mapIdx_assume] at hm
    repeat rw [getVars_mapIdx_assume] at hm
    repeat rw [definedVars_mapIdx_assume] at hm
    repeat rw [modifiedOrDefinedVars_havoc_map]
    repeat rw [modifiedVars_havoc_map]
    repeat rw [getVars_havoc_map]
    repeat rw [definedVars_havoc_map]
    repeat rw [modifiedOrDefinedVars_mapIdx_assert]
    repeat rw [modifiedVars_mapIdx_assert]
    repeat rw [getVars_mapIdx_assert]
    repeat rw [definedVars_mapIdx_assert]
    repeat rw [modifiedOrDefinedVars_mapIdx_assume]
    repeat rw [modifiedVars_mapIdx_assume]
    repeat rw [getVars_mapIdx_assume]
    repeat rw [definedVars_mapIdx_assume]
    simp only [HasVarsImp.definedVars, HasVarsImp.modifiedVars, HasVarsPure.getVars,
      HasPassiveCmds.assert, HasPassiveCmds.assume,
      HasInit.init, HasIdent.ident, HasHavoc.havoc,
      Command.definedVars, Command.modifiedVars, Command.getVars,
      Cmd.definedVars, Cmd.modifiedVars, Cmd.getVars,
      ExprOrNondet.getVars,
      List.append_nil, List.nil_append, List.mem_append, List.not_mem_nil,
      List.mem_singleton, false_or, or_false] at hm ⊢
    try simp only [List.mem_filter, decide_eq_true_eq] at hm
    repeat first
      | exact .inr (Or.inl hm)
      | exact .inr (Or.inr hm)
      | exact .inr (Or.inl (Or.inl hm))
      | exact .inr (Or.inl (Or.inr hm))
      | exact .inr (Or.inr (Or.inl hm))
      | exact .inr (Or.inr (Or.inr hm))
      | exact .inl hm
      | exact .inl (Or.inl hm)
      | exact .inl (Or.inr hm)
      | exact .inl (Or.inl (Or.inl hm))
      | exact .inl (Or.inr (Or.inl hm))
      | exact .inl (Or.inr (Or.inr hm))
      | exact .inr (Or.inr (Or.inl (Or.inl hm)))
      | exact .inr (Or.inr (Or.inl (Or.inr hm)))
      | exact .inr (Or.inr (Or.inr (Or.inl hm)))
      | exact .inr (Or.inr (Or.inr (Or.inr hm)))
      | exact .inr (Or.inl (Or.inl (Or.inl hm)))
      | exact .inr (Or.inl (Or.inl (Or.inr hm)))
      | exact .inr (Or.inl (Or.inr (Or.inl hm)))
      | exact .inr (Or.inl (Or.inr (Or.inr hm)))
      | exact .inr (Or.inr (Or.inl (Or.inl (Or.inl hm))))
      | exact .inr (Or.inr (Or.inl (Or.inl (Or.inr hm))))
      | exact .inr (Or.inr (Or.inl (Or.inr (Or.inl hm))))
      | exact .inr (Or.inr (Or.inl (Or.inr (Or.inr hm))))
      | exact .inr (Or.inr (Or.inr (Or.inl (Or.inl hm))))
      | exact .inr (Or.inr (Or.inr (Or.inr (Or.inl hm))))
      | (rcases hm with hm | hm)
      | (obtain ⟨hm, _⟩ := hm)
      | (subst hm; exact .inl (by simp [Stmt.definedVars, Block.definedVars,
          block_definedVars_append, definedVars_havoc_map,
          definedVars_mapIdx_assert, definedVars_mapIdx_assume,
          HasVarsImp.definedVars, HasInit.init, HasIdent.ident,
          Command.definedVars, Cmd.definedVars]))
      | exact absurd hm (List.not_mem_nil _)))
  -- Residual cases: 8 goals where `hm` mentions `HasNot.not`,
  -- `HasIntOrder.lt … (HasFvar.mkFvar …)`, `HasIntOrder.zero`, the
  -- `loop_measure_var` head, or `List.flatMap (fun lp => getVars lp.snd) inv`,
  -- which the previous scaffold's simp set doesn't handle.
  all_goals (first | contradiction | (
    -- Reduce `getVars (HasNot.not g)` to `getVars g`.
    try (replace hm := mem_getVars_not_subset hm)
    try (rcases hm with hm | hm
         <;> first
           | exact .inr (.inr (.inl (.inl (.inl
               (mem_getVars_not_subset hm)))))
           | exact .inr (.inr (.inl (.inr hm)))
           | exact .inr (.inr (.inl (.inl (.inl hm))))
           | exact .inr (.inr (.inr hm)))
    -- Now `hm` should match one of the source-touched pieces:
    --   * `m ∈ getVars g✝`               → into the `getVars` slot
    --   * `m ∈ flatMap getVars inv`       → into the `inv` slot
    --   * `m ∈ Block.getVars body`        → into the rightmost slot
    --   * `m ∈ getVars (HasIntOrder.lt …)`→ split via `mem_getVars_lt_split`
    -- The measure-variable `head` goal has no `hm` and is closed by
    -- `Or.inl (Or.inl rfl)` after the substitution.
    -- The `tail` goal with `getVars zero = []` is contradictory.
    first
      | exact .inr (.inr (.inl (.inl (.inl hm))))
      | exact .inr (.inr (.inl (.inr hm)))
      | exact .inr (.inr (.inr hm))
      | (rcases mem_getVars_lt_split hm with h₁ | h₂
         · refine .inr (.inr (.inl (.inl (.inr ?_))))
           simp [Option.map_some]
           exact h₁
         · simp [getVars_mkFvar_eq] at h₂
           exact .inl (.inl h₂))
      | exact .inl (.inl rfl)
      | (try simp [getVars_zero_eq_nil] at *)))

/-- The loop case of `mem_touchedVars_stmtResult`. -/
private theorem mem_touchedVars_stmtResult_loop
    (σ : LoopElimState)
    (guard : ExprOrNondet Expression)
    (measure : Option Expression.Expr)
    (inv : List (String × Expression.Expr))
    (body : Statements) (md : MetaData Expression)
    (hok : stmtOk σ (.loop guard measure inv body md))
    (n : Expression.Ident)
    (hn : n ∈ Stmt.touchedVars (stmtResult σ (.loop guard measure inv body md)))
    (hnd : n ∉ Stmt.definedVars (stmtResult σ (.loop guard measure inv body md)) false) :
    n ∈ Stmt.touchedVars (.loop guard measure inv body md) ∧
    n ∉ Stmt.definedVars (.loop guard measure inv body md) false := by
  -- The source's `definedVars` ⊆ transform's `definedVars`; combined with
  -- `hnd` we conclude the second component immediately.
  have hnd_src : n ∉ Stmt.definedVars (.loop guard measure inv body md) false := fun h =>
    hnd (definedVars_subset_stmtResult_loop σ guard measure inv body md hok n (by simpa [Stmt.definedVars] using h))
  refine ⟨?_, hnd_src⟩
  -- Suffices: the transform output equals some `s'` such that every `m` in
  -- its `touchedVars` lies in either its `definedVars` (then `hnd` rules it
  -- out) or in source's `touchedVars`.
  suffices h_suff :
    ∃ (loop_num : String) (s' : Statement),
      stmtResult σ (.loop guard measure inv body md) = s' ∧
      ∀ m, m ∈ Stmt.touchedVars s' →
        m ∈ Stmt.definedVars s' false ∨
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
      m ∈ Stmt.definedVars s' false ∨
      m ∈ Stmt.touchedVars (.loop guard measure inv body md)
  have hok' := hok
  unfold stmtOk at hok'
  match h : (stmtRun σ (.loop guard measure inv body md)).fst with
  | .error e => simp [h, Except.isOk, Except.toBool] at hok'
  | .ok (b, s') =>
    simp only [h]
    -- Save the un-dsimp'd `h` so the aux lemma can use it without the
    -- `StringGenState.gen` opacity issue that prevents Lean from coercing
    -- the dsimp'd LHS back to `(stmtRun σ ...).fst`.
    have h_orig : (stmtRun σ (.loop guard measure inv body md)).fst
                  = .ok (b, s') := h
    dsimp only [stmtRun, StateT.run, ExceptT.run, Stmt.removeLoopsM, removeLoopsLoopCase, buildLoopOutput, buildLoopPassive, buildArbitraryIterFacts, buildArbitraryIterAssumes, buildExitStateAssumes, buildHavocBlock, buildFirstIterFacts, buildEntryInvariants, buildEntryInvariantAssumes, buildInvAssumes, buildMaintainInvariants, buildExitInvariantAssumes, buildGuardParts, buildTerminationStmtsSome, hasLabelConflict, numAssertAssumesForLoop, invSuffix, measureOldIdent,
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
    have body_mod_to_src : ∀ m, m ∈ Block.modifiedVars body →
        m ∈ Stmt.touchedVars (.loop guard measure inv body md) := by
      intro m hm
      simp only [Stmt.touchedVars, Stmt.modifiedOrDefinedVars, Stmt.modifiedVars,
        Stmt.definedVars, Stmt.getVars, ite_true, List.append_nil, List.mem_append]
      exact Or.inl hm
    -- Note: `Block.definedVars body false` is NOT in `Stmt.touchedVars (.loop ..)`
    -- because touchedVars uses `excludeScoped=true`. Variables in
    -- `Block.definedVars body false` are routed to `.inl` (transform's definedVars)
    -- in the dispatch below, not to `.inr` (source touchedVars).
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
    repeat (first
      | (cases h; exact
          ⟨(StringGenState.gen "loop" σ.gen).fst, _, rfl, fun m hm => by
            have hm_orig := hm
            simp only [Stmt.touchedVars, Block.touchedVars,
              Stmt.modifiedOrDefinedVars, Stmt.modifiedVars, Stmt.getVars, Stmt.definedVars,
              Block.modifiedOrDefinedVars, Block.modifiedVars, Block.getVars, Block.definedVars,
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
              Bool.false_eq_true, ↓reduceIte, ite_true, ite_false,
              List.append_nil, List.nil_append,
              List.mem_append, List.not_mem_nil, List.mem_singleton,
              false_or, or_false] at hm
            try simp only [List.mem_filter, decide_eq_true_eq] at hm
            -- Dispatch each disjunct of `hm` to the appropriate side.
            (repeat first
              | exact .inr (body_mod_to_src _ hm.1)
              | exact .inr (body_mod_to_src _ hm)
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
              | (exact .inl (by
                   simp only [Stmt.definedVars, Bool.false_eq_true, ↓reduceIte,
                     Block.definedVars, block_definedVars_append,
                     definedVars_havoc_map, definedVars_mapIdx_assert,
                     definedVars_mapIdx_assume,
                     HasVarsImp.definedVars, HasInit.init, HasIdent.ident,
                     Command.definedVars, Cmd.definedVars,
                     List.append_nil, List.nil_append, List.mem_append,
                     List.not_mem_nil, false_or, or_false]
                   first
                     | exact hm | exact .inl hm | exact .inr hm
                     | exact .inl (.inl hm) | exact .inl (.inr hm)
                     | exact .inr (.inl hm) | exact .inr (.inr hm)
                     | exact .inl (.inl (.inl hm)) | exact .inl (.inl (.inr hm))
                     | exact .inl (.inr (.inl hm)) | exact .inl (.inr (.inr hm))
                     | exact .inr (.inl (.inl hm)) | exact .inr (.inl (.inr hm))
                     | exact .inr (.inr (.inl hm)) | exact .inr (.inr (.inr hm))))
              | exact absurd hm (List.not_mem_nil _))
            -- Residual goal (abstract-`s'` branch).  Discharge via the
            -- factored aux lemma.
            all_goals
              exact mem_touchedVars_stmtResult_loop_aux σ guard measure inv body md
                hok b s' h_orig m hm_orig⟩)
      | contradiction
      | (split at h; skip))
    all_goals (first
      | (cases h; exact
          ⟨(StringGenState.gen "loop" σ.gen).fst, _, rfl, fun m hm => by
            simp only [Stmt.touchedVars, Block.touchedVars,
              Stmt.modifiedOrDefinedVars, Stmt.modifiedVars, Stmt.getVars, Stmt.definedVars,
              Block.modifiedOrDefinedVars, Block.modifiedVars, Block.getVars, Block.definedVars,
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
              Bool.false_eq_true, ↓reduceIte, ite_true, ite_false,
              List.append_nil, List.nil_append,
              List.mem_append, List.not_mem_nil, List.mem_singleton,
              false_or, or_false] at hm
            try simp only [List.mem_filter, decide_eq_true_eq] at hm
            (repeat first
              | exact .inr (body_mod_to_src _ hm.1)
              | exact .inr (body_mod_to_src _ hm)
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
              | (exact .inl (by
                   simp only [Stmt.definedVars, Bool.false_eq_true, ↓reduceIte,
                     Block.definedVars, block_definedVars_append,
                     definedVars_havoc_map, definedVars_mapIdx_assert,
                     definedVars_mapIdx_assume,
                     HasVarsImp.definedVars, HasInit.init, HasIdent.ident,
                     Command.definedVars, Cmd.definedVars,
                     List.append_nil, List.nil_append, List.mem_append,
                     List.not_mem_nil, false_or, or_false]
                   first
                     | exact hm | exact .inl hm | exact .inr hm
                     | exact .inl (.inl hm) | exact .inl (.inr hm)
                     | exact .inr (.inl hm) | exact .inr (.inr hm)
                     | exact .inl (.inl (.inl hm)) | exact .inl (.inl (.inr hm))
                     | exact .inl (.inr (.inl hm)) | exact .inl (.inr (.inr hm))
                     | exact .inr (.inl (.inl hm)) | exact .inr (.inl (.inr hm))
                     | exact .inr (.inr (.inl hm)) | exact .inr (.inr (.inr hm))))
              | exact absurd hm (List.not_mem_nil _))
            done⟩)
      | contradiction)

-- Every name in the transform's `touchedVars` outside its `definedVars` was
-- already in the source's `touchedVars` outside source's `definedVars`.
mutual
private theorem mem_touchedVars_stmtResult
    (σ : LoopElimState) (s : Statement) (hok : stmtOk σ s)
    (n : Expression.Ident)
    (hn : n ∈ Stmt.touchedVars (stmtResult σ s))
    (hnd : n ∉ Stmt.definedVars (stmtResult σ s) false) :
    n ∈ Stmt.touchedVars s ∧ n ∉ Stmt.definedVars s false := by
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
    have hnd' : n ∉ Block.definedVars (blockResult σ bss) false := by
      simpa [Stmt.definedVars] using hnd
    have hn' : n ∈ Block.touchedVars (blockResult σ bss) := by
      simp only [Stmt.touchedVars, Stmt.modifiedOrDefinedVars, Stmt.modifiedVars,
        Stmt.definedVars, Stmt.getVars, ite_true, List.append_nil] at hn
      simp only [Block.touchedVars, Block.modifiedOrDefinedVars, List.mem_append]
      rcases List.mem_append.mp hn with hm | hg
      · exact Or.inl (Or.inl hm)
      · exact Or.inr hg
    have ⟨htv, hndef⟩ := mem_touchedVars_blockResult σ bss (stmtOk_block_inner hok) n hn' hnd'
    constructor
    · simp only [Stmt.touchedVars, Stmt.modifiedOrDefinedVars, Stmt.modifiedVars,
        Stmt.definedVars, Stmt.getVars, ite_true, List.append_nil, List.mem_append]
      simp only [Block.touchedVars, Block.modifiedOrDefinedVars, List.mem_append] at htv
      rcases htv with (hm | hd) | hg
      · exact Or.inl hm
      · exact absurd (block_definedVars_true_subset_false bss n hd) hndef
      · exact Or.inr hg
    · simpa [Stmt.definedVars] using hndef
  | .ite c tss ess md =>
    rw [stmtResult_ite] at hn hnd
    have hnd' : n ∉ Block.definedVars (blockResult σ tss) false ∧
                n ∉ Block.definedVars (blockResult (blockPostState σ tss) ess) false := by
      simp only [Stmt.definedVars, Bool.false_eq_true, ↓reduceIte, List.mem_append, not_or] at hnd
      exact hnd
    have hnd_tss : n ∉ Block.definedVars tss false := fun h =>
      hnd'.1 (definedVars_subset_blockResult σ tss (stmtOk_ite_left hok) n h)
    have hnd_ess : n ∉ Block.definedVars ess false := fun h =>
      hnd'.2 (definedVars_subset_blockResult (blockPostState σ tss) ess (stmtOk_ite_right hok) n h)
    have hn' : n ∈ Stmt.touchedVars
        (.ite c (blockResult σ tss) (blockResult (blockPostState σ tss) ess) md) := hn
    simp only [Stmt.touchedVars, Stmt.modifiedOrDefinedVars, Stmt.modifiedVars,
      Stmt.definedVars, Stmt.getVars, ite_true, List.append_nil] at hn'
    -- hn' : n ∈ (Block.modifiedVars ... ++ Block.modifiedVars ...) ++ (c.getVars ++ ...)
    rcases List.mem_append.mp hn' with h_mod | h_gv
    · -- n in modifiedVars of one branch
      rcases List.mem_append.mp h_mod with h_t | h_e
      · -- n ∈ Block.modifiedVars (blockResult σ tss)
        have h_in : n ∈ Block.touchedVars (blockResult σ tss) :=
          List.mem_append_left _ (List.mem_append_left _ h_t)
        have ⟨hsrc, hndef_src⟩ :=
          mem_touchedVars_blockResult σ tss (stmtOk_ite_left hok) n h_in hnd'.1
        constructor
        · simp only [Stmt.touchedVars, Stmt.modifiedOrDefinedVars, Stmt.modifiedVars,
            Stmt.definedVars, Stmt.getVars, ite_true, List.append_nil]
          simp only [Block.touchedVars, Block.modifiedOrDefinedVars, List.mem_append] at hsrc
          rcases hsrc with (hm | hd) | hg
          · exact List.mem_append_left _ (List.mem_append_left _ hm)
          · exact absurd (block_definedVars_true_subset_false tss n hd) hndef_src
          · exact List.mem_append_right _ (List.mem_append_left _ (List.mem_append_right _ hg))
        · simp only [Stmt.definedVars, Bool.false_eq_true, ↓reduceIte, List.mem_append, not_or]
          exact ⟨hndef_src, hnd_ess⟩
      · -- n ∈ Block.modifiedVars (blockResult (blockPostState σ tss) ess)
        have h_in : n ∈ Block.touchedVars (blockResult (blockPostState σ tss) ess) :=
          List.mem_append_left _ (List.mem_append_left _ h_e)
        have ⟨hsrc, hndef_src⟩ :=
          mem_touchedVars_blockResult (blockPostState σ tss) ess (stmtOk_ite_right hok) n h_in hnd'.2
        constructor
        · simp only [Stmt.touchedVars, Stmt.modifiedOrDefinedVars, Stmt.modifiedVars,
            Stmt.definedVars, Stmt.getVars, ite_true, List.append_nil]
          simp only [Block.touchedVars, Block.modifiedOrDefinedVars, List.mem_append] at hsrc
          rcases hsrc with (hm | hd) | hg
          · exact List.mem_append_left _ (List.mem_append_right _ hm)
          · exact absurd (block_definedVars_true_subset_false ess n hd) hndef_src
          · exact List.mem_append_right _ (List.mem_append_right _ hg)
        · simp only [Stmt.definedVars, Bool.false_eq_true, ↓reduceIte, List.mem_append, not_or]
          exact ⟨hnd_tss, hndef_src⟩
    · -- n in getVars (c.getVars ++ Block.getVars tss' ++ Block.getVars ess')
      rcases List.mem_append.mp h_gv with h_cgt | h_ge
      · rcases List.mem_append.mp h_cgt with h_c | h_gt
        · -- n ∈ ExprOrNondet.getVars c (condition is unchanged)
          constructor
          · simp only [Stmt.touchedVars, Stmt.modifiedOrDefinedVars, Stmt.modifiedVars,
              Stmt.definedVars, Stmt.getVars, ite_true, List.append_nil]
            exact List.mem_append_right _ (List.mem_append_left _ (List.mem_append_left _ h_c))
          · simp only [Stmt.definedVars, Bool.false_eq_true, ↓reduceIte, List.mem_append, not_or]
            exact ⟨hnd_tss, hnd_ess⟩
        · -- n ∈ Block.getVars (blockResult σ tss)
          have h_in : n ∈ Block.touchedVars (blockResult σ tss) :=
            List.mem_append_right _ h_gt
          have ⟨hsrc, hndef_src⟩ :=
            mem_touchedVars_blockResult σ tss (stmtOk_ite_left hok) n h_in hnd'.1
          constructor
          · simp only [Stmt.touchedVars, Stmt.modifiedOrDefinedVars, Stmt.modifiedVars,
              Stmt.definedVars, Stmt.getVars, ite_true, List.append_nil]
            simp only [Block.touchedVars, Block.modifiedOrDefinedVars, List.mem_append] at hsrc
            rcases hsrc with (hm | hd) | hg
            · exact List.mem_append_left _ (List.mem_append_left _ hm)
            · exact absurd (block_definedVars_true_subset_false tss n hd) hndef_src
            · exact List.mem_append_right _ (List.mem_append_left _ (List.mem_append_right _ hg))
          · simp only [Stmt.definedVars, Bool.false_eq_true, ↓reduceIte, List.mem_append, not_or]
            exact ⟨hndef_src, hnd_ess⟩
      · -- n ∈ Block.getVars (blockResult (blockPostState σ tss) ess)
        have h_in : n ∈ Block.touchedVars (blockResult (blockPostState σ tss) ess) :=
          List.mem_append_right _ h_ge
        have ⟨hsrc, hndef_src⟩ :=
          mem_touchedVars_blockResult (blockPostState σ tss) ess (stmtOk_ite_right hok) n h_in hnd'.2
        constructor
        · simp only [Stmt.touchedVars, Stmt.modifiedOrDefinedVars, Stmt.modifiedVars,
            Stmt.definedVars, Stmt.getVars, ite_true, List.append_nil]
          simp only [Block.touchedVars, Block.modifiedOrDefinedVars, List.mem_append] at hsrc
          rcases hsrc with (hm | hd) | hg
          · exact List.mem_append_left _ (List.mem_append_right _ hm)
          · exact absurd (block_definedVars_true_subset_false ess n hd) hndef_src
          · exact List.mem_append_right _ (List.mem_append_right _ hg)
        · simp only [Stmt.definedVars, Bool.false_eq_true, ↓reduceIte, List.mem_append, not_or]
          exact ⟨hnd_tss, hndef_src⟩
  | .loop guard measure inv body md =>
    exact mem_touchedVars_stmtResult_loop σ guard measure inv body md hok n hn hnd

private theorem mem_touchedVars_blockResult
    (σ : LoopElimState) (bss : Statements) (hok : blockOk σ bss)
    (n : Expression.Ident)
    (hn : n ∈ Block.touchedVars (blockResult σ bss))
    (hnd : n ∉ Block.definedVars (blockResult σ bss) false) :
    n ∈ Block.touchedVars bss ∧ n ∉ Block.definedVars bss false := by
  match bss with
  | [] =>
    rw [blockResult_nil] at hn hnd
    refine ⟨?_, hnd⟩
    -- Block.touchedVars [] = [] ++ [] = [] → contradiction
    simp [Block.touchedVars, Block.modifiedOrDefinedVars, Block.getVars] at hn
  | s :: rest =>
    rw [blockResult_cons] at hn hnd
    simp only [Block.touchedVars, Block.modifiedOrDefinedVars, Block.modifiedVars,
      Block.definedVars, Block.getVars, List.mem_append] at hn ⊢
    simp only [Block.definedVars, List.mem_append, not_or] at hnd ⊢
    obtain ⟨hnd_s, hnd_r⟩ := hnd
    have hnd_s_src : n ∉ Stmt.definedVars s false := fun h =>
      hnd_s (definedVars_subset_stmtResult σ s (blockOk_cons_left hok) n h)
    have hnd_r_src : n ∉ Block.definedVars rest false := fun h =>
      hnd_r (definedVars_subset_blockResult (stmtPostState σ s) rest (blockOk_cons_right hok) n h)
    rcases hn with ((hms | hmr) | (hds | hdr)) | (hgs | hgr)
    · -- n ∈ Stmt.modifiedVars (stmtResult σ s)
      have h_in : n ∈ Stmt.touchedVars (stmtResult σ s) := by
        simp only [Stmt.touchedVars, Stmt.modifiedOrDefinedVars, List.mem_append]
        exact Or.inl (Or.inl hms)
      have ⟨hsrc, hndef_s⟩ := mem_touchedVars_stmtResult σ s (blockOk_cons_left hok) n h_in hnd_s
      simp only [Stmt.touchedVars, Stmt.modifiedOrDefinedVars, List.mem_append] at hsrc
      refine ⟨?_, hndef_s, hnd_r_src⟩
      rcases hsrc with (hm | hd) | hg
      · exact Or.inl (Or.inl (Or.inl hm))
      · exact Or.inl (Or.inr (Or.inl hd))
      · exact Or.inr (Or.inl hg)
    · -- n ∈ Block.modifiedVars (blockResult (stmtPostState σ s) rest)
      have h_in : n ∈ Block.touchedVars (blockResult (stmtPostState σ s) rest) := by
        simp only [Block.touchedVars, Block.modifiedOrDefinedVars, List.mem_append]
        exact Or.inl (Or.inl hmr)
      have ⟨hsrc, hndef_r⟩ :=
        mem_touchedVars_blockResult (stmtPostState σ s) rest (blockOk_cons_right hok) n h_in hnd_r
      simp only [Block.touchedVars, Block.modifiedOrDefinedVars, List.mem_append] at hsrc
      refine ⟨?_, hnd_s_src, hndef_r⟩
      rcases hsrc with (hm | hd) | hg
      · exact Or.inl (Or.inl (Or.inr hm))
      · exact Or.inl (Or.inr (Or.inr hd))
      · exact Or.inr (Or.inr hg)
    · -- n ∈ Stmt.definedVars (stmtResult σ s) true → contradiction
      exact absurd (stmt_definedVars_true_subset_false (stmtResult σ s) n hds) hnd_s
    · -- n ∈ Block.definedVars (blockResult ...) true → contradiction
      exact absurd (block_definedVars_true_subset_false (blockResult (stmtPostState σ s) rest) n hdr) hnd_r
    · -- n ∈ Stmt.getVars (stmtResult σ s)
      have h_in : n ∈ Stmt.touchedVars (stmtResult σ s) := by
        simp only [Stmt.touchedVars, Stmt.modifiedOrDefinedVars, List.mem_append]
        exact Or.inr hgs
      have ⟨hsrc, hndef_s⟩ := mem_touchedVars_stmtResult σ s (blockOk_cons_left hok) n h_in hnd_s
      simp only [Stmt.touchedVars, Stmt.modifiedOrDefinedVars, List.mem_append] at hsrc
      refine ⟨?_, hndef_s, hnd_r_src⟩
      rcases hsrc with (hm | hd) | hg
      · exact Or.inl (Or.inl (Or.inl hm))
      · exact Or.inl (Or.inr (Or.inl hd))
      · exact Or.inr (Or.inl hg)
    · -- n ∈ Block.getVars (blockResult (stmtPostState σ s) rest)
      have h_in : n ∈ Block.touchedVars (blockResult (stmtPostState σ s) rest) := by
        simp only [Block.touchedVars, Block.modifiedOrDefinedVars, List.mem_append]
        exact Or.inr hgr
      have ⟨hsrc, hndef_r⟩ :=
        mem_touchedVars_blockResult (stmtPostState σ s) rest (blockOk_cons_right hok) n h_in hnd_r
      simp only [Block.touchedVars, Block.modifiedOrDefinedVars, List.mem_append] at hsrc
      refine ⟨?_, hnd_s_src, hndef_r⟩
      rcases hsrc with (hm | hd) | hg
      · exact Or.inl (Or.inl (Or.inr hm))
      · exact Or.inl (Or.inr (Or.inr hd))
      · exact Or.inr (Or.inr hg)
end

/-! ## `defUseWellFormed` preservation through `stmtResult` / `blockResult`

The output of the loop-elim transform is also `defUseWellFormed`.  This is
needed to discharge the `InitEnvWF.defUseOk` field on the output side of
`loopElim_overapproximatesAggressive`.

The proof is structural over the statement.  The non-loop cases reduce
trivially via the `stmtResult_*` / `blockResult_*` identity lemmas.  The
loop case is the only interesting one: we must verify well-formedness for
the produced wrapper

    block loop_label [first_iter_facts, ite guard (arb_facts :: exit_state) [] {}]

against `outer = (·.store).isSome`, given that the source `loop` body is
well-formed against the same `outer` and that the reserved `$__loop` prefix
is fresh in `outer` (via `BlockInitEnvWF.reservedFresh`).  The body itself is
unchanged by the transform — only the wrapper is fresh — so `outer_extend`
suffices for the body's well-formedness inside the encoding (extended by
`m_old`). -/

/-- `Stmt.definedVars (stmtResult σ s) true = Stmt.definedVars s true`.

    For non-loop cases this is straightforward (`stmtResult` is identity for
    cmd/exit/funcDecl/typeDecl, and `definedVars _ true = []` for compound).
    The loop case uses `stmtResult_loop_struct`, which says the loop's output
    is a block, hence `definedVars _ true = []`. -/
private theorem stmtResult_definedVars_true_eq
    (σ : LoopElimState) (s : Statement) (hok : stmtOk σ s) :
    Stmt.definedVars (stmtResult σ s) true = Stmt.definedVars s true := by
  match s with
  | .cmd c => rw [stmtResult_cmd]
  | .exit l md => rw [stmtResult_exit]
  | .funcDecl d md => rw [stmtResult_funcDecl]
  | .typeDecl tc md => rw [stmtResult_typeDecl]
  | .block l bss md =>
    rw [stmtResult_block]; simp [Stmt.definedVars]
  | .ite c tss ess md =>
    rw [stmtResult_ite]; simp [Stmt.definedVars]
  | .loop guard measure inv body md =>
    have ⟨_, _, _, _, hs', _⟩ := stmtResult_loop_struct σ guard measure inv body md hok
    rw [hs']; simp [Stmt.definedVars]

/-! ### Piece-wise `defUseWellFormed` lemmas for loop-elim builders -/

/-- `defUseWellFormed` of a havoc-only command list: requires only that all
    havoc'd variables are in `outer`. -/
private theorem defUseWellFormed_havoc_map (outer : Expression.Ident → Bool)
    (xs : List Expression.Ident) (md : MetaData Expression)
    (hxs : ∀ n ∈ xs, outer n = Bool.true) :
    Block.defUseWellFormed (P := Expression) (C := Command)
      outer (xs.map (fun n => Stmt.cmd (HasHavoc.havoc n md))) = Bool.true := by
  induction xs with
  | nil => simp [Block.defUseWellFormed]
  | cons x rest ih =>
    show Block.defUseWellFormed outer
      (Stmt.cmd (HasHavoc.havoc x md) :: rest.map (fun n => Stmt.cmd (HasHavoc.havoc n md))) = Bool.true
    apply defUseWellFormed_cons_intro
    · -- head: havoc x is well-formed since x ∈ outer.
      show Stmt.defUseWellFormed (P := Expression) (C := Command)
        outer (Stmt.cmd (HasHavoc.havoc x md)) = Bool.true
      simp only [Stmt.defUseWellFormed, HasVarsPure.getVars, HasVarsImp.modifiedVars,
        HasVarsImp.definedVars, HasHavoc.havoc, Command.getVars, Command.modifiedVars,
        Command.definedVars, Cmd.getVars, Cmd.modifiedVars, Cmd.definedVars,
        ExprOrNondet.getVars, List.all_nil, Bool.and_true, Bool.true_and]
      simp [List.all_cons, hxs x (.head _)]
    · -- tail: extending outer by [] (havoc doesn't add to definedVars true) — same as outer.
      have heq : (fun n => outer n || decide (n ∈
          Stmt.definedVars (P := Expression) (C := Command)
            (Stmt.cmd (HasHavoc.havoc x md)) true)) =
          outer := by
        funext n
        simp [Stmt.definedVars, HasVarsImp.definedVars, HasHavoc.havoc,
          Command.definedVars, Cmd.definedVars]
      rw [defUseWellFormed_block_congr (outer₂ := outer) (fun n => congrFun heq n)]
      exact ih (fun n hn => hxs n (.tail _ hn))

/-- `defUseWellFormed` of a `mapIdx` of asserts: requires only that all
    `getVars` of the assert expressions are in `outer`. -/
private theorem defUseWellFormed_mapIdx_assert (outer : Expression.Ident → Bool)
    (inv : List (String × Expression.Expr)) (md : MetaData Expression)
    (label : Nat → (String × Expression.Expr) → String)
    (hgv : ∀ n ∈ inv.flatMap (fun lp => HasVarsPure.getVars lp.2), outer n = Bool.true) :
    Block.defUseWellFormed (P := Expression) (C := Command) outer
      (inv.mapIdx fun i le => Stmt.cmd (HasPassiveCmds.assert (label i le) le.2 md)) = Bool.true := by
  induction inv generalizing label with
  | nil => simp [List.mapIdx_nil, Block.defUseWellFormed]
  | cons x rest ih =>
    rw [List.mapIdx_cons]
    apply defUseWellFormed_cons_intro
    · show Stmt.defUseWellFormed (P := Expression) (C := Command) outer
            (Stmt.cmd (HasPassiveCmds.assert (label 0 x) x.2 md)) = Bool.true
      simp only [Stmt.defUseWellFormed, HasVarsPure.getVars, HasVarsImp.modifiedVars,
        HasVarsImp.definedVars, HasPassiveCmds.assert, Command.getVars, Command.modifiedVars,
        Command.definedVars, Cmd.getVars, Cmd.modifiedVars, Cmd.definedVars,
        List.all_nil, Bool.and_true, Bool.true_and]
      rw [List.all_eq_true]
      intro n hn
      apply hgv n
      simp only [List.flatMap_cons, List.mem_append]
      exact .inl hn
    · have heq : (fun n => outer n || decide (n ∈ Stmt.definedVars (P := Expression) (C := Command)
          (Stmt.cmd (HasPassiveCmds.assert (label 0 x) x.2 md)) true)) = outer := by
        funext n
        simp [Stmt.definedVars, HasVarsImp.definedVars, HasPassiveCmds.assert,
          Command.definedVars, Cmd.definedVars]
      rw [defUseWellFormed_block_congr (outer₂ := outer) (fun n => congrFun heq n)]
      exact ih (fun i le => label (i + 1) le) (fun n hn =>
        hgv n (by simp only [List.flatMap_cons, List.mem_append]; exact .inr hn))

/-- `defUseWellFormed` of a `mapIdx` of assumes: requires only that all
    `getVars` of the assume expressions are in `outer`. -/
private theorem defUseWellFormed_mapIdx_assume (outer : Expression.Ident → Bool)
    (inv : List (String × Expression.Expr)) (md : MetaData Expression)
    (label : Nat → (String × Expression.Expr) → String)
    (hgv : ∀ n ∈ inv.flatMap (fun lp => HasVarsPure.getVars lp.2), outer n = Bool.true) :
    Block.defUseWellFormed (P := Expression) (C := Command) outer
      (inv.mapIdx fun i le => Stmt.cmd (HasPassiveCmds.assume (label i le) le.2 md)) = Bool.true := by
  induction inv generalizing label with
  | nil => simp [List.mapIdx_nil, Block.defUseWellFormed]
  | cons x rest ih =>
    rw [List.mapIdx_cons]
    apply defUseWellFormed_cons_intro
    · show Stmt.defUseWellFormed (P := Expression) (C := Command) outer
            (Stmt.cmd (HasPassiveCmds.assume (label 0 x) x.2 md)) = Bool.true
      simp only [Stmt.defUseWellFormed, HasVarsPure.getVars, HasVarsImp.modifiedVars,
        HasVarsImp.definedVars, HasPassiveCmds.assume, Command.getVars, Command.modifiedVars,
        Command.definedVars, Cmd.getVars, Cmd.modifiedVars, Cmd.definedVars,
        List.all_nil, Bool.and_true, Bool.true_and]
      rw [List.all_eq_true]
      intro n hn
      apply hgv n
      simp only [List.flatMap_cons, List.mem_append]
      exact .inl hn
    · have heq : (fun n => outer n || decide (n ∈ Stmt.definedVars (P := Expression) (C := Command)
          (Stmt.cmd (HasPassiveCmds.assume (label 0 x) x.2 md)) true)) = outer := by
        funext n
        simp [Stmt.definedVars, HasVarsImp.definedVars, HasPassiveCmds.assume,
          Command.definedVars, Cmd.definedVars]
      rw [defUseWellFormed_block_congr (outer₂ := outer) (fun n => congrFun heq n)]
      exact ih (fun i le => label (i + 1) le) (fun n hn =>
        hgv n (by simp only [List.flatMap_cons, List.mem_append]; exact .inr hn))

/-! Auxiliary: `definedVars _ true = []` for the standard pieces. -/

private theorem definedVars_true_havoc_map (xs : List Expression.Ident)
    (md : MetaData Expression) :
    @Block.definedVars Expression Command _
        (xs.map (fun n => Stmt.cmd (HasHavoc.havoc n md))) true = [] := by
  induction xs with
  | nil => simp [Block.definedVars]
  | cons x rest ih =>
    simp only [List.map_cons, Block.definedVars]
    rw [ih]
    show @Stmt.definedVars Expression Command _ (Stmt.cmd (HasHavoc.havoc x md : Command)) true ++ [] = []
    simp [Stmt.definedVars, HasVarsImp.definedVars, HasHavoc.havoc, Command.definedVars, Cmd.definedVars]

private theorem definedVars_true_mapIdx_assert
    (inv : List (String × Expression.Expr)) (md : MetaData Expression)
    (label : Nat → (String × Expression.Expr) → String) :
    @Block.definedVars Expression Command _
      (inv.mapIdx fun i le =>
        Stmt.cmd (HasPassiveCmds.assert (label i le) le.2 md)) true = [] := by
  induction inv generalizing label with
  | nil => simp [List.mapIdx_nil, Block.definedVars]
  | cons x rest ih =>
    rw [List.mapIdx_cons]
    simp only [Block.definedVars]
    rw [ih]
    show @Stmt.definedVars Expression Command _ (Stmt.cmd (HasPassiveCmds.assert (label 0 x) x.2 md : Command)) true ++ [] = []
    simp [Stmt.definedVars, HasVarsImp.definedVars, HasPassiveCmds.assert,
      Command.definedVars, Cmd.definedVars]

private theorem definedVars_true_mapIdx_assume
    (inv : List (String × Expression.Expr)) (md : MetaData Expression)
    (label : Nat → (String × Expression.Expr) → String) :
    @Block.definedVars Expression Command _
      (inv.mapIdx fun i le =>
        Stmt.cmd (HasPassiveCmds.assume (label i le) le.2 md)) true = [] := by
  induction inv generalizing label with
  | nil => simp [List.mapIdx_nil, Block.definedVars]
  | cons x rest ih =>
    rw [List.mapIdx_cons]
    simp only [Block.definedVars]
    rw [ih]
    show @Stmt.definedVars Expression Command _ (Stmt.cmd (HasPassiveCmds.assume (label 0 x) x.2 md : Command)) true ++ [] = []
    simp [Stmt.definedVars, HasVarsImp.definedVars, HasPassiveCmds.assume,
      Command.definedVars, Cmd.definedVars]

/-! ### Master helper for `defUseWellFormed` of `buildLoopOutput`.

    The transform produces
       block "loop_<n>" [first_iter_asserts, ite g (arb_facts :: exit_state) [] {}]
    where `arb_facts` and `exit_state` are themselves blocks containing the
    body, havoc, and various assert/assume pieces.

    Rather than write this proof inline four times (once per case of the
    guard×measure split), we factor it into a reusable helper that is
    parametric in `assumeGuard`, `pre`, `post`, `exit` (the parts that differ
    between the four cases).  The helper takes WF hypotheses for each piece
    and produces WF of the full output. -/

/-- The "havoc filter" subset of `Block.modifiedVars body` that is in `outer`.
    Given `defUseWellFormed outer body = true`, every var in
    `(Block.modifiedVars body).filter (fun v => v ∉ Block.definedVars body false)`
    is in `outer`. -/
private theorem havoc_filter_subset_outer
    (outer : Expression.Ident → Bool) (body : Statements)
    (h_body_wf : Block.defUseWellFormed outer body = Bool.true) :
    ∀ n ∈ ((Block.modifiedVars body).filter
            (fun v => decide ¬v ∈ Block.definedVars body Bool.false)),
      outer n = Bool.true := by
  intro n hn
  rw [List.mem_filter] at hn
  obtain ⟨hn_mod, hn_ndef⟩ := hn
  rw [decide_eq_true_eq] at hn_ndef
  exact defUseWellFormed_modGetVars_implies_outer h_body_wf (Or.inl hn_mod) hn_ndef

/-- The havoc block constructed from `body`'s modified-but-not-defined vars
    is `defUseWellFormed` against any `outer` that body is well-formed against. -/
private theorem defUseWellFormed_havoc_block
    (outer : Expression.Ident → Bool) (body : Statements)
    (md : MetaData Expression) (loop_num : String)
    (h_body_wf : Block.defUseWellFormed outer body = Bool.true) :
    Stmt.defUseWellFormed (P := Expression) (C := Command) outer
      (Stmt.block (toString loopElimBlockPrefix ++ toString "loop_havoc_" ++ loop_num)
        (List.map (fun n => Stmt.cmd (HasHavoc.havoc n md))
          (List.filter (fun v => decide ¬v ∈ Block.definedVars body Bool.false)
            (Block.modifiedVars body)))
        ∅) = Bool.true := by
  rw [defUseWellFormed_block]
  exact defUseWellFormed_havoc_map outer _ md
    (havoc_filter_subset_outer outer body h_body_wf)

/-- The havoc block's `Stmt.definedVars _ true = []`. -/
private theorem definedVars_true_havoc_block
    (body : Statements) (md : MetaData Expression) (loop_num : String) :
    @Stmt.definedVars Expression Command _
      (Stmt.block (toString loopElimBlockPrefix ++ toString "loop_havoc_" ++ loop_num)
        (List.map (fun n => Stmt.cmd (HasHavoc.havoc n md))
          (List.filter (fun v => decide ¬v ∈ Block.definedVars body Bool.false)
            (Block.modifiedVars body)))
        ∅) true = [] := by
  simp [Stmt.definedVars]

/-- WF of the `arbitrary_iter_assumes_<n>` block: given `assumeGuard` is WF
    and the invariants' `getVars` are in `outer`. -/
private theorem defUseWellFormed_arb_iter_assumes_block
    (outer : Expression.Ident → Bool) (loop_num : String)
    (assumeGuard : Statements)
    (inv : List (String × Expression.Expr)) (md : MetaData Expression)
    (h_assumeGuard_wf : Block.defUseWellFormed outer assumeGuard = Bool.true)
    (h_assumeGuard_def_true_empty :
        @Block.definedVars Expression Command _ assumeGuard true = [])
    (h_inv_getVars :
        ∀ n ∈ inv.flatMap (fun lp => HasVarsPure.getVars lp.2),
          outer n = Bool.true) :
    Stmt.defUseWellFormed (P := Expression) (C := Command) outer
      (Stmt.block (toString loopElimBlockPrefix ++ toString "arbitrary_iter_assumes_" ++ loop_num)
        (assumeGuard ++ inv.mapIdx (fun i lp =>
          Stmt.cmd (HasPassiveCmds.assume
            (toString loopElimAssumePrefix ++ loop_num ++ toString "_invariant_" ++
              toString (if lp.fst.isEmpty = Bool.true then toString i
                        else toString i ++ toString "_" ++ toString lp.fst))
            lp.2 md)))
        md) = Bool.true := by
  rw [defUseWellFormed_block]
  rw [defUseWellFormed_block_append]
  refine ⟨h_assumeGuard_wf, ?_⟩
  -- Tail: outer extended by definedVars true assumeGuard = outer.
  rw [defUseWellFormed_block_congr (outer₂ := outer)
        (fun n => by simp [h_assumeGuard_def_true_empty])]
  exact defUseWellFormed_mapIdx_assume outer inv md _ h_inv_getVars

/-- The arb_iter_assumes block's `Stmt.definedVars _ true = []`. -/
private theorem definedVars_true_arb_iter_assumes_block
    (loop_num : String) (assumeGuard : Statements)
    (inv : List (String × Expression.Expr)) (md : MetaData Expression)
    (h_assumeGuard_def_true_empty :
        @Block.definedVars Expression Command _ assumeGuard true = []) :
    @Stmt.definedVars Expression Command _
      (Stmt.block (toString loopElimBlockPrefix ++ toString "arbitrary_iter_assumes_" ++ loop_num)
        (assumeGuard ++ inv.mapIdx (fun i lp =>
          Stmt.cmd (HasPassiveCmds.assume
            (toString loopElimAssumePrefix ++ loop_num ++ toString "_invariant_" ++
              toString (if lp.fst.isEmpty = Bool.true then toString i
                        else toString i ++ toString "_" ++ toString lp.fst))
            lp.2 md)))
        md) true = [] := by
  simp [Stmt.definedVars]

/-- Master helper: well-formedness of `buildLoopOutput`-shaped statements.
    Parametric in `assumeGuard`, `pre`, `post`, `exit` (the four pieces that
    differ between guard×measure cases). -/
private theorem defUseWellFormed_buildLoopOutput_form
    (loop_num : String) (g : ExprOrNondet Expression)
    (inv : List (String × Expression.Expr))
    (body : Statements) (md : MetaData Expression)
    (assumeGuard pre post exit : Statements)
    (outer : Expression.Ident → Bool)
    (h_body_wf : Block.defUseWellFormed outer body = Bool.true)
    (h_inv_getVars :
        ∀ n ∈ inv.flatMap (fun lp => HasVarsPure.getVars lp.2),
          outer n = Bool.true)
    (h_g_getVars : ∀ n ∈ g.getVars, outer n = Bool.true)
    -- `assumeGuard` well-formed and "open" (definedVars true = []).
    (h_assumeGuard_wf : Block.defUseWellFormed outer assumeGuard = Bool.true)
    (h_assumeGuard_def_true_empty :
        @Block.definedVars Expression Command _ assumeGuard true = [])
    -- `pre` is well-formed against any outer-extension that includes outer
    -- (i.e., monotone), and we know what its `definedVars true` is via
    -- `pre_def_true`.  We also need that `pre` isn't reading anything outside
    -- `outer ∪ pre.definedVars true` and doesn't define anything in
    -- `Block.definedVars body false`.
    (pre_def_true : List Expression.Ident)
    (h_pre_def_true_eq :
        @Block.definedVars Expression Command _ pre true = pre_def_true)
    (h_pre_wf : Block.defUseWellFormed outer pre = Bool.true)
    -- `body`'s touched vars don't intersect `pre_def_true` (so we can
    -- absorb pre_def_true into outer for body via defUseWellFormed_outer_extend).
    (h_pre_def_disjoint_body :
        ∀ n ∈ pre_def_true,
          n ∉ Block.modifiedVars body ∧ n ∉ Block.getVars body ∧
          n ∉ Block.definedVars body false)
    -- And: `pre_def_true` doesn't intersect `outer` (so adding it via
    -- `outer ⊕ pre_def_true` truly extends outer).
    -- We don't actually need this directly — but we need that adding
    -- `pre_def_true` to outer doesn't break inv-getVars / etc.
    -- Concretely we need that `pre_def_true ∩ inv_getVars = ∅` and
    -- `pre_def_true ∩ g.getVars = ∅` so the lifted assumes/asserts still hold.
    -- Simpler: just require that `pre_def_true ⊆ {fresh names not in outer-touched}`,
    -- which we model as: pre_def_true is disjoint from inv_getVars ∪ g.getVars.
    (h_pre_def_disjoint_inv :
        ∀ n ∈ pre_def_true,
          n ∉ inv.flatMap (fun lp => HasVarsPure.getVars lp.2))
    (h_pre_def_disjoint_g :
        ∀ n ∈ pre_def_true, n ∉ g.getVars)
    -- `post` is well-formed against `outer ⊕ pre_def_true ⊕ body.definedVars true`.
    (h_post_wf : Block.defUseWellFormed
        (fun n => outer n || decide (n ∈ pre_def_true) ||
                  decide (n ∈ Block.definedVars body true)) post = Bool.true)
    (h_post_def_true_empty :
        @Block.definedVars Expression Command _ post true = [])
    -- `exit` is well-formed against `outer`.
    (h_exit_wf : Block.defUseWellFormed outer exit = Bool.true)
    (h_exit_def_true_empty :
        @Block.definedVars Expression Command _ exit true = []) :
    Stmt.defUseWellFormed (P := Expression) (C := Command) outer
      (Stmt.block (toString loopElimBlockPrefix ++ toString "loop_" ++ loop_num)
        [Stmt.block
            (toString loopElimBlockPrefix ++ toString "first_iter_asserts_" ++ loop_num)
            (inv.mapIdx (fun i lp =>
               Stmt.cmd (HasPassiveCmds.assert
                 (toString loopElimAssertPrefix ++ loop_num ++ toString "_entry_invariant_" ++
                   toString (if lp.fst.isEmpty = Bool.true then toString i
                             else toString i ++ toString "_" ++ toString lp.fst))
                 lp.snd md)) ++
             inv.mapIdx (fun i lp =>
               Stmt.cmd (HasPassiveCmds.assume
                 (toString loopElimAssumePrefix ++ loop_num ++ toString "_entry_invariant_" ++
                   toString (if lp.fst.isEmpty = Bool.true then toString i
                             else toString i ++ toString "_" ++ toString lp.fst))
                 lp.snd md)))
            ∅,
          Stmt.ite g
            (Stmt.block
                (toString loopElimBlockPrefix ++ toString "arbitrary_iter_facts_" ++ loop_num)
                ([Stmt.block
                      (toString loopElimBlockPrefix ++ toString "loop_havoc_" ++ loop_num)
                      (List.map (fun n => Stmt.cmd (HasHavoc.havoc n md))
                        (List.filter (fun v => decide ¬v ∈ Block.definedVars body Bool.false)
                          (Block.modifiedVars body)))
                      ∅,
                    Stmt.block
                      (toString loopElimBlockPrefix ++ toString "arbitrary_iter_assumes_" ++ loop_num)
                      (assumeGuard ++ inv.mapIdx (fun i lp =>
                        Stmt.cmd (HasPassiveCmds.assume
                          (toString loopElimAssumePrefix ++ loop_num ++ toString "_invariant_" ++
                            toString (if lp.fst.isEmpty = Bool.true then toString i
                                      else toString i ++ toString "_" ++ toString lp.fst))
                          lp.2 md)))
                      md] ++ pre ++ body ++
                  inv.mapIdx (fun i lp =>
                    Stmt.cmd (HasPassiveCmds.assert
                      (toString loopElimAssertPrefix ++ loop_num ++
                        toString "_arbitrary_iter_maintain_invariant_" ++
                        toString (if lp.fst.isEmpty = Bool.true then toString i
                                  else toString i ++ toString "_" ++ toString lp.fst))
                      lp.snd md)) ++ post)
                ∅
              :: ([Stmt.block
                    (toString loopElimBlockPrefix ++ toString "loop_havoc_" ++ loop_num)
                    (List.map (fun n => Stmt.cmd (HasHavoc.havoc n md))
                      (List.filter (fun v => decide ¬v ∈ Block.definedVars body Bool.false)
                        (Block.modifiedVars body)))
                    ∅] ++ exit ++
                inv.mapIdx (fun i lp =>
                  Stmt.cmd (HasPassiveCmds.assume
                    (toString loopElimAssumePrefix ++ loop_num ++ toString "_exit_invariant_" ++
                      toString (if lp.fst.isEmpty = Bool.true then toString i
                                else toString i ++ toString "_" ++ toString lp.fst))
                    lp.snd md))))
            [] ∅]
        ∅) = Bool.true := by
  -- Outermost: a `Stmt.block` reduces to `Block.defUseWellFormed` of the inner list.
  rw [defUseWellFormed_block]
  -- The inner list is `[first_iter_asserts; ite g (...) [] {}]`.  Peel the head.
  apply defUseWellFormed_cons_intro
  · -- HEAD 1: first_iter_asserts block.
    -- It's a `Stmt.block (label) (asserts ++ assumes) ∅`.  Reduce to the inner.
    rw [defUseWellFormed_block]
    rw [defUseWellFormed_block_append]
    refine ⟨?_, ?_⟩
    · -- The asserts mapIdx.
      exact defUseWellFormed_mapIdx_assert outer inv md _ h_inv_getVars
    · -- The assumes mapIdx, against `outer ⊕ asserts.definedVars true = outer`.
      rw [defUseWellFormed_block_congr (outer₂ := outer) (fun n => by
        rw [definedVars_true_mapIdx_assert]; simp)]
      exact defUseWellFormed_mapIdx_assume outer inv md _ h_inv_getVars
  · -- TAIL 1: extension by first_iter_asserts.definedVars true is empty (block-wrapped).
    rw [defUseWellFormed_block_congr (outer₂ := outer) (fun n => by simp [Stmt.definedVars])]
    -- The remaining list is `[ite g (arb_facts :: exit_state) [] {}]`.  Peel the head.
    apply defUseWellFormed_cons_intro
    · -- HEAD 2: the ite.
      simp only [Stmt.defUseWellFormed, Bool.and_eq_true]
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · -- All g.getVars in outer.
        rw [List.all_eq_true]; exact h_g_getVars
      · -- THEN-branch: the arb_facts block plus exit_state list.
        -- The block is wrapped in a single-element list.
        show Block.defUseWellFormed outer
          (Stmt.block _ ([_, _] ++ pre ++ body ++ _ ++ post) ∅
            :: ([_] ++ exit ++ _)) = Bool.true
        apply defUseWellFormed_cons_intro
        · -- arb_facts block.
          rw [defUseWellFormed_block]
          -- Inner: `[havoc; arb_iter_assumes] ++ pre ++ body ++ maintain_inv ++ post`.
          rw [defUseWellFormed_block_append]
          refine ⟨?_, ?_⟩
          · -- LHS: `[havoc; arb_iter_assumes] ++ pre ++ body ++ maintain_inv`.
            rw [defUseWellFormed_block_append]
            refine ⟨?_, ?_⟩
            · rw [defUseWellFormed_block_append]
              refine ⟨?_, ?_⟩
              · rw [defUseWellFormed_block_append]
                refine ⟨?_, ?_⟩
                · -- `[havoc; arb_iter_assumes]`
                  apply defUseWellFormed_cons_intro
                  · exact defUseWellFormed_havoc_block outer body md loop_num h_body_wf
                  · -- After havoc, outer extension by [] = outer.
                    rw [defUseWellFormed_block_congr (outer₂ := outer) (fun n => by
                      simp [definedVars_true_havoc_block])]
                    apply defUseWellFormed_cons_intro
                    · exact defUseWellFormed_arb_iter_assumes_block outer loop_num
                        assumeGuard inv md h_assumeGuard_wf h_assumeGuard_def_true_empty
                        h_inv_getVars
                    · -- Trailing nil after the assumes block.
                      rw [defUseWellFormed_block_congr (outer₂ := outer) (fun n => by
                        simp [definedVars_true_arb_iter_assumes_block])]
                      simp [Block.defUseWellFormed]
                · -- After `[havoc; arb_iter_assumes]`, the running outer extension is
                  -- `outer + ([] ++ [])` (both are blocks → definedVars true = []).
                  -- So pre is WF against (outer + ∅) = outer.
                  rw [defUseWellFormed_block_congr (outer₂ := outer) (fun n => by
                    simp [Block.definedVars, definedVars_true_havoc_block,
                          definedVars_true_arb_iter_assumes_block, Stmt.definedVars])]
                  exact h_pre_wf
              · -- After `[havoc; arb_iter_assumes] ++ pre`, the running outer is
                -- `outer + (... + pre.definedVars true) = outer + pre_def_true`.
                rw [defUseWellFormed_block_congr
                      (outer₂ := fun n => outer n || decide (n ∈ pre_def_true)) (fun n => by
                  simp [Block.definedVars, definedVars_true_havoc_block,
                        definedVars_true_arb_iter_assumes_block, Stmt.definedVars,
                        h_pre_def_true_eq])]
                -- Body is WF against outer.  Extend by pre_def_true (disjoint from body).
                exact defUseWellFormed_outer_extend_block h_body_wf (fun n hn => by
                  rw [decide_eq_true_eq] at hn
                  exact h_pre_def_disjoint_body n hn)
            · -- After `[havoc; arb_iter_assumes] ++ pre ++ body`, the running outer is
              -- `outer + pre_def_true + body.definedVars true`.
              rw [defUseWellFormed_block_congr
                    (outer₂ := fun n => outer n || decide (n ∈ pre_def_true)
                                || decide (n ∈ Block.definedVars body Bool.true))
                    (fun n => by
                rw [block_definedVars_append]
                simp [Block.definedVars, definedVars_true_havoc_block,
                      definedVars_true_arb_iter_assumes_block, Stmt.definedVars,
                      h_pre_def_true_eq, Bool.or_assoc])]
              -- maintain_invariants asserts; need invs' getVars in extended outer.
              apply defUseWellFormed_mapIdx_assert
              intro n hn
              simp only [Bool.or_eq_true, decide_eq_true_eq]
              exact .inl (.inl (h_inv_getVars n hn))
          · -- After `[havoc; arb_iter_assumes] ++ pre ++ body ++ maintain_inv`, the running
            -- outer is `outer + pre_def_true + body.definedVars true + []`.
            rw [defUseWellFormed_block_congr
                  (outer₂ := fun n => outer n || decide (n ∈ pre_def_true)
                              || decide (n ∈ Block.definedVars body Bool.true))
                  (fun n => by
              rw [block_definedVars_append, block_definedVars_append,
                  block_definedVars_append, definedVars_true_mapIdx_assert]
              simp [Block.definedVars, definedVars_true_havoc_block,
                    definedVars_true_arb_iter_assumes_block, Stmt.definedVars,
                    h_pre_def_true_eq, Bool.or_assoc])]
            exact h_post_wf
        · -- exit_state tail: `[loop_havoc; ...] ++ exit ++ exit_inv_assumes`,
          -- against `outer ⊕ arb_facts.definedVars true = outer` (block-wrapped).
          rw [defUseWellFormed_block_congr (outer₂ := outer) (fun n => by simp [Stmt.definedVars])]
          rw [defUseWellFormed_block_append]
          refine ⟨?_, ?_⟩
          · rw [defUseWellFormed_block_append]
            refine ⟨?_, ?_⟩
            · -- `[loop_havoc]` singleton.
              apply defUseWellFormed_cons_intro
              · exact defUseWellFormed_havoc_block outer body md loop_num h_body_wf
              · rw [defUseWellFormed_block_congr (outer₂ := outer) (fun n => by
                  simp [definedVars_true_havoc_block])]
                simp [Block.defUseWellFormed]
            · -- exit, against `outer + havoc_block.definedVars true = outer`.
              rw [defUseWellFormed_block_congr (outer₂ := outer) (fun n => by
                simp [Block.definedVars, definedVars_true_havoc_block, Stmt.definedVars])]
              exact h_exit_wf
          · -- exit_inv_assumes mapIdx.
            rw [defUseWellFormed_block_congr (outer₂ := outer) (fun n => by
              simp [Block.definedVars, definedVars_true_havoc_block, Stmt.definedVars,
                    h_exit_def_true_empty])]
            exact defUseWellFormed_mapIdx_assume outer inv md _ h_inv_getVars
      · -- ELSE-branch: empty.
        simp [Block.defUseWellFormed]
    · -- TAIL 2: outer extension by ite.definedVars true = [] = outer.
      simp [Block.defUseWellFormed, Stmt.definedVars]

/-! ### Case-specific instantiations of `defUseWellFormed_buildLoopOutput_form` -/

/-- Auxiliary: an assume command with single getVars in outer is WF and has
    `definedVars _ true = []`. -/
private theorem defUseWellFormed_singleton_assume
    (outer : Expression.Ident → Bool) (label : String)
    (e : Expression.Expr) (md : MetaData Expression)
    (hgv : ∀ n ∈ HasVarsPure.getVars e, outer n = Bool.true) :
    Block.defUseWellFormed (P := Expression) (C := Command) outer
      [Stmt.cmd (HasPassiveCmds.assume label e md)] = Bool.true := by
  apply defUseWellFormed_cons_intro
  · simp only [Stmt.defUseWellFormed, HasVarsPure.getVars, HasVarsImp.modifiedVars,
      HasVarsImp.definedVars, HasPassiveCmds.assume, Command.getVars,
      Command.modifiedVars, Command.definedVars, Cmd.getVars, Cmd.modifiedVars,
      Cmd.definedVars, List.all_nil, Bool.and_true, Bool.true_and]
    rw [List.all_eq_true]; exact hgv
  · simp [Block.defUseWellFormed]

private theorem definedVars_true_singleton_assume
    (label : String) (e : Expression.Expr) (md : MetaData Expression) :
    @Block.definedVars Expression Command _
      [Stmt.cmd (HasPassiveCmds.assume label e md)] true = [] := by
  simp [Block.definedVars, Stmt.definedVars, HasVarsImp.definedVars,
        HasPassiveCmds.assume, Command.definedVars, Cmd.definedVars]

/-- WF of the loop output for the `.nondet` case (no guard, no measure):
    all four pieces (`assumeGuard`, `pre`, `post`, `exit`) are empty. -/
private theorem defUseWellFormed_loop_output_nondet
    (loop_num : String) (inv : List (String × Expression.Expr))
    (body : Statements) (md : MetaData Expression)
    (outer : Expression.Ident → Bool)
    (h_body_wf : Block.defUseWellFormed outer body = Bool.true)
    (h_inv_getVars : ∀ n ∈ inv.flatMap (fun lp => HasVarsPure.getVars lp.2),
        outer n = Bool.true) :
    Stmt.defUseWellFormed (P := Expression) (C := Command) outer
      (Stmt.block (toString loopElimBlockPrefix ++ toString "loop_" ++ loop_num)
        [Stmt.block
            (toString loopElimBlockPrefix ++ toString "first_iter_asserts_" ++ loop_num)
            (inv.mapIdx (fun i lp =>
               Stmt.cmd (HasPassiveCmds.assert
                 (toString loopElimAssertPrefix ++ loop_num ++ toString "_entry_invariant_" ++
                   toString (if lp.fst.isEmpty = Bool.true then toString i
                             else toString i ++ toString "_" ++ toString lp.fst))
                 lp.snd md)) ++
             inv.mapIdx (fun i lp =>
               Stmt.cmd (HasPassiveCmds.assume
                 (toString loopElimAssumePrefix ++ loop_num ++ toString "_entry_invariant_" ++
                   toString (if lp.fst.isEmpty = Bool.true then toString i
                             else toString i ++ toString "_" ++ toString lp.fst))
                 lp.snd md)))
            ∅,
          Stmt.ite (.nondet)
            (Stmt.block
                (toString loopElimBlockPrefix ++ toString "arbitrary_iter_facts_" ++ loop_num)
                ([Stmt.block
                      (toString loopElimBlockPrefix ++ toString "loop_havoc_" ++ loop_num)
                      (List.map (fun n => Stmt.cmd (HasHavoc.havoc n md))
                        (List.filter (fun v => decide ¬v ∈ Block.definedVars body Bool.false)
                          (Block.modifiedVars body)))
                      ∅,
                    Stmt.block
                      (toString loopElimBlockPrefix ++ toString "arbitrary_iter_assumes_" ++ loop_num)
                      (([] : Statements) ++ inv.mapIdx (fun i lp =>
                        Stmt.cmd (HasPassiveCmds.assume
                          (toString loopElimAssumePrefix ++ loop_num ++ toString "_invariant_" ++
                            toString (if lp.fst.isEmpty = Bool.true then toString i
                                      else toString i ++ toString "_" ++ toString lp.fst))
                          lp.2 md)))
                      md] ++ ([] : Statements) ++ body ++
                  inv.mapIdx (fun i lp =>
                    Stmt.cmd (HasPassiveCmds.assert
                      (toString loopElimAssertPrefix ++ loop_num ++
                        toString "_arbitrary_iter_maintain_invariant_" ++
                        toString (if lp.fst.isEmpty = Bool.true then toString i
                                  else toString i ++ toString "_" ++ toString lp.fst))
                      lp.snd md)) ++ ([] : Statements))
                ∅
              :: ([Stmt.block
                    (toString loopElimBlockPrefix ++ toString "loop_havoc_" ++ loop_num)
                    (List.map (fun n => Stmt.cmd (HasHavoc.havoc n md))
                      (List.filter (fun v => decide ¬v ∈ Block.definedVars body Bool.false)
                        (Block.modifiedVars body)))
                    ∅] ++ ([] : Statements) ++
                inv.mapIdx (fun i lp =>
                  Stmt.cmd (HasPassiveCmds.assume
                    (toString loopElimAssumePrefix ++ loop_num ++ toString "_exit_invariant_" ++
                      toString (if lp.fst.isEmpty = Bool.true then toString i
                                else toString i ++ toString "_" ++ toString lp.fst))
                    lp.snd md))))
            [] ∅]
        ∅) = Bool.true := by
  apply defUseWellFormed_buildLoopOutput_form
    (assumeGuard := []) (pre := []) (post := []) (exit := []) (pre_def_true := [])
  · exact h_body_wf
  · exact h_inv_getVars
  · intro n hn; simp [ExprOrNondet.getVars] at hn
  · simp [Block.defUseWellFormed]
  · simp [Block.definedVars]
  · simp [Block.definedVars]
  · simp [Block.defUseWellFormed]
  · intro n hn; simp at hn
  · intro n hn; simp at hn
  · intro n hn; simp at hn
  · simp [Block.defUseWellFormed]
  · simp [Block.definedVars]
  · simp [Block.defUseWellFormed]
  · simp [Block.definedVars]

/-- WF of the loop output for the `.det g, none` case:
    `assumeGuard = [guard_assume]`, `pre = []`, `post = []`,
    `exit = [not_guard_assume]`. -/
private theorem defUseWellFormed_loop_output_detNone
    (loop_num : String) (inv : List (String × Expression.Expr))
    (body : Statements) (md : MetaData Expression)
    (outer : Expression.Ident → Bool)
    (h_body_wf : Block.defUseWellFormed outer body = Bool.true)
    (h_inv_getVars : ∀ n ∈ inv.flatMap (fun lp => HasVarsPure.getVars lp.2),
        outer n = Bool.true)
    (g : Expression.Expr)
    (h_g_getVars : ∀ n ∈ HasVarsPure.getVars g, outer n = Bool.true) :
    Stmt.defUseWellFormed (P := Expression) (C := Command) outer
      (Stmt.block (toString loopElimBlockPrefix ++ toString "loop_" ++ loop_num)
        [Stmt.block
            (toString loopElimBlockPrefix ++ toString "first_iter_asserts_" ++ loop_num)
            (inv.mapIdx (fun i lp =>
               Stmt.cmd (HasPassiveCmds.assert
                 (toString loopElimAssertPrefix ++ loop_num ++ toString "_entry_invariant_" ++
                   toString (if lp.fst.isEmpty = Bool.true then toString i
                             else toString i ++ toString "_" ++ toString lp.fst))
                 lp.snd md)) ++
             inv.mapIdx (fun i lp =>
               Stmt.cmd (HasPassiveCmds.assume
                 (toString loopElimAssumePrefix ++ loop_num ++ toString "_entry_invariant_" ++
                   toString (if lp.fst.isEmpty = Bool.true then toString i
                             else toString i ++ toString "_" ++ toString lp.fst))
                 lp.snd md)))
            ∅,
          Stmt.ite (.det g)
            (Stmt.block
                (toString loopElimBlockPrefix ++ toString "arbitrary_iter_facts_" ++ loop_num)
                ([Stmt.block
                      (toString loopElimBlockPrefix ++ toString "loop_havoc_" ++ loop_num)
                      (List.map (fun n => Stmt.cmd (HasHavoc.havoc n md))
                        (List.filter (fun v => decide ¬v ∈ Block.definedVars body Bool.false)
                          (Block.modifiedVars body)))
                      ∅,
                    Stmt.block
                      (toString loopElimBlockPrefix ++ toString "arbitrary_iter_assumes_" ++ loop_num)
                      ([Stmt.cmd (HasPassiveCmds.assume
                          (toString loopElimAssumePrefix ++ loop_num ++ toString "_guard")
                          g md)] ++ inv.mapIdx (fun i lp =>
                        Stmt.cmd (HasPassiveCmds.assume
                          (toString loopElimAssumePrefix ++ loop_num ++ toString "_invariant_" ++
                            toString (if lp.fst.isEmpty = Bool.true then toString i
                                      else toString i ++ toString "_" ++ toString lp.fst))
                          lp.2 md)))
                      md] ++ ([] : Statements) ++ body ++
                  inv.mapIdx (fun i lp =>
                    Stmt.cmd (HasPassiveCmds.assert
                      (toString loopElimAssertPrefix ++ loop_num ++
                        toString "_arbitrary_iter_maintain_invariant_" ++
                        toString (if lp.fst.isEmpty = Bool.true then toString i
                                  else toString i ++ toString "_" ++ toString lp.fst))
                      lp.snd md)) ++ ([] : Statements))
                ∅
              :: ([Stmt.block
                    (toString loopElimBlockPrefix ++ toString "loop_havoc_" ++ loop_num)
                    (List.map (fun n => Stmt.cmd (HasHavoc.havoc n md))
                      (List.filter (fun v => decide ¬v ∈ Block.definedVars body Bool.false)
                        (Block.modifiedVars body)))
                    ∅] ++ [Stmt.cmd (HasPassiveCmds.assume
                      (toString loopElimAssumePrefix ++ loop_num ++ toString "_not_guard")
                      (HasNot.not g) md)] ++
                inv.mapIdx (fun i lp =>
                  Stmt.cmd (HasPassiveCmds.assume
                    (toString loopElimAssumePrefix ++ loop_num ++ toString "_exit_invariant_" ++
                      toString (if lp.fst.isEmpty = Bool.true then toString i
                                else toString i ++ toString "_" ++ toString lp.fst))
                    lp.snd md))))
            [] ∅]
        ∅) = Bool.true := by
  apply defUseWellFormed_buildLoopOutput_form
    (assumeGuard := [Stmt.cmd (HasPassiveCmds.assume
      (toString loopElimAssumePrefix ++ loop_num ++ toString "_guard") g md)])
    (pre := [])
    (post := [])
    (exit := [Stmt.cmd (HasPassiveCmds.assume
      (toString loopElimAssumePrefix ++ loop_num ++ toString "_not_guard")
      (HasNot.not g) md)])
    (pre_def_true := [])
  · exact h_body_wf
  · exact h_inv_getVars
  · intro n hn; simp [ExprOrNondet.getVars] at hn; exact h_g_getVars n hn
  · -- assumeGuard WF
    exact defUseWellFormed_singleton_assume outer _ g md h_g_getVars
  · -- assumeGuard.definedVars true = []
    exact definedVars_true_singleton_assume _ g md
  · -- pre.definedVars true = []
    simp [Block.definedVars]
  · -- pre WF
    simp [Block.defUseWellFormed]
  · intro n hn; simp at hn
  · intro n hn; simp at hn
  · intro n hn; simp at hn
  · simp [Block.defUseWellFormed]
  · simp [Block.definedVars]
  · -- exit WF
    apply defUseWellFormed_singleton_assume
    intro n hn
    -- HasNot.not g's getVars ⊆ g's getVars.
    exact h_g_getVars n (mem_getVars_not_subset hn)
  · -- exit.definedVars true = []
    exact definedVars_true_singleton_assume _ _ md

/-- WF of the loop output for the `.det g, some m` case:
    `assumeGuard = [guard_assume]`, `pre = [m_old_init, measure_lb]`,
    `post = [measure_decrease]`, `exit = [not_guard_assume]`. -/
private theorem defUseWellFormed_loop_output_detSome
    (loop_num : String) (inv : List (String × Expression.Expr))
    (body : Statements) (md : MetaData Expression)
    (outer : Expression.Ident → Bool)
    (h_body_wf : Block.defUseWellFormed outer body = Bool.true)
    (h_inv_getVars : ∀ n ∈ inv.flatMap (fun lp => HasVarsPure.getVars lp.2),
        outer n = Bool.true)
    (g : Expression.Expr)
    (h_g_getVars : ∀ n ∈ HasVarsPure.getVars g, outer n = Bool.true)
    (m : Expression.Expr)
    (h_m_getVars : ∀ n ∈ HasVarsPure.getVars m, outer n = Bool.true)
    -- m_old freshness: not in body's touchedVars, not in outer.
    (h_m_old_notin_body : (HasIdent.ident (toString "$__loop_measure_" ++ loop_num)
        : Expression.Ident) ∉ Block.touchedVars body)
    (h_m_old_not_outer : outer (HasIdent.ident (toString "$__loop_measure_" ++ loop_num)
        : Expression.Ident) = Bool.false)
    (h_m_old_notin_body_def : (HasIdent.ident (toString "$__loop_measure_" ++ loop_num)
        : Expression.Ident) ∉ Block.definedVars body Bool.false)
    -- Note: the goal's m_old is `(HasIdent.ident ...)` but the body's touched vars
    -- include `m`'s getVars and `g`'s getVars in outer, so m_old can't be among them
    -- by freshness.  But since m_old ∉ outer, m_old ∉ inv_getVars and m_old ∉ g_getVars
    -- (by `defUseWellFormed_loop` originally).  The user passes these directly.
    (h_m_old_notin_inv : (HasIdent.ident (toString "$__loop_measure_" ++ loop_num)
        : Expression.Ident) ∉ inv.flatMap (fun lp => HasVarsPure.getVars lp.2))
    (h_m_old_notin_g : (HasIdent.ident (toString "$__loop_measure_" ++ loop_num)
        : Expression.Ident) ∉ HasVarsPure.getVars g) :
    Stmt.defUseWellFormed (P := Expression) (C := Command) outer
      (Stmt.block (toString loopElimBlockPrefix ++ toString "loop_" ++ loop_num)
        [Stmt.block
            (toString loopElimBlockPrefix ++ toString "first_iter_asserts_" ++ loop_num)
            (inv.mapIdx (fun i lp =>
               Stmt.cmd (HasPassiveCmds.assert
                 (toString loopElimAssertPrefix ++ loop_num ++ toString "_entry_invariant_" ++
                   toString (if lp.fst.isEmpty = Bool.true then toString i
                             else toString i ++ toString "_" ++ toString lp.fst))
                 lp.snd md)) ++
             inv.mapIdx (fun i lp =>
               Stmt.cmd (HasPassiveCmds.assume
                 (toString loopElimAssumePrefix ++ loop_num ++ toString "_entry_invariant_" ++
                   toString (if lp.fst.isEmpty = Bool.true then toString i
                             else toString i ++ toString "_" ++ toString lp.fst))
                 lp.snd md)))
            ∅,
          Stmt.ite (.det g)
            (Stmt.block
                (toString loopElimBlockPrefix ++ toString "arbitrary_iter_facts_" ++ loop_num)
                ([Stmt.block
                      (toString loopElimBlockPrefix ++ toString "loop_havoc_" ++ loop_num)
                      (List.map (fun n => Stmt.cmd (HasHavoc.havoc n md))
                        (List.filter (fun v => decide ¬v ∈ Block.definedVars body Bool.false)
                          (Block.modifiedVars body)))
                      ∅,
                    Stmt.block
                      (toString loopElimBlockPrefix ++ toString "arbitrary_iter_assumes_" ++ loop_num)
                      ([Stmt.cmd (HasPassiveCmds.assume
                          (toString loopElimAssumePrefix ++ loop_num ++ toString "_guard")
                          g md)] ++ inv.mapIdx (fun i lp =>
                        Stmt.cmd (HasPassiveCmds.assume
                          (toString loopElimAssumePrefix ++ loop_num ++ toString "_invariant_" ++
                            toString (if lp.fst.isEmpty = Bool.true then toString i
                                      else toString i ++ toString "_" ++ toString lp.fst))
                          lp.2 md)))
                      md] ++ [Stmt.cmd (HasInit.init
                        (HasIdent.ident (toString "$__loop_measure_" ++ loop_num))
                        HasIntOrder.intTy (.det m) md),
                      Stmt.cmd (HasPassiveCmds.assert
                        (toString loopElimAssertPrefix ++ loop_num ++ toString "_measure_lb")
                        (HasNot.not (HasIntOrder.lt
                          (HasFvar.mkFvar (HasIdent.ident
                            (toString "$__loop_measure_" ++ loop_num)))
                          HasIntOrder.zero)) md)] ++ body ++
                  inv.mapIdx (fun i lp =>
                    Stmt.cmd (HasPassiveCmds.assert
                      (toString loopElimAssertPrefix ++ loop_num ++
                        toString "_arbitrary_iter_maintain_invariant_" ++
                        toString (if lp.fst.isEmpty = Bool.true then toString i
                                  else toString i ++ toString "_" ++ toString lp.fst))
                      lp.snd md)) ++
                  [Stmt.cmd (HasPassiveCmds.assert
                    (toString loopElimAssertPrefix ++ loop_num ++ toString "_measure_decrease")
                    (HasIntOrder.lt m
                      (HasFvar.mkFvar (HasIdent.ident
                        (toString "$__loop_measure_" ++ loop_num)))) md)])
                ∅
              :: ([Stmt.block
                    (toString loopElimBlockPrefix ++ toString "loop_havoc_" ++ loop_num)
                    (List.map (fun n => Stmt.cmd (HasHavoc.havoc n md))
                      (List.filter (fun v => decide ¬v ∈ Block.definedVars body Bool.false)
                        (Block.modifiedVars body)))
                    ∅] ++ [Stmt.cmd (HasPassiveCmds.assume
                      (toString loopElimAssumePrefix ++ loop_num ++ toString "_not_guard")
                      (HasNot.not g) md)] ++
                inv.mapIdx (fun i lp =>
                  Stmt.cmd (HasPassiveCmds.assume
                    (toString loopElimAssumePrefix ++ loop_num ++ toString "_exit_invariant_" ++
                      toString (if lp.fst.isEmpty = Bool.true then toString i
                                else toString i ++ toString "_" ++ toString lp.fst))
                    lp.snd md))))
            [] ∅]
        ∅) = Bool.true := by
  -- Set up the m_old identifier as a single-element list for pre_def_true.
  let m_old : Expression.Ident :=
    HasIdent.ident (toString "$__loop_measure_" ++ loop_num)
  have hm_old : m_old = HasIdent.ident (toString "$__loop_measure_" ++ loop_num) := rfl
  apply defUseWellFormed_buildLoopOutput_form
    (assumeGuard := [Stmt.cmd (HasPassiveCmds.assume
      (toString loopElimAssumePrefix ++ loop_num ++ toString "_guard") g md)])
    (pre := [Stmt.cmd (HasInit.init m_old HasIntOrder.intTy (.det m) md),
             Stmt.cmd (HasPassiveCmds.assert
               (toString loopElimAssertPrefix ++ loop_num ++ toString "_measure_lb")
               (HasNot.not (HasIntOrder.lt
                 (HasFvar.mkFvar m_old) HasIntOrder.zero)) md)])
    (post := [Stmt.cmd (HasPassiveCmds.assert
      (toString loopElimAssertPrefix ++ loop_num ++ toString "_measure_decrease")
      (HasIntOrder.lt m (HasFvar.mkFvar m_old)) md)])
    (exit := [Stmt.cmd (HasPassiveCmds.assume
      (toString loopElimAssumePrefix ++ loop_num ++ toString "_not_guard")
      (HasNot.not g) md)])
    (pre_def_true := [m_old])
  · exact h_body_wf
  · exact h_inv_getVars
  · intro n hn; simp [ExprOrNondet.getVars] at hn; exact h_g_getVars n hn
  · -- assumeGuard WF
    exact defUseWellFormed_singleton_assume outer _ g md h_g_getVars
  · -- assumeGuard.definedVars true = []
    exact definedVars_true_singleton_assume _ g md
  · -- pre.definedVars true = [m_old]
    simp [Block.definedVars, Stmt.definedVars, HasVarsImp.definedVars,
          HasInit.init, HasPassiveCmds.assert, Command.definedVars, Cmd.definedVars]
  · -- pre WF
    apply defUseWellFormed_cons_intro
    · -- init m_old: m_old ∉ outer (so the "fresh" check passes)
      simp only [Stmt.defUseWellFormed, HasVarsPure.getVars, HasVarsImp.modifiedVars,
        HasVarsImp.definedVars, HasInit.init, Command.getVars, Command.modifiedVars,
        Command.definedVars, Cmd.getVars, Cmd.modifiedVars, Cmd.definedVars,
        ExprOrNondet.getVars, List.all_nil, Bool.and_true, Bool.true_and]
      rw [Bool.and_eq_true]
      refine ⟨?_, ?_⟩
      · rw [List.all_eq_true]; exact h_m_getVars
      · simp only [List.all_cons, List.all_nil, Bool.and_true]
        rw [hm_old, h_m_old_not_outer]; rfl
    · -- After init, outer is extended by [m_old].
      apply defUseWellFormed_cons_intro
      · -- assert measure_lb: getVars = [m_old]; m_old now in extended outer.
        simp only [Stmt.defUseWellFormed, HasVarsPure.getVars, HasVarsImp.modifiedVars,
          HasVarsImp.definedVars, HasPassiveCmds.assert, Command.getVars,
          Command.modifiedVars, Command.definedVars, Cmd.getVars, Cmd.modifiedVars,
          Cmd.definedVars, List.all_nil, Bool.and_true, Bool.true_and]
        rw [List.all_eq_true]
        intro n hn
        -- n ∈ HasNot.not (m_old < 0) → n is m_old (or in 0's getVars, which is []).
        simp only [Bool.or_eq_true, decide_eq_true_eq, Stmt.definedVars,
          HasVarsImp.definedVars, HasInit.init, Command.definedVars, Cmd.definedVars,
          List.mem_singleton]
        right
        -- Need: n = m_old.  hn : n ∈ getVars (¬ (m_old < 0))
        have hn' := mem_getVars_not_subset hn
        have h2 := mem_getVars_lt_split hn'
        rcases h2 with hl | hr
        · simpa [Lambda.LExpr.LExpr.getVars, HasFvar.mkFvar] using hl
        · simp [Lambda.LExpr.LExpr.getVars] at hr
      · simp [Block.defUseWellFormed]
  · -- pre_def disjoint from body (m_old ∉ body's touched vars)
    intro n hn
    simp at hn; subst hn
    simp [Block.touchedVars, Block.modifiedOrDefinedVars, List.mem_append] at h_m_old_notin_body
    refine ⟨?_, ?_, ?_⟩
    · exact h_m_old_notin_body.1
    · exact h_m_old_notin_body.2.2
    · exact h_m_old_notin_body_def
  · -- pre_def disjoint from inv.flatMap getVars
    intro n hn
    simp at hn; subst hn; exact h_m_old_notin_inv
  · -- pre_def disjoint from g.getVars
    intro n hn
    simp at hn; subst hn; exact h_m_old_notin_g
  · -- post WF (against outer + [m_old] + body.definedVars true)
    apply defUseWellFormed_cons_intro
    · simp only [Stmt.defUseWellFormed, HasVarsPure.getVars, HasVarsImp.modifiedVars,
        HasVarsImp.definedVars, HasPassiveCmds.assert, Command.getVars,
        Command.modifiedVars, Command.definedVars, Cmd.getVars, Cmd.modifiedVars,
        Cmd.definedVars, List.all_nil, Bool.and_true, Bool.true_and]
      rw [List.all_eq_true]
      intro n hn
      -- n ∈ getVars (m < m_old) → n in m's getVars or n = m_old.
      simp only [Bool.or_eq_true, decide_eq_true_eq]
      have h2 := mem_getVars_lt_split hn
      rcases h2 with hl | hr
      · -- n in m's getVars, so n in outer.
        left; left; exact h_m_getVars n hl
      · -- n in getVars (mkFvar m_old), so n = m_old.
        have hmo : n = m_old := by
          simpa [Lambda.LExpr.LExpr.getVars, HasFvar.mkFvar] using hr
        left; right; rw [List.mem_singleton]; exact hmo
    · simp [Block.defUseWellFormed]
  · -- post.definedVars true = []
    simp [Block.definedVars, Stmt.definedVars, HasVarsImp.definedVars,
      HasPassiveCmds.assert, Command.definedVars, Cmd.definedVars]
  · -- exit WF: not_guard assume.
    apply defUseWellFormed_singleton_assume
    intro n hn
    -- HasNot.not g's getVars ⊆ g's getVars.
    exact h_g_getVars n (mem_getVars_not_subset hn)
  · -- exit.definedVars true = []
    exact definedVars_true_singleton_assume _ _ md

/-- Loop case helper: well-formedness of the loop encoding's output.

    The transform produces
       block loop_label [first_iter_facts, ite guard (arb_facts :: exit_state) [] {}]
    which we must show is `defUseWellFormed` against `outer`.  The freshness
    side conditions mean every transform-introduced name (block labels,
    havoc'd vars from the body, m_old) doesn't collide with `outer`. -/
private theorem defUseWellFormed_stmtResult_loop
    (σ : LoopElimState)
    (guard : ExprOrNondet Expression)
    (measure : Option Expression.Expr)
    (inv : List (String × Expression.Expr))
    (body : Statements) (md : MetaData Expression)
    (hok : stmtOk σ (.loop guard measure inv body md))
    (outer : Expression.Ident → Bool)
    (h_outer_fresh : ∀ n, outer n = Bool.true →
      ¬ loopElimReservedPrefix.toList.isPrefixOf n.name.toList)
    (h_def_not_reserved : ∀ n ∈ Block.definedVars body false,
      ¬ loopElimReservedPrefix.toList.isPrefixOf n.name.toList)
    (hwf : Stmt.defUseWellFormed outer
            (.loop guard measure inv body md) = Bool.true) :
    Stmt.defUseWellFormed outer
      (stmtResult σ (.loop guard measure inv body md)) = Bool.true := by
  -- Extract loop-level WF facts from `hwf`.
  unfold Stmt.defUseWellFormed at hwf
  simp only [Bool.and_eq_true] at hwf
  obtain ⟨⟨⟨h_guard_all, h_meas_all⟩, h_inv_all⟩, h_body_wf⟩ := hwf
  rw [List.all_eq_true] at h_guard_all h_meas_all h_inv_all
  -- The output: stmtResult on the source loop is the transform's output.
  -- We use the structural lemma `definedVars_subset_stmtResult_loop` style of unfolding.
  -- Strategy: every (n ∈ touchedVars (stmtResult σ ...)) lies in
  -- (touchedVars source) ∪ (definedVars (stmtResult σ ...)).  Combined with
  -- `outer`-monotone over source touched vars (from hwf) plus the body's
  -- inner well-formedness, we directly call `defUseWellFormed_outer_extend_stmt`
  -- on a "source statement minus m_old reservation" framing.
  --
  -- Easier path: directly induct on the structure exposed by stmtResult_loop_struct.
  -- But the loop output has many nested pieces; rather than go that way, we
  -- use the `defUseWellFormed_touched_notDef` family in reverse: a statement is
  -- well-formed against outer if every (touched but not defined) name is in outer.
  -- However, no such "reverse" lemma is currently available.
  --
  -- Direct approach: apply the structural unfolding (4-way split on guard×measure)
  -- as in `mem_definedVars_stmtResult_loop` etc., then for each concrete output
  -- prove `Stmt.defUseWellFormed outer ...` via the piece-wise helpers.
  show Stmt.defUseWellFormed outer
      (match (stmtRun σ (.loop guard measure inv body md)).fst with
       | .ok (_, s') => s' | .error _ => default) = Bool.true
  have hok' := hok
  unfold stmtOk at hok'
  -- Two `m_old`-related freshness facts proved up-front (we'll discharge them
  -- whenever needed in the .det / .some m branch).
  have h_m_old_pref : ∀ ln,
      loopElimReservedPrefix.toList.isPrefixOf
        ((⟨"$__loop_measure_" ++ ln, ()⟩ : Expression.Ident).name.toList) :=
    fun ln => loopElimReservedPrefix_isPrefixOf_measure ln
  have h_m_old_not_outer : ∀ ln, outer (⟨"$__loop_measure_" ++ ln, ()⟩ : Expression.Ident) = Bool.false := by
    intro ln
    cases hh : outer ⟨"$__loop_measure_" ++ ln, ()⟩ with
    | false => rfl
    | true => exact absurd (h_m_old_pref ln) (h_outer_fresh _ hh)
  have h_m_old_notin_body_def : ∀ ln,
      (⟨"$__loop_measure_" ++ ln, ()⟩ : Expression.Ident) ∉ Block.definedVars body false :=
    fun ln h => h_def_not_reserved _ h (h_m_old_pref ln)
  match h : (stmtRun σ (.loop guard measure inv body md)).fst with
  | .error _ => simp [h, Except.isOk, Except.toBool] at hok'
  | .ok (b, s') =>
    simp only [h]
    dsimp only [stmtRun, StateT.run, ExceptT.run, Stmt.removeLoopsM, removeLoopsLoopCase,
      buildLoopOutput, buildLoopPassive, buildArbitraryIterFacts, buildArbitraryIterAssumes,
      buildExitStateAssumes, buildHavocBlock, buildFirstIterFacts, buildEntryInvariants,
      buildEntryInvariantAssumes, buildInvAssumes, buildMaintainInvariants,
      buildExitInvariantAssumes, buildGuardParts, buildTerminationStmtsSome,
      hasLabelConflict, numAssertAssumesForLoop, invSuffix, measureOldIdent,
      bind, pure, ExceptT.bind, ExceptT.pure, ExceptT.mk, ExceptT.bindCont,
      ExceptT.lift, StateT.bind, StateT.pure,
      Functor.map, liftM, monadLift, MonadLift.monadLift,
      modify, MonadState.modifyGet, StateT.modifyGet, StateT.map,
      genLoopNum, bumpStat] at h
    -- Split on the `if hasLabelConflict then throw else pure`, then on guard,
    -- then on measure, mirroring the case structure of
    -- `definedVars_subset_stmtResult_loop`.  In each successful branch the
    -- equation `h` exposes a concrete `s'`, which is one of three concrete
    -- outputs of `buildLoopOutput`.  We then prove `defUseWellFormed` for that
    -- output by the master helper `defUseWellFormed_buildLoopOutput_form`.
    repeat (first | contradiction | (split at h; skip))
    -- For the `.det / .some m` case, `h` still has `StateT.pure …  .bind …`
    -- around the freshness check; unfold and split again.
    all_goals (first | contradiction | (
      try (unfold StateT.pure at h
           dsimp only [StateT.bind, StateT.map, ExceptT.bindCont, ExceptT.bind,
             ExceptT.pure, ExceptT.mk, ExceptT.lift, bind, pure,
             Functor.map, MonadState.modifyGet, StateT.modifyGet,
             MonadStateOf.modifyGet, bumpStat, modify, genLoopNum] at h
           repeat (first | contradiction | (split at h; skip)))
      all_goals (first
        | contradiction
        | (obtain ⟨_, rfl⟩ := h))))
    -- After all branching, three remaining goals: `.det g, none`, `.det g, some m`, `.nondet`.
    -- Dispatch each by the corresponding case-specific helper.
    case h_1.isFalse =>
      -- det g, none
      rename_i _hcheck _guard0 g0 _meas _hnone
      exact defUseWellFormed_loop_output_detNone _ inv body md outer
        h_body_wf h_inv_all g0
        (fun n hn => h_guard_all n
          (by show n ∈ (ExprOrNondet.det g0 : ExprOrNondet Expression).getVars
              simp [ExprOrNondet.getVars]; exact hn))
    case h_2.isFalse.isTrue =>
      -- det g, some m
      rename_i _hcheck _guard0 g0 _meas m0 h_freshness _h_some
      apply defUseWellFormed_loop_output_detSome _ inv body md outer
        h_body_wf h_inv_all g0
        (fun n hn => h_guard_all n
          (by show n ∈ (ExprOrNondet.det g0 : ExprOrNondet Expression).getVars
              simp [ExprOrNondet.getVars]; exact hn))
        m0
        (fun n hn => h_meas_all n
          (by simp [ExprOrNondet.getVars]; exact hn))
      · exact h_freshness
      · exact h_m_old_not_outer _
      · exact h_m_old_notin_body_def _
      · intro hmem
        have hh := h_inv_all _ hmem
        have hf := h_m_old_not_outer (toString (StringGenState.gen "loop" σ.gen).fst)
        have hh' : outer (⟨"$__loop_measure_" ++ toString (StringGenState.gen "loop" σ.gen).fst, ()⟩ : Expression.Ident) = Bool.true := by simpa using hh
        rw [hf] at hh'
        exact Bool.false_ne_true hh'
      · intro hmem
        have hh := h_guard_all _
          (by show _ ∈ (ExprOrNondet.det g0 : ExprOrNondet Expression).getVars
              simp [ExprOrNondet.getVars]; exact hmem)
        have hf := h_m_old_not_outer (toString (StringGenState.gen "loop" σ.gen).fst)
        have hh' : outer (⟨"$__loop_measure_" ++ toString (StringGenState.gen "loop" σ.gen).fst, ()⟩ : Expression.Ident) = Bool.true := by simpa using hh
        rw [hf] at hh'
        exact Bool.false_ne_true hh'
    case h_2 =>
      -- nondet
      exact defUseWellFormed_loop_output_nondet _ inv body md outer
        h_body_wf h_inv_all

-- Structural well-formedness preservation for `stmtResult` / `blockResult`.
--
-- Two side conditions on the outer scope `outer` propagate through the
-- recursion:
-- * `h_outer_fresh`: `outer n = true` implies `n.name` does NOT have the
--   reserved `$__loop` prefix.  This is provided initially by
--   `InitEnvWF.reservedFresh`.
-- * `h_def_not_reserved`: every var in the SOURCE statement's
--   `definedVars false` does NOT have the reserved prefix.  This is
--   provided initially by `InitEnvWF.definedVarsNotReserved` (with the
--   reserved list still containing `loopElimReservedPrefix`).
--
-- These two facts together let the cons-tail case discharge the freshness
-- side condition for the extended outer (which adds the source's scoped
-- definedVars to the outer scope).
mutual
private theorem defUseWellFormed_stmtResultAux
    (σ : LoopElimState) (s : Statement) (hok : stmtOk σ s)
    (outer : Expression.Ident → Bool)
    (h_outer_fresh : ∀ n, outer n = Bool.true →
      ¬ loopElimReservedPrefix.toList.isPrefixOf n.name.toList)
    (h_def_not_reserved : ∀ n ∈ Stmt.definedVars s false,
      ¬ loopElimReservedPrefix.toList.isPrefixOf n.name.toList)
    (hwf : Stmt.defUseWellFormed outer s = Bool.true) :
    Stmt.defUseWellFormed outer (stmtResult σ s) = Bool.true := by
  match s with
  | .cmd c => rw [stmtResult_cmd]; exact hwf
  | .exit l md => rw [stmtResult_exit]; exact hwf
  | .funcDecl d md => rw [stmtResult_funcDecl]; exact hwf
  | .typeDecl tc md => rw [stmtResult_typeDecl]; exact hwf
  | .block l bss md =>
    rw [stmtResult_block]
    have hwf' : Block.defUseWellFormed outer bss = Bool.true := by
      simpa [defUseWellFormed_block] using hwf
    have hdef_block : ∀ n ∈ Block.definedVars bss false,
        ¬ loopElimReservedPrefix.toList.isPrefixOf n.name.toList := by
      intro n hn
      apply h_def_not_reserved n
      show n ∈ Stmt.definedVars (s := Stmt.block l bss md) false
      simpa [Stmt.definedVars] using hn
    have ih := defUseWellFormed_blockResultAux σ bss (stmtOk_block_inner hok) outer
                h_outer_fresh hdef_block hwf'
    simpa [defUseWellFormed_block] using ih
  | .ite c tss ess md =>
    rw [stmtResult_ite]
    have ⟨hwf_t, hwf_e⟩ := defUseWellFormed_ite_branches hwf
    have hcond : ∀ n ∈ ExprOrNondet.getVars c, outer n = Bool.true := by
      intro n hn
      have h := hwf
      unfold Stmt.defUseWellFormed at h
      simp only [Bool.and_eq_true] at h
      have hcond_all := h.1.1
      rw [List.all_eq_true] at hcond_all
      exact hcond_all n hn
    have hdef_t : ∀ n ∈ Block.definedVars tss false,
        ¬ loopElimReservedPrefix.toList.isPrefixOf n.name.toList := by
      intro n hn
      apply h_def_not_reserved n
      show n ∈ Stmt.definedVars (s := Stmt.ite c tss ess md) false
      simp [Stmt.definedVars]; exact .inl hn
    have hdef_e : ∀ n ∈ Block.definedVars ess false,
        ¬ loopElimReservedPrefix.toList.isPrefixOf n.name.toList := by
      intro n hn
      apply h_def_not_reserved n
      show n ∈ Stmt.definedVars (s := Stmt.ite c tss ess md) false
      simp [Stmt.definedVars]; exact .inr hn
    have ih_t := defUseWellFormed_blockResultAux σ tss (stmtOk_ite_left hok) outer
                  h_outer_fresh hdef_t hwf_t
    have ih_e := defUseWellFormed_blockResultAux (blockPostState σ tss) ess
                  (stmtOk_ite_right hok) outer h_outer_fresh hdef_e hwf_e
    unfold Stmt.defUseWellFormed
    simp only [Bool.and_eq_true]
    refine ⟨⟨?_, ih_t⟩, ih_e⟩
    rw [List.all_eq_true]
    exact hcond
  | .loop guard measure inv body md =>
    have hdef_body : ∀ n ∈ Block.definedVars body false,
        ¬ loopElimReservedPrefix.toList.isPrefixOf n.name.toList := by
      intro n hn
      apply h_def_not_reserved n
      show n ∈ Stmt.definedVars (s := Stmt.loop guard measure inv body md) false
      simpa [Stmt.definedVars] using hn
    exact defUseWellFormed_stmtResult_loop σ guard measure inv body md hok outer
      h_outer_fresh hdef_body hwf

private theorem defUseWellFormed_blockResultAux
    (σ : LoopElimState) (bss : Statements) (hok : blockOk σ bss)
    (outer : Expression.Ident → Bool)
    (h_outer_fresh : ∀ n, outer n = Bool.true →
      ¬ loopElimReservedPrefix.toList.isPrefixOf n.name.toList)
    (h_def_not_reserved : ∀ n ∈ Block.definedVars bss false,
      ¬ loopElimReservedPrefix.toList.isPrefixOf n.name.toList)
    (hwf : Block.defUseWellFormed outer bss = Bool.true) :
    Block.defUseWellFormed outer (blockResult σ bss) = Bool.true := by
  match bss with
  | [] => rw [blockResult_nil]; rfl
  | s :: rest =>
    rw [blockResult_cons]
    have ⟨hwf_s, hwf_rest⟩ := defUseWellFormed_cons hwf
    have hdef_s : ∀ n ∈ Stmt.definedVars s false,
        ¬ loopElimReservedPrefix.toList.isPrefixOf n.name.toList := by
      intro n hn
      apply h_def_not_reserved n
      simp [Block.definedVars]; exact .inl hn
    have hdef_rest : ∀ n ∈ Block.definedVars rest false,
        ¬ loopElimReservedPrefix.toList.isPrefixOf n.name.toList := by
      intro n hn
      apply h_def_not_reserved n
      simp [Block.definedVars]; exact .inr hn
    have ih_s := defUseWellFormed_stmtResultAux σ s (blockOk_cons_left hok) outer
                  h_outer_fresh hdef_s hwf_s
    apply defUseWellFormed_cons_intro ih_s
    -- Tail's outer is extended by `Stmt.definedVars (stmtResult σ s) true`.
    -- Use `stmtResult_definedVars_true_eq` to align that with `Stmt.definedVars s true`.
    have hdef_eq : Stmt.definedVars (stmtResult σ s) true = Stmt.definedVars s true :=
      stmtResult_definedVars_true_eq σ s (blockOk_cons_left hok)
    have h_new_outer_fresh : ∀ n, (outer n || decide (n ∈ Stmt.definedVars s true)) = Bool.true →
        ¬ loopElimReservedPrefix.toList.isPrefixOf n.name.toList := by
      intro n hn
      simp only [Bool.or_eq_true, decide_eq_true_eq] at hn
      rcases hn with h | h
      · exact h_outer_fresh n h
      · -- n ∈ Stmt.definedVars s true → n ∈ Stmt.definedVars s false (by subset).
        exact hdef_s n (stmt_definedVars_true_subset_false s n h)
    have ih_rest := defUseWellFormed_blockResultAux (stmtPostState σ s) rest
      (blockOk_cons_right hok) (fun n => outer n || decide (n ∈ Stmt.definedVars s true))
      h_new_outer_fresh hdef_rest hwf_rest
    have hcongr : ∀ n,
        (outer n || decide (n ∈ Stmt.definedVars (stmtResult σ s) true)) =
        (outer n || decide (n ∈ Stmt.definedVars s true)) := by
      intro n; rw [hdef_eq]
    rw [defUseWellFormed_block_congr hcongr (blockResult (stmtPostState σ s) rest)]
    exact ih_rest
end

/-- Top-level wrapper for the structural lemma, taking an `InitEnvWF` and
    extracting both `h_outer_fresh` and `h_def_not_reserved` from it. -/
private theorem defUseWellFormed_stmtResult
    (σ : LoopElimState) (s : Statement) (hok : stmtOk σ s)
    (reserved : List String)
    (h_loop_reserved : loopElimReservedPrefix ∈ reserved)
    {ρ₀ : Env Expression}
    (hswf : InitEnvWF reserved s ρ₀) :
    Stmt.defUseWellFormed (fun n => (ρ₀.store n).isSome) (stmtResult σ s) = Bool.true := by
  apply defUseWellFormed_stmtResultAux σ s hok (fun n => (ρ₀.store n).isSome)
  · intro n hsome hpref
    exact hswf.reservedFresh n hsome loopElimReservedPrefix h_loop_reserved hpref
  · intro n hn hpref
    exact hswf.definedVarsNotReserved n hn loopElimReservedPrefix h_loop_reserved hpref
  · exact hswf.defUseOk

theorem loopElim_overapproximatesAggressive
    (hwf_ext : WFEvalExtension φ) (σ : LoopElimState) :
    Transform.OverapproximatesAggressively
      (LangCore π φ)
      (LangCore π φ)
      (fun s => open Classical in
                if Stmt.noFuncDecl s = Bool.true ∧ stmtOk σ s
                then some (stmtResult σ s) else none)
      loopElimReservedPrefix := by
  intro reserved st st' ht h_loop_reserved h_pd ρ₀ hswf
  -- hswf has type (LangCore π φ).initEnvWF reserved st ρ₀, which unfolds to
  -- InitEnvWF reserved st ρ₀.  We extract its WF eval fields explicitly.
  have hswf' : InitEnvWF reserved st ρ₀ := hswf
  have hwfb := hswf'.wfBool
  have hwfv := hswf'.wfVal
  have hwfvar := hswf'.wfVar
  simp only at ht
  split at ht
  · rename_i hcond
    obtain ⟨hnofd, hok⟩ := hcond
    simp only [Option.some.injEq] at ht; subst ht
    -- Derive the freshness precondition for `simulation`/`canfail_simulation`
    -- generically over `reserved` (matches the new signature).
    have hreserved_sig : ∀ n, (ρ₀.store n).isSome →
        ∀ p ∈ reserved, ¬ p.toList.isPrefixOf n.name.toList :=
      fun n hsome p hp => hswf.reservedFresh n hsome p hp
    -- `loopElimReservedPrefixSig` and `loopElimReservedPrefix` are definitionally
    -- equal (both `"$__loop"`); this lets us discharge `simulation`'s
    -- `h_loop_reserved` premise from the top-level `h_loop_reserved`.
    have h_loop_reserved' : loopElimReservedPrefixSig ∈ reserved := h_loop_reserved
    have hsim := (simulation π φ hwf_ext (Stmt.sizeOf st) reserved h_loop_reserved').1
      σ st (Nat.le_refl _) hnofd hok ρ₀ hswf'
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro ρ' hstar; exact hsim.1 ρ' hstar
    · intro lbl ρ' hstar; exact hsim.2 lbl ρ' hstar
    · intro ⟨cfg, hfail, hreach⟩
      by_cases hnf₀ : ρ₀.hasFailure = Bool.true
      · exact ⟨.stmt (stmtResult σ st) ρ₀, by show ρ₀.hasFailure = Bool.true; exact hnf₀, .refl _⟩
      · exact (canfail_simulation π φ hwf_ext (Stmt.sizeOf st) reserved h_loop_reserved').1
          σ st (Nat.le_refl _) hok hnofd ρ₀ hswf' ⟨cfg, hfail, hreach⟩
    · -- Show `InitEnvWF reserved (stmtResult σ st) ρ₀` from `InitEnvWF reserved st ρ₀`.
      -- The transform's fresh `$__loop_measure_N` names start with the reserved
      -- prefix `$__loop`; `hswf.reservedFresh` rules them out of `ρ₀.store`.
      -- The output InitEnvWF uses `reserved.erase loopElimReservedPrefix` since
      -- the output may have introduced names with `loopElimReservedPrefix`.
      refine
        { readWritesDefined := ?readWritesDefined,
          defsUndefined := ?defsUndefined,
          definedVarsNotReserved := ?definedVarsNotReserved,
          reservedFresh := ?reservedFresh,
          wfBool := hswf.wfBool,
          wfVal := hswf.wfVal,
          wfVar := hswf.wfVar,
          evalCong := hswf.evalCong,
          exprCongr := hswf.exprCongr,
          defUseOk := ?defUseOk }
      case readWritesDefined =>
        intro n hn hnd
        have ⟨hn_src, hnd_src⟩ := mem_touchedVars_stmtResult σ st hok n hn hnd
        exact hswf.readWritesDefined n hn_src hnd_src
      case defsUndefined =>
        intro n hn
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
      case reservedFresh =>
        -- Weaker than the input since `reserved.erase` is a subset.
        intro n hsome p hp_mem
        exact hswf.reservedFresh n hsome p (List.mem_of_mem_erase hp_mem)
      case definedVarsNotReserved =>
        -- Output's `definedVarsNotReserved` for `reserved.erase loopElimReservedPrefix`.
        -- Each n in transform's definedVars is either in source's definedVars
        -- or has the `loopElimReservedPrefix` prefix (per `mem_definedVars_stmtResult`).
        intro n hn p hp_mem
        rcases mem_definedVars_stmtResult σ st hok n hn with hold | hpref
        · -- Source's defs don't have any prefix from `reserved`, hence not from
          -- `reserved.erase loopElimReservedPrefix` (a subset).
          exact hswf.definedVarsNotReserved n hold p (List.mem_of_mem_erase hp_mem)
        · -- n has `loopElimReservedPrefix` as prefix.  Suppose for contradiction
          -- p is also a prefix of n.  Then since both `p` and `loopElimReservedPrefix`
          -- are prefixes of `n.name`, one of them is a prefix of the other.
          -- But `h_pd` says they're prefix-disjoint — contradiction.
          intro h_p_prefix
          have ⟨h_pd_left, h_pd_right⟩ := h_pd p hp_mem
          -- Two `Char`-list prefixes of the same list: one is a prefix of the other.
          have h_pp_or : p.toList.isPrefixOf loopElimReservedPrefix.toList = Bool.true ∨
                        loopElimReservedPrefix.toList.isPrefixOf p.toList = Bool.true := by
            -- Use the helper: two prefixes of the same list are comparable.
            have h1 : p.toList.IsPrefix n.name.toList := by
              rw [List.isPrefixOf_iff_prefix] at h_p_prefix; exact h_p_prefix
            have h2 : loopElimReservedPrefix.toList.IsPrefix n.name.toList := by
              rw [List.isPrefixOf_iff_prefix] at hpref; exact hpref
            rcases List.prefix_or_prefix_of_prefix h1 h2 with h | h
            · left; rw [List.isPrefixOf_iff_prefix]; exact h
            · right; rw [List.isPrefixOf_iff_prefix]; exact h
          rcases h_pp_or with h | h
          · exact h_pd_left h
          · exact h_pd_right h
      case defUseOk =>
        exact defUseWellFormed_stmtResult σ st hok reserved
          h_loop_reserved hswf'
  · exact absurd ht (by nofun)

end Core.LoopElim

end -- public section
