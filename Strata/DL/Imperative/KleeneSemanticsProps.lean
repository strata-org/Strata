/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.DL.Imperative.KleeneStmtSemantics
import all Strata.DL.Imperative.CmdSemantics
import all Strata.Util.Relations
import all Strata.Util.RelationsProps

/-! # Properties of Kleene (nondeterministic) small-step semantics

Generic helpers for `StepKleene` / `StepKleeneStar` that are independent
of any particular program transformation, and properties of the event-trace
relation `StepKleeneE`.

Key theorems:
* `StepKleeneE.imp` — `StepKleeneE` is monotone in its command relation.
* `stepKleeneStarE_seq_inner` / `stepKleeneStarE_block_inner` — lift a traced
  Kleene run through a `seq` / `block` context.
* `kleene_assume_traceE` — an `assume` command emits its captured condition.
* `kleene_seq_traceE` — chain a terminating left run with a right run.
* `kleene_choice_left_traceE` / `kleene_choice_right_traceE` — prefix a branch
  run with the corresponding choice step.
* `kleene_loop_zero_traceE` — a loop may exit immediately, emitting nothing.
* `stepKleeneE_preserves_factory` / `stepKleeneStarE_preserves_factory` —
  canonical Kleene execution never changes the factory. -/

namespace Imperative

public section

variable {P : PureExpr} [HasFvar P] [HasBool P] [HasBoolOps P]

/-! ## Env helpers -/

omit [HasFvar P] [HasBool P] [HasBoolOps P] in
theorem assume_env_eq (ρ : Env P) :
    ({ ρ with store := ρ.store, hasFailure := ρ.hasFailure || false } : Env P) = ρ := by
  cases ρ; simp [Bool.or_false]

omit [HasFvar P] [HasBoolOps P] in
theorem eval_tt_is_tt [LawfulHasVal P]
    (σ : SemanticStore P) (f : P.Factory)
    (hwfv : WellFormedSemanticEvalVal (P := P) f) :
    P.eval f σ HasBool.tt = some HasBool.tt :=
  hwfv.identityOnValues HasBool.tt σ (HasBool.boolIsVal f).1

/-! ## Kleene small-step helpers -/

theorem kleene_block_inner_star
    (σ_parent : SemanticStore P)
    (inner inner' : KleeneConfig P (Cmd P))
    (h : StepKleeneStar P (EvalCmd P) inner inner') :
    StepKleeneStar P (EvalCmd P) (.block σ_parent inner) (.block σ_parent inner') := by
  induction h with
  | refl => exact .refl _
  | step _ mid _ hstep _ ih => exact .step _ _ _ (.step_block_body hstep) ih

/-- Lift an inner execution through a block wrapper to terminal (with projection). -/
theorem kleene_block_terminal
    (σ_parent : SemanticStore P)
    (inner : KleeneConfig P (Cmd P)) (ρ' : Env P)
    (h : StepKleeneStar P (EvalCmd P) inner (.terminal ρ')) :
    StepKleeneStar P (EvalCmd P) (.block σ_parent inner)
      (.terminal { ρ' with store := projectStore σ_parent ρ'.store }) :=
  ReflTrans_Transitive _ _ _ _
    (kleene_block_inner_star σ_parent inner (.terminal ρ') h)
    (.step _ _ _ .step_block_done (.refl _))

theorem kleene_seq_inner_star
    (inner inner' : KleeneConfig P (Cmd P)) (s2 : KleeneStmt P (Cmd P))
    (h : StepKleeneStar P (EvalCmd P) inner inner') :
    StepKleeneStar P (EvalCmd P) (.seq inner s2) (.seq inner' s2) := by
  induction h with
  | refl => exact .refl _
  | step _ mid _ hstep _ ih => exact .step _ _ _ (.step_seq_inner hstep) ih

theorem kleene_seq_terminal
    (s1 s2 : KleeneStmt P (Cmd P)) (ρ ρ₁ ρ' : Env P)
    (h1 : StepKleeneStar P (EvalCmd P) (.stmt s1 ρ) (.terminal ρ₁))
    (h2 : StepKleeneStar P (EvalCmd P) (.stmt s2 ρ₁) (.terminal ρ')) :
    StepKleeneStar P (EvalCmd P) (.stmt (.seq s1 s2) ρ) (.terminal ρ') :=
  .step _ _ _ .step_seq (ReflTrans_Transitive _ _ _ _
    (ReflTrans_Transitive _ _ _ _ (kleene_seq_inner_star _ _ s2 h1)
      (.step _ _ _ .step_seq_done (.refl _))) h2)

theorem kleene_assume_terminal
    {label : String} {expr : P.Expr} {md : MetaData P} {ρ₀ : Env P}
    (hcond : P.eval ρ₀.factory ρ₀.store expr = some HasBool.tt)
    (hwfb : WellFormedSemanticEvalBool (P := P) ρ₀.factory) :
    StepKleeneStar P (EvalCmd P)
      (.stmt (.cmd (.assume label expr md)) ρ₀) (.terminal ρ₀) := by
  have raw : StepKleeneStar P (EvalCmd P)
      (.stmt (.cmd (.assume label expr md)) ρ₀)
      (.terminal { ρ₀ with store := ρ₀.store, hasFailure := ρ₀.hasFailure || false }) :=
    .step _ _ _ (.step_cmd (EvalCmd.eval_assume hcond hwfb)) (.refl _)
  rwa [assume_env_eq] at raw

theorem kleene_assume_then
    {label : String} {expr : P.Expr} {md : MetaData P}
    {b : KleeneStmt P (Cmd P)} {ρ₀ : Env P}
    (h_assume : StepKleeneStar P (EvalCmd P)
      (.stmt (.cmd (.assume label expr md)) ρ₀) (.terminal ρ₀)) :
    StepKleeneStar P (EvalCmd P)
      (.stmt (.seq (.cmd (.assume label expr md)) b) ρ₀) (.stmt b ρ₀) :=
  .step _ _ _ .step_seq
    (ReflTrans_Transitive _ _ _ _
      (kleene_seq_inner_star _ _ b h_assume)
      (.step _ _ _ .step_seq_done (.refl _)))

/-- Monotonicity of `StepKleeneE` in the command relation: if `EvalCmd` implies
`EvalCmd'` pointwise, every `StepKleeneE` step for `EvalCmd` is a `StepKleeneE`
step for `EvalCmd'`.  The control-flow rules are command-agnostic; only
`step_cmd` uses the hypothesis. -/
theorem StepKleeneE.imp
    {CmdT EventT : Type} {P : PureExpr} [HasBool P] [HasBoolOps P]
    {EvalCmd EvalCmd' : EvalCmdParamE P CmdT EventT}
    (h_imp : ∀ fac σ c σ' emitted, EvalCmd fac σ c σ' emitted → EvalCmd' fac σ c σ' emitted)
    {c tr c'}
    (h : StepKleeneE P EvalCmd c tr c') :
    StepKleeneE P EvalCmd' c tr c' := by induction h <;> solve_by_elim

/-! ## Traced (event) Kleene structural helpers -/

/-- Lift a traced Kleene run of a sequence's left config through the sequence
context. -/
theorem stepKleeneStarE_seq_inner
    {P : PureExpr} [HasBool P] [HasBoolOps P]
    {CmdT EventT : Type} {evalCmd : EvalCmdParamE P CmdT EventT}
    {inner inner' : KleeneConfig P CmdT} {right : KleeneStmt P CmdT}
    {trace : List EventT}
    (h : StepKleeneStarE P evalCmd inner trace inner') :
    StepKleeneStarE P evalCmd (.seq inner right) trace (.seq inner' right) := by
  induction h with
  | refl => exact .refl _
  | step _ emitted _ rest _ hstep _ ih =>
      exact .step _ emitted _ rest _ (.step_seq_inner hstep) ih

/-- Lift a traced Kleene run of a block's inner config through the block
context. -/
theorem stepKleeneStarE_block_inner
    {P : PureExpr} [HasBool P] [HasBoolOps P]
    {CmdT EventT : Type} {evalCmd : EvalCmdParamE P CmdT EventT}
    {inner inner' : KleeneConfig P CmdT} {parent : SemanticStore P}
    {trace : List EventT}
    (h : StepKleeneStarE P evalCmd inner trace inner') :
    StepKleeneStarE P evalCmd (.block parent inner) trace (.block parent inner') := by
  induction h with
  | refl => exact .refl _
  | step _ emitted _ rest _ hstep _ ih =>
      exact .step _ emitted _ rest _ (.step_block_body hstep) ih

/-- Executing an `assume` command in the Kleene semantics emits exactly its
captured condition and leaves the store unchanged. -/
theorem kleene_assume_traceE
    {P : PureExpr} [HasFvar P] [HasBool P] [HasBoolOps P]
    (ρ : Env P) (label : String) (expr : P.Expr) (md : MetaData P) :
    StepKleeneStarE P (EvalCmdE P)
      (.stmt (.cmd (.assume label expr md)) ρ)
      [Event.assume (EventArg.mk ρ.factory ρ.store label expr md)]
      (.terminal { ρ with store := ρ.store }) :=
  .step _ _ _ _ _ (StepKleeneE.step_cmd EvalCmdE.eval_assume) (.refl _)

/-- Chain a traced run of a sequence's left branch that terminates with a run
of its right branch. -/
theorem kleene_seq_traceE
    {P : PureExpr} [HasBool P] [HasBoolOps P]
    {CmdT EventT : Type} {evalCmd : EvalCmdParamE P CmdT EventT}
    {left right : KleeneStmt P CmdT} {ρ ρ₁ : Env P}
    {trace₁ trace₂ : List EventT} {cfg₂ : KleeneConfig P CmdT}
    (hleft : StepKleeneStarE P evalCmd (.stmt left ρ) trace₁ (.terminal ρ₁))
    (hright : StepKleeneStarE P evalCmd (.stmt right ρ₁) trace₂ cfg₂) :
    StepKleeneStarE P evalCmd (.stmt (.seq left right) ρ)
      (trace₁ ++ trace₂) cfg₂ := by
  have henter : StepKleeneStarE P evalCmd
      (.stmt (.seq left right) ρ) [] (.seq (.stmt left ρ) right) :=
    .step _ _ _ _ _ StepKleeneE.step_seq (.refl _)
  have hleft' := stepKleeneStarE_seq_inner (right := right) hleft
  have hcontinue : StepKleeneStarE P evalCmd
      (.seq (.terminal ρ₁) right) [] (.stmt right ρ₁) :=
    .step _ _ _ _ _ StepKleeneE.step_seq_done (.refl _)
  simpa using ReflTransTrace.trans _ henter
    (ReflTransTrace.trans _ hleft'
      (ReflTransTrace.trans _ hcontinue hright))

/-- Prefix a traced run of a choice's left branch with the left-choice step. -/
theorem kleene_choice_left_traceE
    {P : PureExpr} [HasBool P] [HasBoolOps P]
    {CmdT EventT : Type} {evalCmd : EvalCmdParamE P CmdT EventT}
    {left right : KleeneStmt P CmdT} {ρ : Env P}
    {trace : List EventT} {cfg : KleeneConfig P CmdT}
    (h : StepKleeneStarE P evalCmd (.stmt left ρ) trace cfg) :
    StepKleeneStarE P evalCmd (.stmt (.choice left right) ρ) trace cfg :=
  .step _ _ _ _ _ StepKleeneE.step_choice_left h

/-- Prefix a traced run of a choice's right branch with the right-choice step. -/
theorem kleene_choice_right_traceE
    {P : PureExpr} [HasBool P] [HasBoolOps P]
    {CmdT EventT : Type} {evalCmd : EvalCmdParamE P CmdT EventT}
    {left right : KleeneStmt P CmdT} {ρ : Env P}
    {trace : List EventT} {cfg : KleeneConfig P CmdT}
    (h : StepKleeneStarE P evalCmd (.stmt right ρ) trace cfg) :
    StepKleeneStarE P evalCmd (.stmt (.choice left right) ρ) trace cfg :=
  .step _ _ _ _ _ StepKleeneE.step_choice_right h

/-- A Kleene loop may exit immediately, emitting no events. -/
theorem kleene_loop_zero_traceE
    {P : PureExpr} [HasBool P] [HasBoolOps P]
    {CmdT EventT : Type} {evalCmd : EvalCmdParamE P CmdT EventT}
    (body : KleeneStmt P CmdT) (ρ : Env P) :
    StepKleeneStarE P evalCmd (.stmt (.loop body) ρ) [] (.terminal ρ) :=
  .step _ _ _ _ _ StepKleeneE.step_loop_zero (.refl _)

/-- A single canonical Kleene event step may change the store but never the
factory. -/
theorem stepKleeneE_preserves_factory
    {P : PureExpr} [HasFvar P] [HasBool P]
    {source target : KleeneConfig P (Cmd P)} {trace : Trace P}
    (h : StepKleeneE P (EvalCmdE P) source trace target) :
    target.getEnv.factory = source.getEnv.factory := by
  induction h with
  | step_seq_inner _ ih => exact ih
  | step_block_body _ ih => exact ih
  | _ => rfl

/-- Canonical Kleene execution changes stores but never changes factories. -/
theorem stepKleeneStarE_preserves_factory
    {P : PureExpr} [HasFvar P] [HasBool P] [HasBoolOps P]
    {source target : KleeneConfig P (Cmd P)} {trace : Trace P}
    (h : StepKleeneStarE P (EvalCmdE P) source trace target) :
    target.getEnv.factory = source.getEnv.factory := by
  induction h with
  | refl => rfl
  | step source emitted mid rest target hstep _ ih =>
      exact ih.trans (stepKleeneE_preserves_factory hstep)

end -- public section
end Imperative
