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

Generic properties of the event-trace relation `StepKleeneE`, independent of
any particular program transformation.

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

/-- Monotonicity of `StepKleeneE` in the command relation: if `EvalCmd` implies
`EvalCmd'` pointwise, every `StepKleeneE` step for `EvalCmd` is a `StepKleeneE`
step for `EvalCmd'`.  The control-flow rules are command-agnostic; only
`step_cmd` uses the hypothesis. -/
theorem StepKleeneE.imp
    {CmdT : Type} {EventT : Type _} {P : PureExpr} [HasBool P] [HasBoolOps P]
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
    {CmdT : Type} {EventT : Type _} {evalCmd : EvalCmdParamE P CmdT EventT}
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
    {CmdT : Type} {EventT : Type _} {evalCmd : EvalCmdParamE P CmdT EventT}
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
    {CmdT : Type} {EventT : Type _} {evalCmd : EvalCmdParamE P CmdT EventT}
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
    {CmdT : Type} {EventT : Type _} {evalCmd : EvalCmdParamE P CmdT EventT}
    {left right : KleeneStmt P CmdT} {ρ : Env P}
    {trace : List EventT} {cfg : KleeneConfig P CmdT}
    (h : StepKleeneStarE P evalCmd (.stmt left ρ) trace cfg) :
    StepKleeneStarE P evalCmd (.stmt (.choice left right) ρ) trace cfg :=
  .step _ _ _ _ _ StepKleeneE.step_choice_left h

/-- Prefix a traced run of a choice's right branch with the right-choice step. -/
theorem kleene_choice_right_traceE
    {P : PureExpr} [HasBool P] [HasBoolOps P]
    {CmdT : Type} {EventT : Type _} {evalCmd : EvalCmdParamE P CmdT EventT}
    {left right : KleeneStmt P CmdT} {ρ : Env P}
    {trace : List EventT} {cfg : KleeneConfig P CmdT}
    (h : StepKleeneStarE P evalCmd (.stmt right ρ) trace cfg) :
    StepKleeneStarE P evalCmd (.stmt (.choice left right) ρ) trace cfg :=
  .step _ _ _ _ _ StepKleeneE.step_choice_right h

/-- A Kleene loop may exit immediately, emitting no events. -/
theorem kleene_loop_zero_traceE
    {P : PureExpr} [HasBool P] [HasBoolOps P]
    {CmdT : Type} {EventT : Type _} {evalCmd : EvalCmdParamE P CmdT EventT}
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
