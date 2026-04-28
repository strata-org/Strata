/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.DL.Imperative.KleeneStmtSemantics
import all Strata.DL.Imperative.CmdSemantics
import all Strata.DL.Util.Relations

/-! # Properties of Kleene (nondeterministic) small-step semantics

Generic helpers for `StepKleene` / `StepKleeneStar` that are independent
of any particular program transformation. -/

namespace Imperative

public section

variable {P : PureExpr} [HasFvar P] [HasBool P] [HasNot P] [HasVal P] [HasBoolVal P]

/-! ## Env helpers -/

omit [HasFvar P] [HasVal P] [HasBool P] [HasNot P] in
theorem assume_env_eq (ρ : Env P) :
    ({ ρ with store := ρ.store, hasFailure := ρ.hasFailure || false } : Env P) = ρ := by
  cases ρ; simp [Bool.or_false]

omit [HasFvar P] [HasNot P] in
theorem eval_tt_is_tt
    (δ : SemanticEval P) (σ : SemanticStore P)
    (hwfv : WellFormedSemanticEvalVal δ) :
    δ σ HasBool.tt = some HasBool.tt :=
  hwfv.2 HasBool.tt σ HasBoolVal.bool_is_val.1

/-! ## Kleene small-step helpers -/

omit [HasVal P] [HasBoolVal P] in
theorem kleene_seq_inner_star
    (inner inner' : KleeneConfig P (Cmd P)) (s2 : KleeneStmt P (Cmd P))
    (h : StepKleeneStar P (EvalCmd P) inner inner') :
    StepKleeneStar P (EvalCmd P) (.seq inner s2) (.seq inner' s2) := by
  induction h with
  | refl => exact .refl _
  | step _ mid _ hstep _ ih => exact .step _ _ _ (.step_seq_inner hstep) ih

omit [HasVal P] [HasBoolVal P] in
theorem kleene_seq_terminal
    (s1 s2 : KleeneStmt P (Cmd P)) (ρ ρ₁ ρ' : Env P)
    (h1 : StepKleeneStar P (EvalCmd P) (.stmt s1 ρ) (.terminal ρ₁))
    (h2 : StepKleeneStar P (EvalCmd P) (.stmt s2 ρ₁) (.terminal ρ')) :
    StepKleeneStar P (EvalCmd P) (.stmt (.seq s1 s2) ρ) (.terminal ρ') :=
  .step _ _ _ .step_seq (ReflTrans_Transitive _ _ _ _
    (ReflTrans_Transitive _ _ _ _ (kleene_seq_inner_star _ _ s2 h1)
      (.step _ _ _ .step_seq_done (.refl _))) h2)

omit [HasVal P] [HasBoolVal P] in
theorem kleene_assume_terminal
    {label : String} {expr : P.Expr} {md : MetaData P} {ρ₀ : Env P}
    (hcond : ρ₀.eval ρ₀.store expr = some HasBool.tt)
    (hwfb : WellFormedSemanticEvalBool ρ₀.eval) :
    StepKleeneStar P (EvalCmd P)
      (.stmt (.cmd (.assume label expr md)) ρ₀) (.terminal ρ₀) := by
  have raw : StepKleeneStar P (EvalCmd P)
      (.stmt (.cmd (.assume label expr md)) ρ₀)
      (.terminal { ρ₀ with store := ρ₀.store, hasFailure := ρ₀.hasFailure || false }) :=
    .step _ _ _ (.step_cmd (EvalCmd.eval_assume hcond hwfb)) (.refl _)
  rwa [assume_env_eq] at raw

end -- public section
end Imperative
