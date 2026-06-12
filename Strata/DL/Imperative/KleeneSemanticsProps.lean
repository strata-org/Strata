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

<<<<<<< HEAD
variable {P : PureExpr} [HasFvar P] [HasBool P] [HasNot P] [HasVal P] [HasBoolVal P]
  [HasVarsPure P P.Expr]
=======
variable {P : PureExpr} [HasFvar P] [HasBool P] [HasBoolOps P]
>>>>>>> origin/main2

/-! ## Env helpers -/

omit [HasFvar P] [HasBool P] [HasBoolOps P] in
theorem assume_env_eq (ρ : Env P) :
    ({ ρ with store := ρ.store, hasFailure := ρ.hasFailure || false } : Env P) = ρ := by
  cases ρ; simp [Bool.or_false]

omit [HasFvar P] [HasBoolOps P] in
theorem eval_tt_is_tt
    (δ : SemanticEval P) (σ : SemanticStore P)
    (hwfv : WellFormedSemanticEvalVal δ) :
    δ σ HasBool.tt = some HasBool.tt :=
  hwfv.2 HasBool.tt σ HasBool.boolIsVal.1

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
    (hcond : ρ₀.eval ρ₀.store expr = some HasBool.tt)
    (hwfb : WellFormedSemanticEvalBool ρ₀.eval)
    (hwfc : WellFormedSemanticEvalExprCongr ρ₀.eval) :
    StepKleeneStar P (EvalCmd P)
      (.stmt (.cmd (.assume label expr md)) ρ₀) (.terminal ρ₀) := by
  have raw : StepKleeneStar P (EvalCmd P)
      (.stmt (.cmd (.assume label expr md)) ρ₀)
      (.terminal { ρ₀ with store := ρ₀.store, hasFailure := ρ₀.hasFailure || false }) :=
    .step _ _ _ (.step_cmd (EvalCmd.eval_assume hcond hwfb hwfc)) (.refl _)
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

end -- public section
end Imperative
