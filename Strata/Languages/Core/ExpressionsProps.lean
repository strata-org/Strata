/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Core.InstWellFormedSemanticsEval
public import Strata.DL.Lambda.LExprEvalProps
import all Strata.DL.Lambda.LExprEvalProps

public section

/-! # Concrete Core expression evaluator properties

Evaluator laws that depend on Core's concrete expression factory but are not
specific to one value type.

Key result:
- `coreEval_ite` evaluates a conditional whose condition and branches fully
  evaluate.
-/

namespace Core

open Imperative Lambda

/-- If the condition reduces to `boolConst β` and both branches reduce to values,
then the conditional reduces in one extra step to the selected branch. -/
private theorem eval_ite_value
    (f : Expression.Factory) (σ : CoreStore) (m : Unit) (c t e : Expression.Expr)
    (n : Nat) (β : Bool) (tv ev : Expression.Expr)
    (hc : Lambda.LExpr.eval n f σ c = (Lambda.LExpr.boolConst () β, .value true))
    (ht : Lambda.LExpr.eval n f σ t = (tv, .value true))
    (he : Lambda.LExpr.eval n f σ e = (ev, .value true)) :
    Lambda.LExpr.eval (n + 1) f σ (.ite m c t e)
      = ((if β then tv else ev), .value true) := by
  simp only [Lambda.LExpr.eval]
  rw [if_neg (by rw [Lambda.isCanonicalValue_ite_false]; simp), Lambda.callOfLFunc_ite_none]
  cases β with
  | true =>
    simp [Lambda.LExpr.evalCore, Lambda.LExpr.evalIte, hc, ht, Lambda.LExpr.boolConst,
      Lambda.LExpr.EvalResult.isValueTrue, Lambda.LExpr.EvalResult.combineValueFlag]
  | false =>
    simp [Lambda.LExpr.evalCore, Lambda.LExpr.evalIte, hc, he, Lambda.LExpr.boolConst,
      Lambda.LExpr.EvalResult.isValueTrue, Lambda.LExpr.EvalResult.combineValueFlag]

/-- **`ite` on `Core.Factory`.** If the condition fully evaluates to `boolConst β`
and both branches fully evaluate, the conditional fully evaluates to the selected
branch value. -/
theorem coreEval_ite (σ : CoreStore) (m : Unit) (c t e : Expression.Expr)
    (β : Bool) (tv ev : Expression.Expr)
    (hc : Lambda.LExpr.evalFully Core.Factory σ c = some (Lambda.LExpr.boolConst () β))
    (ht : Lambda.LExpr.evalFully Core.Factory σ t = some tv)
    (he : Lambda.LExpr.evalFully Core.Factory σ e = some ev) :
    Lambda.LExpr.evalFully Core.Factory σ (.ite m c t e) = some (if β then tv else ev) := by
  obtain ⟨nc, hnc, _⟩ := Lambda.evalFully_some_exists Core.Factory σ c _ hc
  obtain ⟨nt, hnt, _⟩ := Lambda.evalFully_some_exists Core.Factory σ t _ ht
  obtain ⟨ne, hne, _⟩ := Lambda.evalFully_some_exists Core.Factory σ e _ he
  have hc_max := Lambda.eval_value_true_mono_le Core.Factory σ nc (max (max nc nt) ne)
    (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_left _ _)) c _ hnc
  have ht_max := Lambda.eval_value_true_mono_le Core.Factory σ nt (max (max nc nt) ne)
    (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_left _ _)) t _ hnt
  have he_max := Lambda.eval_value_true_mono_le Core.Factory σ ne (max (max nc nt) ne)
    (Nat.le_max_right _ _) e _ hne
  have hstep := eval_ite_value Core.Factory σ m c t e (max (max nc nt) ne) β tv ev
    hc_max ht_max he_max
  exact Lambda.evalFully_of_value_true Core.Factory σ _ _ _ hstep

end Core

end -- public section
