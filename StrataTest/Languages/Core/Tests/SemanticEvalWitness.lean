/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

meta import Strata.Languages.Core.StatementSemantics
import Strata.DL.Lambda.Semantics

/-!
# A concrete evaluator satisfying the semantic well-formedness conditions

`EvalCommand.call_sem` requires its evaluator `δ : CoreEval` to satisfy
`WellFormedSemanticEvalVal` and `WellFormedSemanticEvalVar` simultaneously.
This file exhibits a concrete `CoreEval` (`coreWitnessEval`) that provably
satisfies both, witnessing that those conditions are jointly inhabitable.

The evaluator follows the shape of a real expression evaluator:

* on a free-variable atom it returns the store binding (`HasFvar.getFvar`
  behavior — this is what `WellFormedSemanticEvalVar` constrains);
* on a value (`const`/`bvar`/`op`/`abs`) it is the identity (so it satisfies the
  identity-on-values half of `WellFormedSemanticEvalVal`);
* on any other (reducible) expression it normalizes to a canonical value.

This witness preserves value-ness but not typing — e.g. a boolean expression
normalizes to the integer `canonicalValue`. That suffices here: the
well-formedness predicates constrain value-ness, not types.

The two conditions are jointly satisfiable because they only constrain
value-only stores (`WellFormedStore`): on such a store the free-variable lookup
returns a value, so it agrees with the "every output is a value" requirement.
-/

namespace Core

open Imperative
open Lambda (LExpr LConst)

meta section

/-- A concrete `CoreEval`: identity on canonical values, store lookup on fvars,
    constant otherwise. -/
def coreWitnessEval : CoreEval := fun f σ e =>
  if Lambda.LExpr.isCanonicalValue f e then some e
  else match e with
  | .fvar _ x _ => σ x
  | _ => some (.const () (LConst.intConst 0))

/-- Canonical values have no free variables, so they are not fvars. -/
private theorem canonical_not_fvar (f : Expression.Factory)
    (e : Expression.Expr) (hcan : Lambda.LExpr.isCanonicalValue f e = true) :
    HasFvar.getFvar (P := Expression) e = none := by
  cases e with
  | fvar m x ty =>
    have h_no_vars := Lambda.isCanonicalValue_getVars_nil f _ hcan
    simp [Lambda.LExpr.LExpr.getVars] at h_no_vars
  | _ => rfl

/-- On a free-variable atom the witness returns the store binding. -/
theorem coreWitnessEval_wfVar (f : Expression.Factory) :
    WellFormedSemanticEvalVar coreWitnessEval f := by
  intro e v σ _hwfs hget
  simp only [coreWitnessEval]
  have h_not_can : Lambda.LExpr.isCanonicalValue f e ≠ true := by
    intro hcan
    have h := canonical_not_fvar f e hcan
    simp [h] at hget
  rw [if_neg h_not_can]
  cases e with
  | fvar m x ty =>
    simp only [HasFvar.getFvar] at hget; cases hget; rfl
  | _ => simp [HasFvar.getFvar] at hget

/-- Every witness output on a well-formed store is a value, and the witness is
    the identity on values. -/
theorem coreWitnessEval_wfVal (f : Expression.Factory) :
    WellFormedSemanticEvalVal coreWitnessEval f := by
  constructor
  · -- outputsAreValues
    intro e v σ hwfs heval
    simp only [coreWitnessEval] at heval
    split at heval
    · -- isCanonicalValue f e = true, output is e
      rename_i h_can
      cases heval; exact h_can
    · -- not canonical
      cases e with
      | fvar m x ty =>
        exact hwfs x v heval
      | _ =>
        simp at heval; cases heval
        show Lambda.LExpr.isCanonicalValue _ _ = true
        unfold Lambda.LExpr.isCanonicalValue; rfl
  · -- identityOnValues
    intro v σ hv
    simp only [HasVal.value] at hv
    simp only [coreWitnessEval, hv, ite_true]

/-- Corollary: the conjunction is inhabitable by a genuine evaluator. -/
theorem exists_wf_coreEval (f : Expression.Factory) :
    ∃ δ : CoreEval, WellFormedSemanticEvalVar δ f ∧ WellFormedSemanticEvalVal δ f :=
  ⟨coreWitnessEval, coreWitnessEval_wfVar f, coreWitnessEval_wfVal f⟩

end

end Core
