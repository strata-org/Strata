/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

meta import Strata.Languages.Core.StatementSemantics

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

/-- A canonical Core value used as the normal form of reducible expressions. -/
def canonicalValue : Expression.Expr := .const () (LConst.intConst 0)

theorem canonicalValue_isValue : Value canonicalValue := .const

/-- A concrete `CoreEval`: look up `fvar`s, act as identity on values, and
    reduce everything else to `canonicalValue`. -/
def coreWitnessEval : CoreEval := fun σ e =>
  match e with
  | .fvar _ x _ => σ x
  | .const _ c  => some (.const () c)
  | .bvar _ i   => some (.bvar () i)
  | .op _ o ty  => some (.op () o ty)
  | .abs _ n ty b => some (.abs () n ty b)
  | _ => some canonicalValue

/-- On a free-variable atom the witness returns the store binding. -/
theorem coreWitnessEval_wfVar : WellFormedSemanticEvalVar coreWitnessEval := by
  intro e v σ _hwfs hget
  cases e <;> simp_all only [HasFvar.getFvar, coreWitnessEval, reduceCtorEq]
  cases hget
  rfl

/-- Every witness output on a well-formed store is a value, and the witness is
    the identity on values. -/
theorem coreWitnessEval_wfVal : WellFormedSemanticEvalVal coreWitnessEval := by
  refine ⟨?_, ?_⟩
  · -- outputs are values (using well-formedness of the store for the fvar case)
    intro e v σ hwfs heval
    cases e with
    | fvar m x ty =>
      -- output is `σ x`; `WellFormedStore σ` makes it a value
      simp only [coreWitnessEval] at heval
      exact hwfs x v heval
    | const m c   => simp only [coreWitnessEval] at heval; cases heval; exact .const
    | bvar m i    => simp only [coreWitnessEval] at heval; cases heval; exact .bvar
    | op m o ty   => simp only [coreWitnessEval] at heval; cases heval; exact .op
    | abs m n ty b => simp only [coreWitnessEval] at heval; cases heval; exact .abs
    | app m f a   => simp only [coreWitnessEval] at heval; cases heval; exact canonicalValue_isValue
    | ite m c t e => simp only [coreWitnessEval] at heval; cases heval; exact canonicalValue_isValue
    | eq m a b    => simp only [coreWitnessEval] at heval; cases heval; exact canonicalValue_isValue
    | quant m k n ty tr b =>
      simp only [coreWitnessEval] at heval; cases heval; exact canonicalValue_isValue
  · -- identity on values
    intro v σ hv
    cases hv with
    | const => rfl
    | bvar  => rfl
    | op    => rfl
    | abs   => rfl

/-- A Core evaluator bundled with the well-formedness conditions that
    `EvalCommand.call_sem` requires. -/
structure WFCoreEval where
  eval : CoreEval
  wfVar : WellFormedSemanticEvalVar eval
  wfVal : WellFormedSemanticEvalVal eval

/-- `WFCoreEval` is inhabited (witnessed by `coreWitnessEval`), so the
    conditions `call_sem` requires are satisfiable — i.e. `call_sem` is not
    vacuous. -/
instance : Inhabited WFCoreEval :=
  ⟨coreWitnessEval, coreWitnessEval_wfVar, coreWitnessEval_wfVal⟩

/-- Corollary: the conjunction is inhabitable by a genuine evaluator. -/
theorem exists_wf_coreEval :
    ∃ δ : CoreEval, WellFormedSemanticEvalVar δ ∧ WellFormedSemanticEvalVal δ :=
  ⟨(default : WFCoreEval).eval, (default : WFCoreEval).wfVar, (default : WFCoreEval).wfVal⟩

end

end Core
