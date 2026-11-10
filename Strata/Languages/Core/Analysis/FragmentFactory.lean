/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Core.Factory
public import Strata.Languages.Core.ProgramFact

/-! # Factories that keep programs in the same-theory fragment

`FragmentFactory F`: what the phases after `typeCheck` need of the factory they evaluate
with, so that evaluation keeps a program in the same-theory fragment. It depends only on the
factory, not on any phase, so any phase can require it of the factory it starts with.
-/

namespace Core.Specification.Analysis

public section

/-- **A factory that keeps programs in the same-theory fragment when it evaluates**: its
    functions have no body; each evaluator returns a literal, in SMT-LIB's string alphabet
    when its arguments are, or the second of exactly two arguments (as the connectives
    `Bool.And`, `Bool.Or` and `Bool.Implies` do, keeping the polarity of that position);
    and the real operations the fragment reads literals through (`Real.Neg`, `Real.Mul`,
    `Real.Div`) do not evaluate, so a literal operand stays one. -/
structure FragmentFactory (F : Lambda.Factory CoreLParams) : Prop where
  noBody : ∀ fn ∈ F.toArray, fn.body = none
  evalShape : ∀ fn ∈ F.toArray, ∀ ceval, fn.concreteEval = some ceval →
    ∀ md args r, ceval md args = some r →
      ((∃ m c, r = .const m c) ∧
          ((∀ a ∈ args, StrLitsInAlphabet a = Bool.true) → StrLitsInAlphabet r = Bool.true)) ∨
        ∃ x, args = [x, r]
  realUneval : ∀ fn ∈ F.toArray, fn.name.name ∈ ["Real.Neg", "Real.Mul", "Real.Div"] →
    fn.concreteEval = none

end -- public section

end Core.Specification.Analysis
