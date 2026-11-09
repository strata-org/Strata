/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.DL.Imperative.Logic.TraceInterp
public import Strata.DL.Lambda.LExprDenoteEval
public import Strata.DL.Lambda.LExprDenoteEvalProps
public import Strata.Languages.Core.Expressions

/-! # Denotational interpretation of Core event conditions

Interprets captured Core assertion, assumption, and cover conditions over one
Lambda factory `F`. Core's evaluator is denotational (`Core.Expression.eval` is
`Lambda.LExpr.denoteEval`), and a runtime factory carries a consistent model of its
Lambda factory, so a condition captured under a runtime factory over `F` holds
exactly when it evaluates to `true` in that runtime factory's model: every free
variable is bound to a value of the model, and the condition type checks at `bool`
under the sorts of those values and denotes `true`. For entry environments whose
runtime factory is over `F` (`ρ₀.factory.factory = F`, as `ProcEntryEnv` and
`Procedure.contractTriple` require), every condition a run captures is over `F`,
since steps keep the factory, so quantifying over those entries quantifies over
every model of `F`. This reading is meant for such entries only.

Conditions captured under a runtime factory over another Lambda factory are
interpreted by an arbitrary predicate carried by the world. Quantifying over
worlds then makes every such assertion invalid unless an earlier assumption is the
same condition, so an entry over another factory must not be admitted.

Key definitions: `DenoteValuation`, `DenoteBasedInterp`.
-/

namespace Core.Logic

public section

/-- A world for the conditions over a Lambda factory `F`: the interpretation of conditions
captured under a runtime factory over another Lambda factory. -/
structure DenoteValuation (F : Lambda.Factory Core.CoreLParams) where
  /-- Conservative interpretation of conditions outside the ambient factory. -/
  offFactoryHolds : Imperative.EventArg Core.Expression → Prop

/-- Interpret Core event conditions over the Lambda factory `F`.

A condition captured under a runtime factory over `F` holds when it evaluates to
`true` in that runtime factory. A condition captured under a runtime factory over
another Lambda factory holds when the world's `offFactoryHolds` says so. Using one
predicate per world also preserves propositional relationships between repeated
identical conditions. -/
@[expose] noncomputable def DenoteBasedInterp (F : Lambda.Factory Core.CoreLParams) :
    Imperative.ConditionInterp Core.Expression where
  World := DenoteValuation F
  holds := fun valuation condition =>
    (condition.factory.factory = F ∧
      Core.Expression.eval condition.factory condition.store condition.expr =
        some (Imperative.HasBool.ttVal condition.factory)) ∨
    (condition.factory.factory ≠ F ∧ valuation.offFactoryHolds condition)

end -- public section

end Core.Logic
