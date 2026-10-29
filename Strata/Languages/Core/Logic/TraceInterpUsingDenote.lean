/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.DL.Imperative.Logic.TraceInterp
public import Strata.DL.Lambda.Denote.LExprDenote
public import Strata.Languages.Core.Expressions

/-! # Denotational interpretation of Core event conditions

Interprets captured Core assertion, assumption, and cover conditions with
`Lambda.LExpr.denote`. A fixed ambient `Lambda.Interp F` supplies the semantic
model. Worlds carry type- and free-variable valuations together with an
arbitrary predicate for conditions captured under other factories. All
ambient-factory conditions in a trace share one model and one valuation.

The captured store is substituted into each expression before denotation.  This
preserves the event's state snapshot while allowing one shared valuation across
events emitted before and after assignments.  Conditions must remain
well-typed at `bool` after substitution; ill-typed conditions do not hold.
-/

namespace Core.Logic

public section

/-- A valuation in one fixed denotational model. Quantification over these
worlds gives universal closure of residual type and free variables while keeping
assumptions and assertions in the same valuation. Conditions captured under a
different factory are interpreted by an arbitrary shared predicate. -/
structure DenoteValuation {F : Core.Expression.Factory}
    (model : Lambda.Interp F) where
  tyVarVal : Lambda.TyVarVal
  freeVarVal : Lambda.FreeVarVal Core.CoreLParams model.tcInterp
  /-- Conservative interpretation of conditions outside the ambient factory. -/
  offFactoryHolds : Imperative.EventArg Core.Expression → Prop

/-- Substitute the store captured by an event into its condition expression. -/
@[expose] def capturedExpr
    (condition : Imperative.EventArg Core.Expression) : Core.Expression.Expr :=
  Lambda.LExpr.substFvarsFromEnv (T := Core.CoreLParams)
    (Lambda.Env.mk condition.store) condition.expr

/-- Interpret Core event conditions in one consistent Lambda model.

Conditions captured under the ambient factory use `Lambda.LExpr.denote`.
Conditions from another factory use the world's arbitrary `offFactoryHolds`
predicate because the ambient model cannot interpret them. Quantification over
worlds then prevents an off-factory assumption from vacuously validating an
unrelated assertion: the predicate may make the assumption true and the
assertion false. Using one predicate per world also preserves propositional
relationships between repeated identical conditions. -/
@[expose] noncomputable def DenoteBasedInterp
    {F : Core.Expression.Factory} (model : Lambda.Interp F) :
    Imperative.ConditionInterp Core.Expression where
  World := DenoteValuation model
  holds := fun valuation condition =>
    (condition.factory = F ∧
      ∃ h : Lambda.LExpr.HasTypeA [] (capturedExpr condition) .bool,
        (Lambda.LExpr.denote model.tcInterp model.opInterp
          valuation.freeVarVal valuation.tyVarVal .nil
          (capturedExpr condition) .bool h : Bool) = true) ∨
    (condition.factory ≠ F ∧ valuation.offFactoryHolds condition)

end -- public section

end Core.Logic
