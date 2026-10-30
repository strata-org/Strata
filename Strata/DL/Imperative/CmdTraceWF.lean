/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.DL.Imperative.CmdTrace
public import Strata.DL.Imperative.CmdSemantics

/-! # Semantic well-formedness of captured events

Each event captures the factory and store at the moment it is emitted.
`EventArg.SemanticWF` records that the captured store holds only values and
that the captured factory's evaluator respects free-variable store agreement.
`Event.semanticWF` and `Trace.semanticWF` lift it to events and traces.

These definitions depend on the evaluator conditions in
`Strata.DL.Imperative.CmdSemantics`, which itself imports
`Strata.DL.Imperative.CmdTrace`, so they live here rather than beside
`EventArg`.
-/

namespace Imperative

public section

/-- Semantic evidence carried by an event-argument snapshot. -/
structure EventArg.SemanticWF {P : PureExpr} [HasVal P] [HasFvars P]
    (arg : EventArg P) : Prop where
  storeWellDefined : WellFormedStore arg.store arg.factory
  exprCongr : WellFormedSemanticEvalExprCongr arg.factory

/-- Semantic evidence carried by an event snapshot. -/
@[expose] def Event.semanticWF {P : PureExpr} [HasVal P] [HasFvars P] :
    Event P → Prop
  | .assert arg | .assume arg | .cover arg => arg.SemanticWF

/-- Every event snapshot in a trace is semantically well formed. -/
@[expose] def Trace.semanticWF {P : PureExpr} [HasVal P] [HasFvars P]
    (trace : Trace P) : Prop :=
  ∀ event ∈ trace, Event.semanticWF event

/-- Semantic snapshot evidence composes across trace concatenation. -/
theorem Trace.semanticWF_append {P : PureExpr} [HasVal P] [HasFvars P]
    {first second : Trace P} (hfirst : Trace.semanticWF first)
    (hsecond : Trace.semanticWF second) : Trace.semanticWF (first ++ second) := by
  intro event hevent
  exact (List.mem_append.mp hevent).elim (hfirst event) (hsecond event)

end -- public section

end Imperative
