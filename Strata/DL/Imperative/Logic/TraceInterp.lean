/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.DL.Imperative.CmdTrace

/-! # Deductive trace interpretation

Defines semantic neutrality, assumption satisfaction, trace reachability,
assertion validity and satisfiability, and cover satisfiability over interpreted
command events.
The `*From` definitions are recursive workers carrying assumptions accumulated
before the remaining trace.
-/

namespace Imperative

public section

section

variable (P : PureExpr)

/-- Interprets captured conditions in a semantic world shared by every
condition in a trace. -/
structure ConditionInterp (P : PureExpr) where
  /-- Shared semantic worlds in which captured conditions are interpreted. -/
  World : Type
  /-- Whether a captured event condition holds in a semantic world. -/
  holds : World → EventArg P → Prop

/-- Interpretation of event conditions using the partial evaluator. -/
@[expose] def EvaluatorBasedInterp (P : PureExpr) [HasBool P] :
    ConditionInterp P where
  World := Unit
  holds := fun _ c => P.eval c.factory c.store c.expr = some HasBool.tt

/-- An event is semantically neutral when its condition holds in every world. -/
@[expose] def Event.neutral (I : ConditionInterp P) : Event P → Prop
  | .assert condition | .assume condition | .cover condition =>
      ∀ world, I.holds world condition

namespace Trace

/-- Every assumption in `trace` holds in `world`. -/
@[expose] def AssumptionsHold (I : ConditionInterp P)
    (world : I.World) (trace : Trace P) : Prop :=
  ∀ condition, Event.assume condition ∈ trace → I.holds world condition

/-- Given a trace, the program state after execution of the trace is reachable
  when its assumptions are jointly satisfiable in one shared semantic world. -/
@[expose] def Reachable (I : ConditionInterp P) (trace : Trace P) : Prop :=
  ∃ world, AssumptionsHold P I world trace

/-- Worker for assertion validity parameterized by the assertion conditions to
keep. The first trace contains assumptions accumulated before the remaining
trace. -/
@[expose] def AssertionsValidFromP
    (I : ConditionInterp P) (keep : EventArg P → Prop) :
    Trace P → Trace P → Prop
  | _, [] => True
  | assumptions, Event.assume condition :: rest =>
      AssertionsValidFromP I keep (assumptions ++ [Event.assume condition]) rest
  | assumptions, Event.assert condition :: rest =>
      (keep condition →
        ∀ world, AssumptionsHold P I world assumptions → I.holds world condition) ∧
      AssertionsValidFromP I keep assumptions rest
  | assumptions, Event.cover _ :: rest =>
      AssertionsValidFromP I keep assumptions rest

/-- Worker for validity of every assertion, with assumptions accumulated before
the remaining trace. -/
@[expose] abbrev AssertionsValidFrom (I : ConditionInterp P) :
    Trace P → Trace P → Prop :=
  AssertionsValidFromP P I (fun _ => True)

/-- Every assertion in the trace holds whenever all assumptions preceding that
particular assertion hold. Later assumptions cannot discharge an earlier
assertion. -/
@[expose] def AssertionsValid (I : ConditionInterp P)
    (trace : Trace P) : Prop :=
  AssertionsValidFrom P I [] trace

/-- Worker for satisfiability of one assertion identifier with assumptions
accumulated before the remaining trace. It succeeds when some matching assertion
occurrence has a world satisfying both its preceding assumptions and captured
condition. -/
@[expose] def AssertionSatisfiableFrom
    (I : ConditionInterp P) (aid : AssertId P) : Trace P → Trace P → Prop
  | _, [] => False
  | assumptions, Event.assume condition :: rest =>
      AssertionSatisfiableFrom I aid
        (assumptions ++ [Event.assume condition]) rest
  | assumptions, Event.assert condition :: rest =>
      ((condition.label = aid.label ∧ condition.expr = aid.expr ∧
        ∃ world, AssumptionsHold P I world assumptions ∧
          I.holds world condition) ∨
        AssertionSatisfiableFrom I aid assumptions rest)
  | assumptions, Event.cover _ :: rest =>
      AssertionSatisfiableFrom I aid assumptions rest

/-- An assertion identifier is satisfiable in a trace when at least one matching
occurrence and all assumptions preceding it hold in one shared world. The
predicate is false when the identifier does not occur in the trace. -/
@[expose] def AssertionSatisfiable
    (I : ConditionInterp P) (aid : AssertId P) (trace : Trace P) : Prop :=
  AssertionSatisfiableFrom P I aid [] trace

/-- Worker for satisfiability of one cover identifier with assumptions
accumulated before the remaining trace. It succeeds when some matching cover
occurrence has a world satisfying both its preceding assumptions and captured
condition. -/
@[expose] def CoverSatisfiableFrom (I : ConditionInterp P) (cid : CoverId P) :
    Trace P → Trace P → Prop
  | _, [] => False
  | assumptions, Event.assume condition :: rest =>
      CoverSatisfiableFrom I cid (assumptions ++ [Event.assume condition]) rest
  | assumptions, Event.cover condition :: rest =>
      (((condition.label, condition.metadata) = cid ∧
        ∃ world, AssumptionsHold P I world assumptions ∧ I.holds world condition) ∨
        CoverSatisfiableFrom I cid assumptions rest)
  | assumptions, Event.assert _ :: rest =>
      CoverSatisfiableFrom I cid assumptions rest

/-- A cover identifier is satisfiable in a trace when at least one matching
occurrence is satisfiable with all assumptions preceding that occurrence. The
predicate is false when the identifier does not occur in the trace. -/
@[expose] def CoverSatisfiable
    (I : ConditionInterp P) (cid : CoverId P) (trace : Trace P) : Prop :=
  CoverSatisfiableFrom P I cid [] trace

/-- Worker for validity of occurrences matching one assertion identifier. -/
@[expose] abbrev AssertionValidFrom
    (I : ConditionInterp P) (aid : AssertId P) : Trace P → Trace P → Prop :=
  AssertionsValidFromP P I
    (fun condition => condition.label = aid.label ∧ condition.expr = aid.expr)

/-- Validity of all occurrences of one assertion identifier in a trace. -/
@[expose] def AssertionValid (I : ConditionInterp P)
    (aid : AssertId P) (trace : Trace P) : Prop :=
  AssertionValidFrom P I aid [] trace

end Trace

end

end -- public section
end Imperative
