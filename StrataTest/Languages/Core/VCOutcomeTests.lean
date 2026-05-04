/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Core.Verifier
import Strata.Languages.Core.SarifOutput

/-! ## Tests for VCOutcome

Tests all nine outcome combinations from two-sided verification check,
including predicates, SARIF messages, and SARIF severity levels.
-/

namespace Core
open Strata.SMT
open Core.Sarif
open Core.SMT (Result)

def mkOutcome (satisfiabilityProperty : Result) (validityProperty : Result) : VCOutcome :=
  { satisfiabilityProperty, validityProperty }

inductive OutcomePredicate where
  | passAndReachable
  | alwaysFalseAndReachable
  | canBeTrueOrFalseAndIsReachable
  | unreachable
  | satisfiableValidityUnknown
  | alwaysFalseReachabilityUnknown
  | canBeFalseAndIsReachable
  | passReachabilityUnknown
  | unknown
  deriving DecidableEq, Repr

def OutcomePredicate.eval (p : OutcomePredicate) (o : VCOutcome) : Bool :=
  match p with
  | .passAndReachable => o.passAndReachable
  | .alwaysFalseAndReachable => o.alwaysFalseAndReachable
  | .canBeTrueOrFalseAndIsReachable => o.canBeTrueOrFalseAndIsReachable
  | .unreachable => o.unreachable
  | .satisfiableValidityUnknown => o.satisfiableValidityUnknown
  | .alwaysFalseReachabilityUnknown => o.alwaysFalseReachabilityUnknown
  | .canBeFalseAndIsReachable => o.canBeFalseAndIsReachable
  | .passReachabilityUnknown => o.passReachabilityUnknown
  | .unknown => o.unknown

def allPredicates : List OutcomePredicate :=
  [.passAndReachable, .alwaysFalseAndReachable, .canBeTrueOrFalseAndIsReachable, .unreachable,
   .satisfiableValidityUnknown, .alwaysFalseReachabilityUnknown, .canBeFalseAndIsReachable,
   .passReachabilityUnknown, .unknown]

def testOutcome (o : VCOutcome) (expectedTrue : OutcomePredicate) : IO Unit := do
  -- Test base predicates are mutually exclusive
  for p in allPredicates do
    if p == expectedTrue then
      if !p.eval o then IO.eprintln s!"ERROR: Expected {repr p} to be true but was false"
    else
      if p.eval o then IO.eprintln s!"ERROR: Expected {repr p} to be false but was true"
  -- Test derived predicates
  let derivedResults := [
    ("isPass", o.isPass),
    ("isSatisfiable", o.isSatisfiable),
    ("isAlwaysFalse", o.isAlwaysFalse),
    ("isAlwaysTrue", o.isAlwaysTrue),
    ("isReachable", o.isReachable)
  ]
  for (name, value) in derivedResults do
    if value then IO.print s!" {name}"
  let satStr := if let .sat _ := o.satisfiabilityProperty then "sat" else if let .unsat := o.satisfiabilityProperty then "unsat" else "unknown"
  let valStr := if let .sat _ := o.validityProperty then "sat" else if let .unsat := o.validityProperty then "unsat" else "unknown"
  IO.println s!"\nSat:{satStr}|Val:{valStr} {o.emoji .assert .full .deductive} {o.label .assert .full .deductive}, {outcomeToMessage o}, SARIF: Deductive level: {outcomeToLevel .deductive .assert o}, BugFinding level: {outcomeToLevel .bugFinding .assert o}"

/-! ### Outcome: (sat, unsat) - always true and reachable -/

/--
info:  isPass isSatisfiable isAlwaysTrue isReachable
Sat:sat|Val:unsat ✅ always true and is reachable from declaration entry, Always true and reachable, SARIF: Deductive level: none, BugFinding level: none
-/
#guard_msgs in
#eval testOutcome (mkOutcome (.sat default) .unsat) .passAndReachable

/--
info:  isAlwaysFalse isReachable
Sat:unsat|Val:sat ❌ always false and is reachable from declaration entry, Always false and reachable, SARIF: Deductive level: error, BugFinding level: error
-/
#guard_msgs in
#eval testOutcome (mkOutcome .unsat (.sat default)) .alwaysFalseAndReachable

/--
info:  isSatisfiable isReachable
Sat:sat|Val:sat 🔶 can be both true and false and is reachable from declaration entry, True or false depending on inputs, SARIF: Deductive level: error, BugFinding level: note
-/
#guard_msgs in
#eval testOutcome (mkOutcome (.sat default) (.sat default)) .canBeTrueOrFalseAndIsReachable

/--
info:  isPass isAlwaysTrue
Sat:unsat|Val:unsat ✅ pass (❗path unreachable), Unreachable: path condition is contradictory, SARIF: Deductive level: warning, BugFinding level: error
-/
#guard_msgs in
#eval testOutcome (mkOutcome .unsat .unsat) .unreachable

/--
info:  isSatisfiable
Sat:sat|Val:unknown ➕ can be true and is reachable from declaration entry, Can be true, unknown if always true, SARIF: Deductive level: error, BugFinding level: note
-/
#guard_msgs in
#eval testOutcome (mkOutcome (.sat default) (Imperative.SMT.Result.unknown (Ident := Core.Expression.Ident))) .satisfiableValidityUnknown

/--
info:  isAlwaysFalse
Sat:unsat|Val:unknown ✖️ always false if reached, Always false if reached, reachability unknown, SARIF: Deductive level: error, BugFinding level: error
-/
#guard_msgs in
#eval testOutcome (mkOutcome .unsat (Imperative.SMT.Result.unknown (Ident := Core.Expression.Ident))) .alwaysFalseReachabilityUnknown

/--
info:
Sat:unknown|Val:sat ➖ can be false and is reachable from declaration entry, Can be false and is reachable, unknown if always false, SARIF: Deductive level: error, BugFinding level: note
-/
#guard_msgs in
#eval testOutcome (mkOutcome (Imperative.SMT.Result.unknown (Ident := Core.Expression.Ident)) (.sat default)) .canBeFalseAndIsReachable

/--
info:  isPass isAlwaysTrue
Sat:unknown|Val:unsat ✔️ always true if reached, Always true if reached, reachability unknown, SARIF: Deductive level: none, BugFinding level: none
-/
#guard_msgs in
#eval testOutcome (mkOutcome (Imperative.SMT.Result.unknown (Ident := Core.Expression.Ident)) .unsat) .passReachabilityUnknown

/--
info:
Sat:unknown|Val:unknown ❓ unknown, Unknown (solver timeout or incomplete), SARIF: Deductive level: error, BugFinding level: note
-/
#guard_msgs in
#eval testOutcome (mkOutcome (Imperative.SMT.Result.unknown (Ident := Core.Expression.Ident)) (Imperative.SMT.Result.unknown (Ident := Core.Expression.Ident))) .unknown

/-! ### bugFindingAssumingCompleteSpec mode: (sat, sat) is error -/

#guard outcomeToLevel .bugFindingAssumingCompleteSpec .assert (mkOutcome (.sat []) (.sat [])) = Strata.Sarif.Level.error
#guard outcomeToLevel .bugFinding .assert (mkOutcome (.sat []) (.sat [])) = Strata.Sarif.Level.note
#guard outcomeToLevel .bugFindingAssumingCompleteSpec .assert (mkOutcome (.sat []) .unsat) = Strata.Sarif.Level.none
#guard outcomeToLevel .bugFindingAssumingCompleteSpec .assert (mkOutcome .unknown (.sat [])) = Strata.Sarif.Level.error

/-! ### Outcome table verification -/

private def printOutcomeRow (sat val : Imperative.SMT.Result (Ident := Core.Expression.Ident)) : IO Unit := do
  let o : VCOutcome := { satisfiabilityProperty := sat, validityProperty := val }
  let eA := o.emoji .assert .full .deductive
  let lA := o.label .assert .full .deductive
  let eC := o.emoji .cover .full .deductive
  let lC := o.label .cover .full .deductive
  let ded := outcomeToLevel .deductive .assert o
  let bf := outcomeToLevel .bugFinding .assert o
  let bfc := outcomeToLevel .bugFindingAssumingCompleteSpec .assert o
  let coverStr := if eA == eC && lA == lC then "" else s!" | Cover: {eC} {lC}"
  IO.println s!"{eA} {lA} | Deductive: {ded} | BugFinding: {bf} | BugFinding+Complete: {bfc}{coverStr}"

/--
info: === Outcome Table (assert) ===
✅ always true and is reachable from declaration entry | Deductive: none | BugFinding: none | BugFinding+Complete: none | Cover: ✅ satisfiable and reachable from declaration entry
❌ always false and is reachable from declaration entry | Deductive: error | BugFinding: error | BugFinding+Complete: error
🔶 can be both true and false and is reachable from declaration entry | Deductive: error | BugFinding: note | BugFinding+Complete: error | Cover: ✅ satisfiable and reachable from declaration entry
✅ pass (❗path unreachable) | Deductive: warning | BugFinding: error | BugFinding+Complete: error | Cover: ❌ fail (❗path unreachable)
➕ can be true and is reachable from declaration entry | Deductive: error | BugFinding: note | BugFinding+Complete: note | Cover: ✅ satisfiable and reachable from declaration entry
✖️ always false if reached | Deductive: error | BugFinding: error | BugFinding+Complete: error
➖ can be false and is reachable from declaration entry | Deductive: error | BugFinding: note | BugFinding+Complete: error
✔️ always true if reached | Deductive: none | BugFinding: none | BugFinding+Complete: none
❓ unknown | Deductive: error | BugFinding: note | BugFinding+Complete: note
-/
#guard_msgs in
#eval do
  IO.println "=== Outcome Table (assert) ==="
  printOutcomeRow (.sat []) .unsat
  printOutcomeRow .unsat (.sat [])
  printOutcomeRow (.sat []) (.sat [])
  printOutcomeRow .unsat .unsat
  printOutcomeRow (.sat []) (Imperative.SMT.Result.unknown (Ident := Core.Expression.Ident))
  printOutcomeRow .unsat (Imperative.SMT.Result.unknown (Ident := Core.Expression.Ident))
  printOutcomeRow (Imperative.SMT.Result.unknown (Ident := Core.Expression.Ident)) (.sat [])
  printOutcomeRow (Imperative.SMT.Result.unknown (Ident := Core.Expression.Ident)) .unsat
  printOutcomeRow (Imperative.SMT.Result.unknown (Ident := Core.Expression.Ident)) (Imperative.SMT.Result.unknown (Ident := Core.Expression.Ident))

/-! ### AbstractedPhase and ModelValidation tests -/

private def preservingPhase : AbstractedPhase :=
  { name := "Preserving" }

private def rejectingPhase : AbstractedPhase :=
  { name := "Rejecting", getValidation := fun _ => .modelToValidate (fun _ => false) }

private def acceptingPhase : AbstractedPhase :=
  { name := "Accepting", getValidation := fun _ => .modelToValidate (fun _ => true) }

private def needsValidation (phases : List AbstractedPhase)
    (obligation : Imperative.ProofObligation Core.Expression) : Bool :=
  phases.any fun p => match p.getValidation obligation with
    | .modelToValidate _ => true
    | .modelPreserving => false

private def satResult : Result := .sat []
private def unsatResult : Result := .unsat
private def unknownResult : Result := .unknown (some [])

/-- A dummy obligation for testing phase validation. -/
private def dummyObligation : Imperative.ProofObligation Core.Expression :=
  { label := "test", property := .assert, assumptions := [], obligation := .true (), metadata := {} }

/-- info: false -/
#guard_msgs in #eval needsValidation [preservingPhase] dummyObligation

/-- info: true -/
#guard_msgs in #eval needsValidation [rejectingPhase] dummyObligation

/-- info: true -/
#guard_msgs in #eval needsValidation [preservingPhase, rejectingPhase] dummyObligation

-- adjustForPhases: sat stays sat with ModelPreserving
#guard (satResult.adjustForPhases [preservingPhase] dummyObligation).1 == satResult
#guard (satResult.adjustForPhases [preservingPhase] dummyObligation).2 == [{ phase := "Preserving", result := satResult }]

-- adjustForPhases: sat becomes unknown with rejecting validator
#guard (satResult.adjustForPhases [rejectingPhase] dummyObligation).1 == unknownResult
#guard (satResult.adjustForPhases [rejectingPhase] dummyObligation).2 == [{ phase := "Rejecting", result := unknownResult }]

-- adjustForPhases: sat stays sat with accepting validator
#guard (satResult.adjustForPhases [acceptingPhase] dummyObligation).1 == satResult
#guard (satResult.adjustForPhases [acceptingPhase] dummyObligation).2 == [{ phase := "Accepting", result := satResult }]

-- adjustForPhases: sat becomes unknown when any phase rejects
#guard (satResult.adjustForPhases [preservingPhase, rejectingPhase] dummyObligation).1 == unknownResult
#guard (satResult.adjustForPhases [preservingPhase, rejectingPhase] dummyObligation).2 ==
  [{ phase := "Rejecting", result := unknownResult }, { phase := "Preserving", result := unknownResult }]

-- adjustForPhases: unsat is unchanged regardless of phases
#guard (unsatResult.adjustForPhases [rejectingPhase] dummyObligation).1 == unsatResult
#guard (unsatResult.adjustForPhases [rejectingPhase] dummyObligation).2 == []

-- adjustForPhases: unknown stays unknown with rejecting validator, but produces log
#guard (unknownResult.adjustForPhases [rejectingPhase] dummyObligation).1 == unknownResult
#guard (unknownResult.adjustForPhases [rejectingPhase] dummyObligation).2 == [{ phase := "Rejecting", result := unknownResult }]

-- adjustForPhases: unknown promoted to sat with accepting validator
#guard (unknownResult.adjustForPhases [acceptingPhase] dummyObligation).1 == satResult
#guard (unknownResult.adjustForPhases [acceptingPhase] dummyObligation).2 == [{ phase := "Accepting", result := satResult }]

-- adjustForPhases: unknown stays unknown with preserving phase (no validator)
#guard (unknownResult.adjustForPhases [preservingPhase] dummyObligation).1 == unknownResult
#guard (unknownResult.adjustForPhases [preservingPhase] dummyObligation).2 == [{ phase := "Preserving", result := unknownResult }]

-- adjustForPhases: empty phases list preserves sat
#guard (satResult.adjustForPhases [] dummyObligation).1 == satResult
#guard (satResult.adjustForPhases [] dummyObligation).2 == []

/-! ### Combined and front-end phase validation tests -/

/-- Obligation with call-elimination labels in path conditions. -/
private def callElimObligation : Imperative.ProofObligation Core.Expression :=
  { label := "test_callElim", property := .assert,
    assumptions := [[.assumption "callElimAssume_post" (.true ())]],
    obligation := .true (), metadata := {} }

/-- Obligation with no abstraction labels — models are sound. -/
private def cleanObligation : Imperative.ProofObligation Core.Expression :=
  { label := "test_clean", property := .assert,
    assumptions := [[.assumption "precond_x_positive" (.true ())]],
    obligation := .true (), metadata := {} }

-- Combined Core phases: clean obligation preserves sat
#guard (satResult.adjustForPhases [callElimPipelinePhase.phase, loopElimPipelinePhase.phase] cleanObligation).1 == satResult

-- Combined Core phases: call-elim obligation becomes unknown
#guard (satResult.adjustForPhases [callElimPipelinePhase.phase, loopElimPipelinePhase.phase] callElimObligation).1 == unknownResult

-- frontEndPhase: always rejects sat regardless of obligation
#guard (satResult.adjustForPhases [Strata.frontEndPhase] cleanObligation).1 == unknownResult
#guard (satResult.adjustForPhases [Strata.frontEndPhase] callElimObligation).1 == unknownResult

-- frontEndPhase: unsat is unchanged
#guard (unsatResult.adjustForPhases [Strata.frontEndPhase] cleanObligation).1 == unsatResult

end Core
