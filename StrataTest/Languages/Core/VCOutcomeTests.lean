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
  IO.println s!"\nSat:{satStr}|Val:{valStr} {o.emoji} {o.label}, {outcomeToMessage o}, SARIF: Deductive level: {outcomeToLevel .deductive .assert o}, BugFinding level: {outcomeToLevel .bugFinding .assert o}"

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
Sat:unsat|Val:unsat ✅ pass (path not reachable), Unreachable: path condition is contradictory, SARIF: Deductive level: warning, BugFinding level: warning
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
Sat:unknown|Val:sat ➖ can be false and is reachable from declaration entry, Can be false and reachable, unknown if always false, SARIF: Deductive level: error, BugFinding level: note
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

end Core
