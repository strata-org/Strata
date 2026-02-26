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
  | indecisiveAndReachable
  | unreachable
  | satisfiableValidityUnknown
  | alwaysFalseReachabilityUnknown
  | canBeFalseAndReachable
  | passReachabilityUnknown
  | unknown
  deriving DecidableEq, Repr

def OutcomePredicate.eval (p : OutcomePredicate) (o : VCOutcome) : Bool :=
  match p with
  | .passAndReachable => o.passAndReachable
  | .alwaysFalseAndReachable => o.alwaysFalseAndReachable
  | .indecisiveAndReachable => o.indecisiveAndReachable
  | .unreachable => o.unreachable
  | .satisfiableValidityUnknown => o.satisfiableValidityUnknown
  | .alwaysFalseReachabilityUnknown => o.alwaysFalseReachabilityUnknown
  | .canBeFalseAndReachable => o.canBeFalseAndReachable
  | .passReachabilityUnknown => o.passReachabilityUnknown
  | .unknown => o.unknown

def allPredicates : List OutcomePredicate :=
  [.passAndReachable, .alwaysFalseAndReachable, .indecisiveAndReachable, .unreachable,
   .satisfiableValidityUnknown, .alwaysFalseReachabilityUnknown, .canBeFalseAndReachable,
   .passReachabilityUnknown, .unknown]

def testOutcome (o : VCOutcome) (expectedTrue : OutcomePredicate) : IO Unit := do
  for p in allPredicates do
    if p == expectedTrue then
      if !p.eval o then IO.eprintln s!"ERROR: Expected {repr p} to be true but was false"
    else
      if p.eval o then IO.eprintln s!"ERROR: Expected {repr p} to be false but was true"
  let satStr := if let .sat _ := o.satisfiabilityProperty then "sat" else if let .unsat := o.satisfiabilityProperty then "unsat" else "unknown"
  let valStr := if let .sat _ := o.validityProperty then "sat" else if let .unsat := o.validityProperty then "unsat" else "unknown"
  IO.println s!"Sat:{satStr}|Val:{valStr} {o.emoji} {o.label}, {outcomeToMessage o}, SARIF: Deductive level: {outcomeToLevel .deductive o}, BugFinding level: {outcomeToLevel .bugFinding o}"

/-! ### Outcome: (sat, unsat) - always true and reachable -/

/--
info: Sat:sat|Val:unsat ✅ pass, Always true and reachable, SARIF: Deductive level: none, BugFinding level: none
-/
#guard_msgs in
#eval testOutcome (mkOutcome (.sat default) .unsat) .passAndReachable

/-! ### Outcome: (unsat, sat) - always false and reachable -/

/--
info: Sat:unsat|Val:sat ❌ refuted, Always false and reachable, SARIF: Deductive level: error, BugFinding level: error
-/
#guard_msgs in
#eval testOutcome (mkOutcome .unsat (.sat default)) .alwaysFalseAndReachable

/-! ### Outcome: (sat, sat) - true or false depending on inputs -/

/--
info: Sat:sat|Val:sat 🔶 indecisive, True or false depending on inputs, SARIF: Deductive level: error, BugFinding level: note
-/
#guard_msgs in
#eval testOutcome (mkOutcome (.sat default) (.sat default)) .indecisiveAndReachable

/-! ### Outcome: (unsat, unsat) - unreachable -/

/--
info: Sat:unsat|Val:unsat ⛔ unreachable, Unreachable: path condition is contradictory, SARIF: Deductive level: warning, BugFinding level: warning
-/
#guard_msgs in
#eval testOutcome (mkOutcome .unsat .unsat) .unreachable

/-! ### Outcome: (sat, unknown) - can be true, unknown if always true -/

/--
info: Sat:sat|Val:unknown ➕ satisfiable, Can be true, unknown if always true, SARIF: Deductive level: error, BugFinding level: note
-/
#guard_msgs in
#eval testOutcome (mkOutcome (.sat default) (Imperative.SMT.Result.unknown (Ident := Core.Expression.Ident))) .satisfiableValidityUnknown

/-! ### Outcome: (unsat, unknown) - always false if reachable -/

/--
info: Sat:unsat|Val:unknown ✖️ refuted if reachable, Always false if reachable, reachability unknown, SARIF: Deductive level: error, BugFinding level: error
-/
#guard_msgs in
#eval testOutcome (mkOutcome .unsat (Imperative.SMT.Result.unknown (Ident := Core.Expression.Ident))) .alwaysFalseReachabilityUnknown

/-! ### Outcome: (unknown, sat) - can be false and reachable -/

/--
info: Sat:unknown|Val:sat ➖ reachable and can be false, Can be false and reachable, unknown if always false, SARIF: Deductive level: error, BugFinding level: note
-/
#guard_msgs in
#eval testOutcome (mkOutcome (Imperative.SMT.Result.unknown (Ident := Core.Expression.Ident)) (.sat default)) .canBeFalseAndReachable

/-! ### Outcome: (unknown, unsat) - always true if reachable -/

/--
info: Sat:unknown|Val:unsat ✔️ pass if reachable, Always true if reachable, reachability unknown, SARIF: Deductive level: none, BugFinding level: none
-/
#guard_msgs in
#eval testOutcome (mkOutcome (Imperative.SMT.Result.unknown (Ident := Core.Expression.Ident)) .unsat) .passReachabilityUnknown

/-! ### Outcome: (unknown, unknown) - solver timeout or incomplete -/

/--
info: Sat:unknown|Val:unknown ❓ unknown, Unknown (solver timeout or incomplete), SARIF: Deductive level: error, BugFinding level: note
-/
#guard_msgs in
#eval testOutcome (mkOutcome (Imperative.SMT.Result.unknown (Ident := Core.Expression.Ident)) (Imperative.SMT.Result.unknown (Ident := Core.Expression.Ident))) .unknown

end Core
