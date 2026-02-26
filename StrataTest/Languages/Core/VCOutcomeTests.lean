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

/-! ### Outcome: (sat, unsat) - always true and reachable -/

/--
info: Emoji: ✅, Label: pass, Predicate: true, Message: Always true and reachable, Deductive: none, BugFinding: none
-/
#guard_msgs in
#eval do
  let o := mkOutcome (.sat default) .unsat
  IO.println s!"Emoji: {o.emoji}, Label: {o.label}, Predicate: {o.passAndReachable}, Message: {outcomeToMessage o}, Deductive: {outcomeToLevel .deductive o}, BugFinding: {outcomeToLevel .bugFinding o}"

/-! ### Outcome: (unsat, sat) - always false and reachable -/

/--
info: Emoji: ❌, Label: refuted, Predicate: true, Message: Always false and reachable, Deductive: error, BugFinding: error
-/
#guard_msgs in
#eval do
  let o := mkOutcome .unsat (.sat default)
  IO.println s!"Emoji: {o.emoji}, Label: {o.label}, Predicate: {o.alwaysFalseAndReachable}, Message: {outcomeToMessage o}, Deductive: {outcomeToLevel .deductive o}, BugFinding: {outcomeToLevel .bugFinding o}"

/-! ### Outcome: (sat, sat) - true or false depending on inputs -/

/--
info: Emoji: 🔶, Label: indecisive, Predicate: true, Message: True or false depending on inputs, Deductive: error, BugFinding: note
-/
#guard_msgs in
#eval do
  let o := mkOutcome (.sat default) (.sat default)
  IO.println s!"Emoji: {o.emoji}, Label: {o.label}, Predicate: {o.indecisiveAndReachable}, Message: {outcomeToMessage o}, Deductive: {outcomeToLevel .deductive o}, BugFinding: {outcomeToLevel .bugFinding o}"

/-! ### Outcome: (unsat, unsat) - unreachable -/

/--
info: Emoji: ⛔, Label: unreachable, Predicate: true, Message: Unreachable: path condition is contradictory, Deductive: warning, BugFinding: warning
-/
#guard_msgs in
#eval do
  let o := mkOutcome .unsat .unsat
  IO.println s!"Emoji: {o.emoji}, Label: {o.label}, Predicate: {o.unreachable}, Message: {outcomeToMessage o}, Deductive: {outcomeToLevel .deductive o}, BugFinding: {outcomeToLevel .bugFinding o}"

/-! ### Outcome: (sat, unknown) - can be true, unknown if always true -/

/--
info: Emoji: ➕, Label: satisfiable, Predicate: true, Message: Can be true, unknown if always true, Deductive: error, BugFinding: note
-/
#guard_msgs in
#eval do
  let o := mkOutcome (.sat default) (Imperative.SMT.Result.unknown (Ident := Core.Expression.Ident))
  IO.println s!"Emoji: {o.emoji}, Label: {o.label}, Predicate: {o.satisfiableValidityUnknown}, Message: {outcomeToMessage o}, Deductive: {outcomeToLevel .deductive o}, BugFinding: {outcomeToLevel .bugFinding o}"

/-! ### Outcome: (unsat, unknown) - always false if reachable -/

/--
info: Emoji: ✖️, Label: refuted if reachable, Predicate: true, Message: Always false if reachable, reachability unknown, Deductive: error, BugFinding: error
-/
#guard_msgs in
#eval do
  let o := mkOutcome .unsat (Imperative.SMT.Result.unknown (Ident := Core.Expression.Ident))
  IO.println s!"Emoji: {o.emoji}, Label: {o.label}, Predicate: {o.alwaysFalseReachabilityUnknown}, Message: {outcomeToMessage o}, Deductive: {outcomeToLevel .deductive o}, BugFinding: {outcomeToLevel .bugFinding o}"

/-! ### Outcome: (unknown, sat) - can be false and reachable -/

/--
info: Emoji: ➖, Label: reachable and can be false, Predicate: true, Message: Can be false and reachable, unknown if always false, Deductive: error, BugFinding: note
-/
#guard_msgs in
#eval do
  let o := mkOutcome (Imperative.SMT.Result.unknown (Ident := Core.Expression.Ident)) (.sat default)
  IO.println s!"Emoji: {o.emoji}, Label: {o.label}, Predicate: {o.canBeFalseAndReachable}, Message: {outcomeToMessage o}, Deductive: {outcomeToLevel .deductive o}, BugFinding: {outcomeToLevel .bugFinding o}"

/-! ### Outcome: (unknown, unsat) - always true if reachable -/

/--
info: Emoji: ✔️, Label: pass if reachable, Predicate: true, Message: Always true if reachable, reachability unknown, Deductive: none, BugFinding: none
-/
#guard_msgs in
#eval do
  let o := mkOutcome (Imperative.SMT.Result.unknown (Ident := Core.Expression.Ident)) .unsat
  IO.println s!"Emoji: {o.emoji}, Label: {o.label}, Predicate: {o.passReachabilityUnknown}, Message: {outcomeToMessage o}, Deductive: {outcomeToLevel .deductive o}, BugFinding: {outcomeToLevel .bugFinding o}"

/-! ### Outcome: (unknown, unknown) - solver timeout or incomplete -/

/--
info: Emoji: ❓, Label: unknown, Predicate: true, Message: Unknown (solver timeout or incomplete), Deductive: error, BugFinding: note
-/
#guard_msgs in
#eval do
  let o := mkOutcome (Imperative.SMT.Result.unknown (Ident := Core.Expression.Ident)) (Imperative.SMT.Result.unknown (Ident := Core.Expression.Ident))
  IO.println s!"Emoji: {o.emoji}, Label: {o.label}, Predicate: {o.unknown}, Message: {outcomeToMessage o}, Deductive: {outcomeToLevel .deductive o}, BugFinding: {outcomeToLevel .bugFinding o}"

end Core
