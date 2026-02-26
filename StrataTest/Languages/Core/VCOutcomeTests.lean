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

def testOutcome (o : VCOutcome) (predicate : VCOutcome → Bool) : IO Unit := do
  IO.println s!"Emoji: {o.emoji}, Label: {o.label}, Predicate: {predicate o}, Message: {outcomeToMessage o}, SARIF output: Deductive: {outcomeToLevel .deductive o}, BugFinding: {outcomeToLevel .bugFinding o}"

/-! ### Outcome: (sat, unsat) - always true and reachable -/

/--
info: Emoji: ✅, Label: pass, Predicate: true, Message: Always true and reachable, SARIF output: Deductive: none, BugFinding: none
-/
#guard_msgs in
#eval testOutcome (mkOutcome (.sat default) .unsat) (·.passAndReachable)

/-! ### Outcome: (unsat, sat) - always false and reachable -/

/--
info: Emoji: ❌, Label: refuted, Predicate: true, Message: Always false and reachable, SARIF output: Deductive: error, BugFinding: error
-/
#guard_msgs in
#eval testOutcome (mkOutcome .unsat (.sat default)) (·.alwaysFalseAndReachable)

/-! ### Outcome: (sat, sat) - true or false depending on inputs -/

/--
info: Emoji: 🔶, Label: indecisive, Predicate: true, Message: True or false depending on inputs, SARIF output: Deductive: error, BugFinding: note
-/
#guard_msgs in
#eval testOutcome (mkOutcome (.sat default) (.sat default)) (·.indecisiveAndReachable)

/-! ### Outcome: (unsat, unsat) - unreachable -/

/--
info: Emoji: ⛔, Label: unreachable, Predicate: true, Message: Unreachable: path condition is contradictory, SARIF output: Deductive: warning, BugFinding: warning
-/
#guard_msgs in
#eval testOutcome (mkOutcome .unsat .unsat) (·.unreachable)

/-! ### Outcome: (sat, unknown) - can be true, unknown if always true -/

/--
info: Emoji: ➕, Label: satisfiable, Predicate: true, Message: Can be true, unknown if always true, SARIF output: Deductive: error, BugFinding: note
-/
#guard_msgs in
#eval testOutcome (mkOutcome (.sat default) (Imperative.SMT.Result.unknown (Ident := Core.Expression.Ident))) (·.satisfiableValidityUnknown)

/-! ### Outcome: (unsat, unknown) - always false if reachable -/

/--
info: Emoji: ✖️, Label: refuted if reachable, Predicate: true, Message: Always false if reachable, reachability unknown, SARIF output: Deductive: error, BugFinding: error
-/
#guard_msgs in
#eval testOutcome (mkOutcome .unsat (Imperative.SMT.Result.unknown (Ident := Core.Expression.Ident))) (·.alwaysFalseReachabilityUnknown)

/-! ### Outcome: (unknown, sat) - can be false and reachable -/

/--
info: Emoji: ➖, Label: reachable and can be false, Predicate: true, Message: Can be false and reachable, unknown if always false, SARIF output: Deductive: error, BugFinding: note
-/
#guard_msgs in
#eval testOutcome (mkOutcome (Imperative.SMT.Result.unknown (Ident := Core.Expression.Ident)) (.sat default)) (·.canBeFalseAndReachable)

/-! ### Outcome: (unknown, unsat) - always true if reachable -/

/--
info: Emoji: ✔️, Label: pass if reachable, Predicate: true, Message: Always true if reachable, reachability unknown, SARIF output: Deductive: none, BugFinding: none
-/
#guard_msgs in
#eval testOutcome (mkOutcome (Imperative.SMT.Result.unknown (Ident := Core.Expression.Ident)) .unsat) (·.passReachabilityUnknown)

/-! ### Outcome: (unknown, unknown) - solver timeout or incomplete -/

/--
info: Emoji: ❓, Label: unknown, Predicate: true, Message: Unknown (solver timeout or incomplete), SARIF output: Deductive: error, BugFinding: note
-/
#guard_msgs in
#eval testOutcome (mkOutcome (Imperative.SMT.Result.unknown (Ident := Core.Expression.Ident)) (Imperative.SMT.Result.unknown (Ident := Core.Expression.Ident))) (·.unknown)

end Core
