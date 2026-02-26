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

def formatOutcome (o : VCOutcome) : String :=
  s!"{VCOutcome.emoji o} {VCOutcome.label o}"

/-! ### Outcome: (sat, unsat) - always true and reachable -/

/-- info: "✅ pass" -/
#guard_msgs in
#eval formatOutcome (mkOutcome (.sat default) .unsat)

/-- info: true -/
#guard_msgs in
#eval (mkOutcome (.sat default) .unsat).passAndReachable

/-- info: "Always true and reachable" -/
#guard_msgs in
#eval outcomeToMessage (mkOutcome (.sat default) .unsat)

/-- info: Strata.Sarif.Level.none -/
#guard_msgs in
#eval outcomeToLevel .deductive (mkOutcome (.sat default) .unsat)

/-- info: Strata.Sarif.Level.none -/
#guard_msgs in
#eval outcomeToLevel .bugFinding (mkOutcome (.sat default) .unsat)

/-! ### Outcome: (unsat, sat) - always false and reachable -/

/-- info: "❌ refuted" -/
#guard_msgs in
#eval formatOutcome (mkOutcome .unsat (.sat default))

/-- info: true -/
#guard_msgs in
#eval (mkOutcome .unsat (.sat default)).alwaysFalseAndReachable

/-- info: "Always false and reachable" -/
#guard_msgs in
#eval outcomeToMessage (mkOutcome .unsat (.sat default))

/-- info: Strata.Sarif.Level.error -/
#guard_msgs in
#eval outcomeToLevel .deductive (mkOutcome .unsat (.sat default))

/-- info: Strata.Sarif.Level.error -/
#guard_msgs in
#eval outcomeToLevel .bugFinding (mkOutcome .unsat (.sat default))

/-! ### Outcome: (sat, sat) - true or false depending on inputs -/

/-- info: "🔶 indecisive" -/
#guard_msgs in
#eval formatOutcome (mkOutcome (.sat default) (.sat default))

/-- info: true -/
#guard_msgs in
#eval (mkOutcome (.sat default) (.sat default)).indecisiveAndReachable

/-- info: "True or false depending on inputs" -/
#guard_msgs in
#eval outcomeToMessage (mkOutcome (.sat default) (.sat default))

/-- info: Strata.Sarif.Level.error -/
#guard_msgs in
#eval outcomeToLevel .deductive (mkOutcome (.sat default) (.sat default))

/-- info: Strata.Sarif.Level.warning -/
#guard_msgs in
#eval outcomeToLevel .bugFinding (mkOutcome (.sat default) (.sat default))

/-! ### Outcome: (unsat, unsat) - unreachable -/

/-- info: "⛔ unreachable" -/
#guard_msgs in
#eval formatOutcome (mkOutcome .unsat .unsat)

/-- info: true -/
#guard_msgs in
#eval (mkOutcome .unsat .unsat).unreachable

/-- info: "Unreachable: path condition is contradictory" -/
#guard_msgs in
#eval outcomeToMessage (mkOutcome .unsat .unsat)

/-- info: Strata.Sarif.Level.warning -/
#guard_msgs in
#eval outcomeToLevel .deductive (mkOutcome .unsat .unsat)

/-- info: Strata.Sarif.Level.note -/
#guard_msgs in
#eval outcomeToLevel .bugFinding (mkOutcome .unsat .unsat)

/-! ### Outcome: (sat, unknown) - can be true, unknown if always true -/

/-- info: "➕ satisfiable" -/
#guard_msgs in
#eval formatOutcome (mkOutcome (.sat default) (Imperative.SMT.Result.unknown (Ident := Core.Expression.Ident)))

/-- info: true -/
#guard_msgs in
#eval (mkOutcome (.sat default) (Imperative.SMT.Result.unknown (Ident := Core.Expression.Ident))).satisfiableValidityUnknown

/-- info: "Can be true, unknown if always true" -/
#guard_msgs in
#eval outcomeToMessage (mkOutcome (.sat default) (Imperative.SMT.Result.unknown (Ident := Core.Expression.Ident)))

/-- info: Strata.Sarif.Level.error -/
#guard_msgs in
#eval outcomeToLevel .deductive (mkOutcome (.sat default) (Imperative.SMT.Result.unknown (Ident := Core.Expression.Ident)))

/-- info: Strata.Sarif.Level.note -/
#guard_msgs in
#eval outcomeToLevel .bugFinding (mkOutcome (.sat default) (Imperative.SMT.Result.unknown (Ident := Core.Expression.Ident)))

/-! ### Outcome: (unsat, unknown) - always false if reachable -/

/-- info: "✖️ refuted if reachable" -/
#guard_msgs in
#eval formatOutcome (mkOutcome .unsat (Imperative.SMT.Result.unknown (Ident := Core.Expression.Ident)))

/-- info: true -/
#guard_msgs in
#eval (mkOutcome .unsat (Imperative.SMT.Result.unknown (Ident := Core.Expression.Ident))).alwaysFalseReachabilityUnknown

/-- info: "Always false if reachable, reachability unknown" -/
#guard_msgs in
#eval outcomeToMessage (mkOutcome .unsat (Imperative.SMT.Result.unknown (Ident := Core.Expression.Ident)))

/-- info: Strata.Sarif.Level.error -/
#guard_msgs in
#eval outcomeToLevel .deductive (mkOutcome .unsat (Imperative.SMT.Result.unknown (Ident := Core.Expression.Ident)))

/-- info: Strata.Sarif.Level.error -/
#guard_msgs in
#eval outcomeToLevel .bugFinding (mkOutcome .unsat (Imperative.SMT.Result.unknown (Ident := Core.Expression.Ident)))

/-! ### Outcome: (unknown, sat) - can be false and reachable -/

/-- info: "➖ reachable and can be false" -/
#guard_msgs in
#eval formatOutcome (mkOutcome (Imperative.SMT.Result.unknown (Ident := Core.Expression.Ident)) (.sat default))

/-- info: true -/
#guard_msgs in
#eval (mkOutcome (Imperative.SMT.Result.unknown (Ident := Core.Expression.Ident)) (.sat default)).canBeFalseAndReachable

/-- info: "Can be false and reachable, unknown if always false" -/
#guard_msgs in
#eval outcomeToMessage (mkOutcome (Imperative.SMT.Result.unknown (Ident := Core.Expression.Ident)) (.sat default))

/-- info: Strata.Sarif.Level.error -/
#guard_msgs in
#eval outcomeToLevel .deductive (mkOutcome (Imperative.SMT.Result.unknown (Ident := Core.Expression.Ident)) (.sat default))

/-- info: Strata.Sarif.Level.warning -/
#guard_msgs in
#eval outcomeToLevel .bugFinding (mkOutcome (Imperative.SMT.Result.unknown (Ident := Core.Expression.Ident)) (.sat default))

/-! ### Outcome: (unknown, unsat) - always true if reachable -/

/-- info: "✔️ pass if reachable" -/
#guard_msgs in
#eval formatOutcome (mkOutcome (Imperative.SMT.Result.unknown (Ident := Core.Expression.Ident)) .unsat)

/-- info: true -/
#guard_msgs in
#eval (mkOutcome (Imperative.SMT.Result.unknown (Ident := Core.Expression.Ident)) .unsat).passReachabilityUnknown

/-- info: "Always true if reachable, reachability unknown" -/
#guard_msgs in
#eval outcomeToMessage (mkOutcome (Imperative.SMT.Result.unknown (Ident := Core.Expression.Ident)) .unsat)

/-- info: Strata.Sarif.Level.none -/
#guard_msgs in
#eval outcomeToLevel .deductive (mkOutcome (Imperative.SMT.Result.unknown (Ident := Core.Expression.Ident)) .unsat)

/-- info: Strata.Sarif.Level.none -/
#guard_msgs in
#eval outcomeToLevel .bugFinding (mkOutcome (Imperative.SMT.Result.unknown (Ident := Core.Expression.Ident)) .unsat)

/-! ### Outcome: (unknown, unknown) - solver timeout or incomplete -/

/-- info: "❓ unknown" -/
#guard_msgs in
#eval formatOutcome (mkOutcome (Imperative.SMT.Result.unknown (Ident := Core.Expression.Ident)) (Imperative.SMT.Result.unknown (Ident := Core.Expression.Ident)))

/-- info: true -/
#guard_msgs in
#eval (mkOutcome (Imperative.SMT.Result.unknown (Ident := Core.Expression.Ident)) (Imperative.SMT.Result.unknown (Ident := Core.Expression.Ident))).unknown

/-- info: "Unknown (solver timeout or incomplete)" -/
#guard_msgs in
#eval outcomeToMessage (mkOutcome (Imperative.SMT.Result.unknown (Ident := Core.Expression.Ident)) (Imperative.SMT.Result.unknown (Ident := Core.Expression.Ident)))

/-- info: Strata.Sarif.Level.error -/
#guard_msgs in
#eval outcomeToLevel .deductive (mkOutcome (Imperative.SMT.Result.unknown (Ident := Core.Expression.Ident)) (Imperative.SMT.Result.unknown (Ident := Core.Expression.Ident)))

/-- info: Strata.Sarif.Level.warning -/
#guard_msgs in
#eval outcomeToLevel .bugFinding (mkOutcome (Imperative.SMT.Result.unknown (Ident := Core.Expression.Ident)) (Imperative.SMT.Result.unknown (Ident := Core.Expression.Ident)))

end Core
