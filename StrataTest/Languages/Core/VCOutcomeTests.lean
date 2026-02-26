/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Core.Verifier

/-! ## Tests for VCOutcome - All 9 Combinations

Tests all nine possible outcome combinations from the two-sided verification check.
-/

namespace Core
open Strata.SMT

-- Test helper to create VCOutcome from two SMT results
def mkOutcome (satisfiabilityProperty : Result) (validityProperty : Result) : VCOutcome :=
  { satisfiabilityProperty, validityProperty }

-- Helper to format outcome as "emoji label"
def formatOutcome (o : VCOutcome) : String :=
  s!"{VCOutcome.emoji o} {VCOutcome.label o}"

-- Test 1: (sat, unsat) → pass (always true & reachable)
/-- info: "✅ pass" -/
#guard_msgs in
#eval formatOutcome (mkOutcome (satisfiabilityProperty := .sat) (validityProperty := .unsat))

-- Test 2: (unsat, sat) → refuted (always false & reachable)
/-- info: "❌ refuted" -/
#guard_msgs in
#eval formatOutcome (mkOutcome (satisfiabilityProperty := .unsat) (validityProperty := .sat))

-- Test 3: (sat, sat) → indecisive (depends on inputs & reachable)
/-- info: "🔶 indecisive" -/
#guard_msgs in
#eval formatOutcome (mkOutcome (satisfiabilityProperty := .sat) (validityProperty := .sat))

-- Test 4: (unsat, unsat) → unreachable (path condition contradictory)
/-- info: "⛔ unreachable" -/
#guard_msgs in
#eval formatOutcome (mkOutcome (satisfiabilityProperty := .unsat) (validityProperty := .unsat))

-- Test 5: (sat, unknown) → satisfiable (can be true, unknown if always)
/-- info: "➕ satisfiable" -/
#guard_msgs in
#eval formatOutcome (mkOutcome (satisfiabilityProperty := .sat) (validityProperty := .unknown))

-- Test 6: (unsat, unknown) → refuted if reachable (always false if reached)
/-- info: "✖️ refuted if reachable" -/
#guard_msgs in
#eval formatOutcome (mkOutcome (satisfiabilityProperty := .unsat) (validityProperty := .unknown))

-- Test 7: (unknown, sat) → reachable and can be false
/-- info: "➖ reachable and can be false" -/
#guard_msgs in
#eval formatOutcome (mkOutcome (satisfiabilityProperty := .unknown) (validityProperty := .sat))

-- Test 8: (unknown, unsat) → pass if reachable
/-- info: "✔️ pass if reachable" -/
#guard_msgs in
#eval formatOutcome (mkOutcome (satisfiabilityProperty := .unknown) (validityProperty := .unsat))

-- Test 9: (unknown, unknown) → unknown
/-- info: "❓ unknown" -/
#guard_msgs in
#eval formatOutcome (mkOutcome (satisfiabilityProperty := .unknown) (validityProperty := .unknown))

end Core
