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

-- Test 1: (sat, unsat) → pass (always true & reachable)
/-- info: true -/
#guard_msgs in
#eval (mkOutcome (satisfiabilityProperty := .sat) (validityProperty := .unsat)).isPass

/-- info: "✅ pass" -/
#guard_msgs in
#eval s!"{VCOutcome.emoji (mkOutcome (satisfiabilityProperty := .sat) (validityProperty := .unsat))} {VCOutcome.label (mkOutcome (satisfiabilityProperty := .sat) (validityProperty := .unsat))}"

-- Test 2: (unsat, sat) → refuted (always false & reachable)
/-- info: true -/
#guard_msgs in
#eval (mkOutcome (satisfiabilityProperty := .unsat) (validityProperty := .sat)).isRefuted

/-- info: "❌ refuted" -/
#guard_msgs in
#eval s!"{VCOutcome.emoji (mkOutcome (satisfiabilityProperty := .unsat) (validityProperty := .sat))} {VCOutcome.label (mkOutcome (satisfiabilityProperty := .unsat) (validityProperty := .sat))}"

-- Test 3: (sat, sat) → indecisive (depends on inputs & reachable)
/-- info: true -/
#guard_msgs in
#eval (mkOutcome (satisfiabilityProperty := .sat) (validityProperty := .sat)).isIndecisive

/-- info: "🔶 indecisive" -/
#guard_msgs in
#eval s!"{VCOutcome.emoji (mkOutcome (satisfiabilityProperty := .sat) (validityProperty := .sat))} {VCOutcome.label (mkOutcome (satisfiabilityProperty := .sat) (validityProperty := .sat))}"

-- Test 4: (unsat, unsat) → unreachable (path condition contradictory)
/-- info: true -/
#guard_msgs in
#eval (mkOutcome (satisfiabilityProperty := .unsat) (validityProperty := .unsat)).isUnreachable

/-- info: "⛔ unreachable" -/
#guard_msgs in
#eval s!"{VCOutcome.emoji (mkOutcome (satisfiabilityProperty := .unsat) (validityProperty := .unsat))} {VCOutcome.label (mkOutcome (satisfiabilityProperty := .unsat) (validityProperty := .unsat))}"

-- Test 5: (sat, unknown) → satisfiable (can be true, unknown if always)
/-- info: true -/
#guard_msgs in
#eval (mkOutcome (satisfiabilityProperty := .sat) (validityProperty := .unknown)).isSatisfiable

/-- info: "➕ satisfiable" -/
#guard_msgs in
#eval s!"{VCOutcome.emoji (mkOutcome (satisfiabilityProperty := .sat) (validityProperty := .unknown))} {VCOutcome.label (mkOutcome (satisfiabilityProperty := .sat) (validityProperty := .unknown))}"

-- Test 6: (unsat, unknown) → refuted if reachable (always false if reached)
/-- info: true -/
#guard_msgs in
#eval (mkOutcome (satisfiabilityProperty := .unsat) (validityProperty := .unknown)).isRefutedIfReachable

/-- info: "✖️ refuted if reachable" -/
#guard_msgs in
#eval s!"{VCOutcome.emoji (mkOutcome (satisfiabilityProperty := .unsat) (validityProperty := .unknown))} {VCOutcome.label (mkOutcome (satisfiabilityProperty := .unsat) (validityProperty := .unknown))}"

-- Test 7: (unknown, sat) → reachable and can be false
/-- info: true -/
#guard_msgs in
#eval (mkOutcome (satisfiabilityProperty := .unknown) (validityProperty := .sat)).isReachableAndCanBeFalse

/-- info: "➖ reachable and can be false" -/
#guard_msgs in
#eval s!"{VCOutcome.emoji (mkOutcome (satisfiabilityProperty := .unknown) (validityProperty := .sat))} {VCOutcome.label (mkOutcome (satisfiabilityProperty := .unknown) (validityProperty := .sat))}"

-- Test 8: (unknown, unsat) → always true if reachable
/-- info: true -/
#guard_msgs in
#eval (mkOutcome (satisfiabilityProperty := .unknown) (validityProperty := .unsat)).isAlwaysTrueIfReachable

/-- info: "✔️ always true if reachable" -/
#guard_msgs in
#eval s!"{VCOutcome.emoji (mkOutcome (satisfiabilityProperty := .unknown) (validityProperty := .unsat))} {VCOutcome.label (mkOutcome (satisfiabilityProperty := .unknown) (validityProperty := .unsat))}"

-- Test 9: (unknown, unknown) → unknown
/-- info: true -/
#guard_msgs in
#eval (mkOutcome (satisfiabilityProperty := .unknown) (validityProperty := .unknown)).isUnknown

/-- info: "❓ unknown" -/
#guard_msgs in
#eval s!"{VCOutcome.emoji (mkOutcome (satisfiabilityProperty := .unknown) (validityProperty := .unknown))} {VCOutcome.label (mkOutcome (satisfiabilityProperty := .unknown) (validityProperty := .unknown))}"

end Core
