/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Core.Verifier

/-!
# PE Reachability Test

When the partial evaluator resolves a VC by literal evaluation (e.g.,
`assert true` or `assert false` with no path conditions), the outcome
should report definitive reachability — not "if reached".

PE results are determined by constant folding with concrete values, so
phase validation (which checks solver models against pre-transformation
semantics) is skipped: there are no models to validate.

When path conditions (assumptions) are non-empty, the PE cannot
determine reachability and correctly reports "if reached".
-/

namespace Strata

private def options : Core.VerifyOptions :=
  { Core.VerifyOptions.quiet with checkLevel := .full }

----------------------------------------------------------------------

private def assertTruePgm :=
#strata
program Core;
procedure main() returns () {
  assert [trivially_true]: true;
};
#end

-- Trivially reachable: no path conditions → "is reachable"
/-- info: "trivially_true: ✅ always true and is reachable from declaration entry" -/
#guard_msgs in
#eval do
  let results ← verify assertTruePgm (options := options)
    (externalPhases := [Strata.frontEndPhase])
  let mut output := ""
  for vcr in results do
    output := output ++ s!"{vcr.obligation.label}: {vcr.formatOutcome}"
  return output

----------------------------------------------------------------------

private def assertFalsePgm :=
#strata
program Core;
procedure main() returns () {
  assert [trivially_false]: false;
};
#end

/-- info: "trivially_false: ❌ always false and is reachable from declaration entry" -/
#guard_msgs in
#eval do
  let results ← verify assertFalsePgm (options := options)
    (externalPhases := [Strata.frontEndPhase])
  let mut output := ""
  for vcr in results do
    output := output ++ s!"{vcr.obligation.label}: {vcr.formatOutcome}"
  return output

----------------------------------------------------------------------

-- Non-empty assumptions: the requires clause creates a path condition,
-- so the PE can resolve the obligation but not reachability.
private def assertTrueWithRequiresPgm :=
#strata
program Core;
procedure main(x : int) returns ()
spec {
  requires [precond]: x > 0;
} {
  assert [guarded_true]: true;
};
#end

/-- info: "guarded_true: ✔️ always true if reached" -/
#guard_msgs in
#eval do
  let results ← verify assertTrueWithRequiresPgm (options := options)
    (externalPhases := [Strata.frontEndPhase])
  let mut output := ""
  for vcr in results do
    output := output ++ s!"{vcr.obligation.label}: {vcr.formatOutcome}"
  return output

----------------------------------------------------------------------

private def assertFalseWithRequiresPgm :=
#strata
program Core;
procedure main(x : int) returns ()
spec {
  requires [precond]: x > 0;
} {
  assert [guarded_false]: false;
};
#end

/-- info: "guarded_false: ✖️ always false if reached" -/
#guard_msgs in
#eval do
  let results ← verify assertFalseWithRequiresPgm (options := options)
    (externalPhases := [Strata.frontEndPhase])
  let mut output := ""
  for vcr in results do
    output := output ++ s!"{vcr.obligation.label}: {vcr.formatOutcome}"
  return output

----------------------------------------------------------------------

end Strata
