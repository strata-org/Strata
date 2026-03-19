/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.MetaVerifier

open Strata

/-
Near-upstream anchors from `differential_status.md`:
- Gap: Early return
- Upstream note: Verus SST `return expr;` is currently comment-only in translation
-/

private def earlyReturnSeed : Strata.Program :=
#strata
program Boole;

// Target shape once Boole has native return support:
//
// procedure abs_seed(x: int) returns (r: int)
// spec {
//   ensures 0 <= r;
// }
// {
//   if (x < 0) {
//     return 0 - x;
//   } else {
//     return x;
//   }
// };

procedure abs_seed(x: int) returns (r: int)
spec {
  ensures true;
}
{
  if (x < 0) {
    // TODO(feature:return): allow `return 0 - x;`.
    r := 0 - x;
  } else {
    // TODO(feature:return): allow `return x;`.
    r := x;
  }
};
#end

/-- info: Obligation: abs_seed_ensures_0_643
Property: assert
Result: ✅ pass-/
#guard_msgs in
#eval Strata.Boole.verify "cvc5" earlyReturnSeed (options := .quiet)

example : Strata.smtVCsCorrect earlyReturnSeed := by
  gen_smt_vcs
  all_goals (try grind)
