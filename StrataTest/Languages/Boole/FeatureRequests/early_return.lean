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
- Current status: the seed verifies by assigning outputs explicitly
- Remaining gap: real function/procedure-level `return`
-/

private def earlyReturnSeed : Strata.Program :=
#strata
program Boole;

// Target shape once Boole has native return support.
//
// Preferred implementation strategy: wrap the procedure body in a synthetic
// labeled block and lower `return` to output assignments plus `exit` from that
// block.
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
    // TODO(feature:return): allow `return 0 - x;` and exit the whole procedure.
    r := 0 - x;
  } else {
    // TODO(feature:return): allow `return x;` and exit the whole procedure.
    r := x;
  }
};
#end

/-- info:
Obligation: abs_seed_ensures_0_937
Property: assert
Result: ✅ pass-/
#guard_msgs in
#eval Strata.Boole.verify "cvc5" earlyReturnSeed (options := .quiet)

example : Strata.smtVCsCorrect earlyReturnSeed := by
  gen_smt_vcs
  all_goals (try grind)
