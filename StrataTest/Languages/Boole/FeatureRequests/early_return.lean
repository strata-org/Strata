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

Early return is implemented via `exit functionName;`:
  1. The Boole → Core translator wraps every procedure body in a labeled
     block named after the procedure.
  2. `exit functionName;` in the body exits that block, skipping any
     remaining statements — i.e., an early return.
  3. Output variables must be assigned before the exit, as with any early
     return style.
-/

private def earlyReturnSeed : Strata.Program :=
#strata
program Boole;

procedure abs_seed(x: int) returns (r: int)
spec {
  ensures 0 <= r;
}
{
  if (x < 0) {
    r := 0 - x;
    exit abs_seed;
  }
  r := x;
};
#end

/-- info:
Obligation: abs_seed_ensures_0_797
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval Strata.Boole.verify "cvc5" earlyReturnSeed (options := .quiet)

example : Strata.smtVCsCorrect earlyReturnSeed := by
  gen_smt_vcs
  all_goals (try grind)
