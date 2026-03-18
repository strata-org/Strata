/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.MetaVerifier

open Strata

/-
Near-upstream anchors from `differential_status.md`:
- `verus-examples:guide/overflow`
- `verus-examples:overflow`
- Gap: `HasType` overflow guards dropped
-/

private def overflowGuardSeed : Strata.Program :=
#strata
program Boole;

// Target shape: these `fits_u32` conditions stand in for the dropped
// `HasType(U32, e)` overflow checks that should survive translation.

function fits_u32(i: int) : bool;

axiom (forall i: int :: fits_u32(i) ==> 0 <= i);
axiom (forall i: int :: fits_u32(i) ==> i < 4294967296);

procedure overflow_guard_seed(x: int) returns (y: int)
spec {
  requires fits_u32(x);
  requires fits_u32(x + 1);
  ensures y == x + 1;
  ensures fits_u32(y);
}
{
  y := x + 1;
  assert fits_u32(y);
};
#end

#eval Strata.Boole.verify "cvc5" overflowGuardSeed

example : Strata.smtVCsCorrect overflowGuardSeed := by
  gen_smt_vcs
  all_goals (try grind)
