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
//
// This is currently lower priority because `HasType` is Verus-specific
// rather than a core Boole feature.

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

/-- info:
Obligation: assert_6_937
Property: assert
Result: ✅ pass

Obligation: overflow_guard_seed_ensures_4_874
Property: assert
Result: ✅ pass

Obligation: overflow_guard_seed_ensures_5_896
Property: assert
Result: ✅ pass-/
#guard_msgs in
#eval Strata.Boole.verify "cvc5" overflowGuardSeed (options := .quiet)

example : Strata.smtVCsCorrect overflowGuardSeed := by
  gen_smt_vcs
  all_goals (try grind)
