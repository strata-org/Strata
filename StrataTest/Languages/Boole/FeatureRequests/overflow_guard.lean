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
- Verus links:
  `guide/overflow`: https://github.com/verus-lang/verus/blob/main/examples/guide/overflow.rs
  `overflow`: https://github.com/verus-lang/verus/blob/main/examples/overflow.rs
- Gap: `HasType` overflow guards dropped
- Current status: the seed verifies with explicit `fits_u32` predicates
- Remaining gap: deciding whether Verus-specific `HasType` checks should be
  modeled directly
-/

private def overflowGuardSeed : Strata.Program :=
#strata
program Boole;

// Target shape: these `fits_u32` conditions stand in for the dropped
// `HasType(U32, e)` overflow checks that should survive translation.

function fits_u32(i: int) : bool;

axiom (∀ i: int . fits_u32(i) ==> 0 <= i);
axiom (∀ i: int . fits_u32(i) ==> i < 4294967296);

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
Obligation: assert_6_1175
Property: assert
Result: ✅ pass

Obligation: overflow_guard_seed_ensures_4_1112
Property: assert
Result: ✅ pass

Obligation: overflow_guard_seed_ensures_5_1134
Property: assert
Result: ✅ pass-/
#guard_msgs in
#eval Strata.Boole.verify "cvc5" overflowGuardSeed (options := .quiet)

example : Strata.smtVCsCorrect overflowGuardSeed := by
  gen_smt_vcs
  all_goals (try grind)
