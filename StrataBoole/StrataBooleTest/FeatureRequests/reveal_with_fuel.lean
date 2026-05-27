/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import StrataBoole.MetaVerifier

open Strata

/-
Near-upstream anchors from `differential_status.md`:
- `verus-examples:test_expand_errors`
- `verus-examples:recursion`
- Verus links:
  `test_expand_errors`: https://github.com/verus-lang/verus/blob/main/examples/test_expand_errors.rs
  `recursion`: https://github.com/verus-lang/verus/blob/main/examples/recursion.rs
- Gap: `reveal_with_fuel` loses fuel amount
- Current status: the seed verifies only with an uninterpreted placeholder
- Remaining gap: bounded recursive unfolding tied to `reveal_with_fuel`
-/

private def revealWithFuelSeed : Strata.Program :=
#strata
program Boole;

// Target shape once bounded recursive unfolding is supported:
//
// rec function pow2(n: int) : int
// {
//   if n == 0 then 1 else 2 * pow2(n - 1)
// }
//
// procedure reveal_with_fuel_seed(n: int) returns ()
// spec {
//   requires 0 <= n;
//   ensures pow2(n) >= 1;
// }
// {
//   assert pow2(n) >= 1;
// };

function pow2(n: int) : int;

procedure reveal_with_fuel_seed(n: int) returns ()
spec {
  ensures true;
}
{
  assert pow2(n) == pow2(n);
};
#end

/-- info:
Obligation: assert_1_1146
Property: assert
Result: ✅ pass

Obligation: reveal_with_fuel_seed_ensures_0_1126
Property: assert
Result: ✅ pass-/
#guard_msgs in
#eval Strata.Boole.verify "cvc5" revealWithFuelSeed (options := .quiet)

example : Strata.smtVCsCorrectBoole revealWithFuelSeed := by
  gen_smt_vcs_boole
  all_goals (try grind)
