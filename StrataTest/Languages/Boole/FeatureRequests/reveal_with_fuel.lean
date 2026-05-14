/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.MetaVerifier

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

// Target shape once recursive reveal support works end-to-end:
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
//   // TODO(feature:reveal_with_fuel): distinguish bounded unfolding from full reveal.
//   assert pow2(n) >= 1;
// };

function pow2(n: int) : int;

procedure reveal_with_fuel_seed(n: int) returns ()
spec {
  ensures true;
}
{
  // Lower priority for now: this depends on first deciding whether to support
  // the Verus-specific `opaque` / `reveal` family at all, rather than spending
  // time on bounded fuel before the base semantics are settled.
  // TODO(feature:reveal_with_fuel): switch `pow2` back to a recursive definition and
  // model bounded unfolding once recursive reveal support is available end-to-end.
  // TODO(feature:reveal_with_fuel): distinguish bounded unfolding from full reveal.
  assert pow2(n) == pow2(n);
};
#end

#guard_msgs (drop info) in
#eval Strata.Boole.verify "cvc5" revealWithFuelSeed

example : Strata.smtVCsCorrect revealWithFuelSeed := by
  gen_smt_vcs
  all_goals (try grind)
