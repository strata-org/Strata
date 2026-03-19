/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.MetaVerifier

open Strata

/-
Near-upstream anchors from `differential_status.md`:
- `verus-examples:fun_ext`
- `verus-examples:trait_for_fn`
- Gap: higher-order / lambda support
-/

private def higherOrderSeed : Strata.Program :=
#strata
program Boole;

// Target shape: inline lambdas / closures / higher-order values, not only a
// first-order uninterpreted-function encoding.

type FnIntInt;

function apply(f: FnIntInt, x: int) : int;

procedure higher_order_seed(f: FnIntInt, x: int) returns (y: int)
spec {
  ensures y == apply(f, x);
}
{
  // TODO(feature:lambda): allow inline lambdas/closures, not only first-order encodings.
  y := apply(f, x);
};
#end

/-- info: Obligation: higher_order_seed_ensures_0_615
Property: assert
Result: ✅ pass-/
#guard_msgs in
#eval Strata.Boole.verify "cvc5" higherOrderSeed (options:=.quiet)

example : Strata.smtVCsCorrect higherOrderSeed := by
  gen_smt_vcs
  all_goals (try grind)
