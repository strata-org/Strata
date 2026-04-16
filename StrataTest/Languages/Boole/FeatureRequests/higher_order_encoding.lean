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
- Verus links:
  `fun_ext`: https://github.com/verus-lang/verus/blob/main/examples/fun_ext.rs
  `trait_for_fn`: https://github.com/verus-lang/verus/blob/main/examples/trait_for_fn.rs
- Gap: higher-order function values beyond a first-order `apply` encoding
- Current status: the seed verifies with a first-order uninterpreted `apply`
  encoding
- Remaining gap: native higher-order values and calls without the
  `FnIntInt`/`apply` workaround
-/

private def higherOrderSeed : Strata.Program :=
#strata
program Boole;

// Target shape: higher-order values and calls without an explicit `apply`
// wrapper.

type FnIntInt;

function apply(f: FnIntInt, x: int) : int;

procedure higher_order_seed(f: FnIntInt, x: int) returns (y: int)
spec {
  ensures y == apply(f, x);
}
{
  y := apply(f, x);
};
#end

/-- info:
Obligation: higher_order_seed_ensures_0_983
Property: assert
Result: ✅ pass-/
#guard_msgs in
#eval Strata.Boole.verify "cvc5" higherOrderSeed (options:=.quiet)

example : Strata.smtVCsCorrect higherOrderSeed := by
  gen_smt_vcs
  all_goals (try grind)
