/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.MetaVerifier

open Strata

/-
Near-upstream anchors from `differential_status.md`:
- `verus-examples:guide/integers`
- `verus-examples:quantifiers`
- `verus-examples:statements`
- Verus links:
  `guide/integers`: https://github.com/verus-lang/verus/blob/main/examples/guide/integers.rs
  `quantifiers`: https://github.com/verus-lang/verus/blob/main/examples/quantifiers.rs
  `statements`: https://github.com/verus-lang/verus/blob/main/examples/statements.rs
- Gap: widening casts only partially inserted
- Current status: the seed verifies after coercion points are spelled out
- Remaining gap: centralized insertion/preservation of widening casts
-/

private def wideningCastsSeed : Strata.Program :=
#strata
program Boole;

// Target shape: explicit widening/coercion pressure in a quantified formula,
// not only at function/procedure call sites.

type BvVec := Map int bv32;

function bv32_to_int_u(x: bv32) : int;

axiom (∀ x: bv32 . 0 <= bv32_to_int_u(x));

procedure widening_cast_seed(v: BvVec, n: int) returns ()
spec {
  requires 0 <= n;
  ensures ∀ i: int . 0 <= i && i < n ==> 0 <= bv32_to_int_u(v[i]);
}
{
  assert ∀ i: int . 0 <= i && i < n ==> 0 <= bv32_to_int_u(v[i]);
};
#end

#guard_msgs (drop info) in
#eval Strata.Boole.verify "cvc5" wideningCastsSeed

example : Strata.smtVCsCorrect wideningCastsSeed := by
  gen_smt_vcs
  all_goals
    intro Map inst n bv32_to_int_u select v hNonneg hn i hi
    exact hNonneg (select v i)
