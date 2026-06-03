/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.MetaVerifier

open Strata

/-!
Regression test: out-of-bounds check inside a conjunction.

`Bool.And` is now treated like `Bool.Implies` in `collectWFObligations`:
the LHS of `&&` is added as a hypothesis before collecting obligations
from the RHS.  This makes the bounds check on `Sequence.select(nums, j)`
in `0 <= j && j < Sequence.length(nums) && ret == Sequence.select(nums, j)`
provable — without the fix it returns ❓ unknown.
-/

private def seqOobConjunctionPgm : Strata.Program :=
#strata
program Boole;

procedure find_first (nums : Sequence bv32) returns (ret : bv32)
spec {
  requires Sequence.length(nums) > 0;
  ensures ∃ j : int :: 0 <= j && j < Sequence.length(nums) && ret == Sequence.select(nums, j);
}
{
  assume false;
  ret := Sequence.select(nums, 0);
  exit find_first;
};

#end

/-- info:
Obligation: find_first_post_find_first_ensures_1_729_calls_Sequence.select_0
Property: out-of-bounds access check
Result: ✅ pass

Obligation: set_ret_calls_Sequence.select_0
Property: out-of-bounds access check
Result: ✅ pass

Obligation: find_first_ensures_1_729
Property: assert
Result: ✅ pass-/
#guard_msgs in
#eval Strata.Boole.verify "cvc5" seqOobConjunctionPgm (options := .quiet)
