/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.MetaVerifier

open Strata

/-

/* Finds and returns the largest integer in a non-empty vector by iterating through its elements. */
#[allow(unused_imports)]
use vstd::prelude::*;
fn main() {}

verus! {

#[verifier::loop_isolation(false)]
fn find_max(nums: Vec<i32>) -> (ret:i32)
    requires
        nums.len() > 0
    ensures
        forall|i: int| 0 <= i && i < nums.len() ==> ret >= nums[i],
        exists|j: int| 0 <= j && j < nums.len() && ret == nums[j]
{
    let mut max = nums[0];
    let mut i = 1;

    while i < nums.len()
        invariant
            nums.len() > 0,
            0 <= i && i <= nums.len(),
            forall|k: int| 0 <= k && k < i ==> max >= nums[k],
            exists|j: int| 0 <= j && j < i && max == nums[j]
        decreases nums.len() - i
    {
        if nums[i] > max {
            max = nums[i];
        }
        i += 1;
    }

    max
}
}
// Score: (1, 0)
// Safe: True

-/

def findMax : Strata.Program :=
#strata
program Boole;

procedure witnessOccurs(nums: Map int int, n: int, idx: int, value: int) returns ()
spec {
  requires 0 <= idx && idx < n;
  requires value == nums[idx];
  ensures ∃ j: int . 0 <= j && j < n && value == nums[j];
}
{
  assume ∃ j: int . 0 <= j && j < n && value == nums[j];
};

procedure findMax (nums: Map int int, n: int) returns (ret: int)
spec {
  requires n > 0;
  ensures ∀ i: int . 0 <= i && i < n ==> ret >= nums[i];
  ensures ∃ j: int . 0 <= j && j < n && ret == nums[j];
}
{
  var max : int := nums[0];
  var maxIndex : int := 0;
  var i : int := 1;

  while (i < n)
    decreases n - i
    invariant (1 <= i && i <= n)
    invariant (∀ k: int . 0 <= k && k < i ==> max >= nums[k])
    invariant (0 <= maxIndex && maxIndex < i && max == nums[maxIndex])
  {
    if (nums[i] > max) {
      max := nums[i];
      maxIndex := i;
    }
    i := i + 1;
  }
  assert 0 <= maxIndex && maxIndex < n && max == nums[maxIndex];
  ret := nums[maxIndex];
  call witnessOccurs(nums, n, maxIndex, ret);
};
#end

/-- info:
Obligation: witnessOccurs_ensures_2_1229
Property: assert
Result: ✅ pass

Obligation: entry_invariant_0_0
Property: assert
Result: ✅ pass

Obligation: entry_invariant_0_1
Property: assert
Result: ✅ pass

Obligation: entry_invariant_0_2
Property: assert
Result: ✅ pass

Obligation: arbitrary_iter_maintain_invariant_0_0
Property: assert
Result: ✅ pass

Obligation: arbitrary_iter_maintain_invariant_0_1
Property: assert
Result: ✅ pass

Obligation: arbitrary_iter_maintain_invariant_0_2
Property: assert
Result: ✅ pass

Obligation: assert_7_1950
Property: assert
Result: ✅ pass

Obligation: callElimAssert_witnessOccurs_requires_0_1166_4
Property: assert
Result: ✅ pass

Obligation: callElimAssert_witnessOccurs_requires_1_1198_5
Property: assert
Result: ✅ pass

Obligation: findMax_ensures_5_1448
Property: assert
Result: ✅ pass

Obligation: findMax_ensures_6_1508
Property: assert
Result: ✅ pass-/
#guard_msgs in
#eval Strata.Boole.verify "cvc5" findMax (options := .quiet)

example : Strata.smtVCsCorrect findMax := by
  gen_smt_vcs
  all_goals (try grind)
