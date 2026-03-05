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

procedure findMax (nums: Map int int, n: int) returns (ret: int)
spec {
  requires n > 0;
  ensures forall i: int :: 0 <= i && i < n ==> ret >= nums[i];
  ensures exists j: int :: 0 <= j && j < n && ret == nums[j];
}
{
  var max : int := nums[0];
  var i : int := 1;

  while (i < n)
    // decreases n - i;
    invariant (n > 0)
    invariant (0 <= i && i <= n)
    invariant (forall k: int :: 0 <= k && k < i ==> max >= nums[k])
    invariant (exists j: int :: 0 <= j && j < i && max == nums[j])
  {
    if (nums[i] > max) {
      max := nums[i];
    }
    i := i + 1;
  }
  ret := max;
};
#end

theorem findMax_smtVCsCorrect : smtVCsCorrect findMax := by
  gen_smt_vcs
  case arbitrary_iter_maintain_invariant_0_3 =>
    intro Map _ n i max nums get h1 hin h0 ⟨hi1, hi2⟩ (hi3 : ∀ k, _) ⟨j, hi4⟩
    intros
    grind
  case findMax_ensures_1_1080 =>
    simp only [and_imp]
    grind
  case findMax_ensures_2_1143 =>
    intros
    grind
  all_goals (try grind)
