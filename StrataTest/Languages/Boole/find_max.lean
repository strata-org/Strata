/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.MetaVerifier

open Strata

private def find_max_program : Strata.Program :=
#strata
program Boole;

type Array := Map int int;

procedure FindMax(A : Array, n : int) returns (max : int)
spec
{
  requires n >= 1;
  ensures (∀ i:int . 0 <= i && i < n ==> A[i] <= max);
}
{
  max := A[0];
  for i : int := 1 to (n - 1) by 1
    invariant 1 <= i && i <= n
    invariant ∀ j:int . 0 <= j && j < i ==> A[j] <= max
  {
    if (A[i] > max) {
      max := A[i];
    }
  }
};
#end

/-- info: Obligation: entry_invariant_0_0
Property: assert
Result: ✅ pass

Obligation: entry_invariant_0_1
Property: assert
Result: ✅ pass

Obligation: arbitrary_iter_maintain_invariant_0_0
Property: assert
Result: ✅ pass

Obligation: arbitrary_iter_maintain_invariant_0_1
Property: assert
Result: ✅ pass

Obligation: FindMax_ensures_1_313
Property: assert
Result: ✅ pass-/
#guard_msgs in
#eval Strata.Boole.verify "cvc5" find_max_program (options := .quiet)

theorem find_max_program_smt_vcs_correct : Strata.smtVCsCorrect find_max_program := by
  gen_smt_vcs
  all_goals (try grind)
