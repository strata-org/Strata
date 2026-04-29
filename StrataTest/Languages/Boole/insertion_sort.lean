/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.MetaVerifier

open Strata

private def insertionSortPgm :=
#strata
program Boole;

type Array := Map int int;

var A : Array;
var n : int;

procedure InsertionSort() returns ()
spec
{
  modifies A;
  requires 0 <= n;
  requires n <= 1;
  ensures ∀ i:int, j:int . 0 <= i && i <= j && j < n ==> A[i] <= A[j];
}
{
  var j : int;
  var key : int;

  // for-loop syntax + array assignment syntax + quantifier syntax
  for i : int := 1 to (n - 1) by 1
    invariant 1 <= i && i <= n + 1
    invariant ∀ p:int, q:int . 0 <= p && p <= q && q < i ==> A[p] <= A[q]
  {
    key := A[i];
    j := i - 1;

    while (j >= 0 && A[j] > key)
      invariant (-1 <= j && j < i)
      invariant (∀ p:int, q:int . 0 <= p && p <= q && q < i ==> A[p] <= A[q])
    {
      A[j + 1] := A[j];
      j := j - 1;
    }

    A[j + 1] := key;
  }
};
#end

/-- info:
Obligation: entry_invariant_0_0
Property: assert
Result: ✅ pass

Obligation: entry_invariant_0_1
Property: assert
Result: ✅ pass

Obligation: entry_invariant_1_0
Property: assert
Result: ✅ pass

Obligation: entry_invariant_1_1
Property: assert
Result: ✅ pass

Obligation: arbitrary_iter_maintain_invariant_1_0
Property: assert
Result: ✅ pass

Obligation: arbitrary_iter_maintain_invariant_1_1
Property: assert
Result: ✅ pass

Obligation: arbitrary_iter_maintain_invariant_0_0
Property: assert
Result: ✅ pass

Obligation: arbitrary_iter_maintain_invariant_0_1
Property: assert
Result: ✅ pass

Obligation: InsertionSort_ensures_2_337
Property: assert
Result: ✅ pass-/
#guard_msgs in
#eval Strata.Boole.verify "cvc5" insertionSortPgm (options := .quiet)

example : Strata.smtVCsCorrect insertionSortPgm := by
  gen_smt_vcs
  all_goals (try grind)
