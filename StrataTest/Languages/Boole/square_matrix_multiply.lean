/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.MetaVerifier

namespace Strata

/-
General Boole example based on the textbook square-matrix-multiply algorithm.

Purpose:
- keep a nested-loop matrix benchmark in the main Boole example suite
- exercise direct nested `for ... to` lowering end to end
- current status: this example verifies with direct nested `for` loops
-/

private def squareMatrixMult :=
#strata
program Boole;

var A : (Map int (Map int int));
var B : (Map int (Map int int));
var C : (Map int (Map int int));

procedure SquareMatrixMultiply(n: int) returns ()
spec
{
  requires n >= 1;
  modifies C;
}
{
  for i:int := 1 to n
    invariant 1 <= i
    invariant i <= n + 1
  {
    for j:int := 1 to n
      invariant 1 <= j
      invariant j <= n + 1
    {
      C[i][j] := 0;
      for k:int := 1 to n
        invariant 1 <= k
        invariant k <= n + 1
      {
        C[i][j] := (C[i])[j] + ((A[i])[k] * (B[k])[j]);
      }
    }
  }
};

#end

/-- info:
Obligation: loopElimAssert_loop_0_entry_invariant_0
Property: assert
Result: ✅ pass

Obligation: loopElimAssert_loop_0_entry_invariant_1
Property: assert
Result: ✅ pass

Obligation: loopElimAssert_loop_1_entry_invariant_0
Property: assert
Result: ✅ pass

Obligation: loopElimAssert_loop_1_entry_invariant_1
Property: assert
Result: ✅ pass

Obligation: loopElimAssert_loop_2_entry_invariant_0
Property: assert
Result: ✅ pass

Obligation: loopElimAssert_loop_2_entry_invariant_1
Property: assert
Result: ✅ pass

Obligation: loopElimAssert_loop_2_arbitrary_iter_maintain_invariant_0
Property: assert
Result: ✅ pass

Obligation: loopElimAssert_loop_2_arbitrary_iter_maintain_invariant_1
Property: assert
Result: ✅ pass

Obligation: loopElimAssert_loop_1_arbitrary_iter_maintain_invariant_0
Property: assert
Result: ✅ pass

Obligation: loopElimAssert_loop_1_arbitrary_iter_maintain_invariant_1
Property: assert
Result: ✅ pass

Obligation: loopElimAssert_loop_0_arbitrary_iter_maintain_invariant_0
Property: assert
Result: ✅ pass

Obligation: loopElimAssert_loop_0_arbitrary_iter_maintain_invariant_1
Property: assert
Result: ✅ pass-/
#guard_msgs in
#eval Strata.Boole.verify "cvc5" squareMatrixMult (options := .quiet)

example : Strata.smtVCsCorrect squareMatrixMult := by
  gen_smt_vcs
  all_goals (try grind)
