/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT

  Regression test for `smtVCsCorrect` support for programs with user-defined
  datatypes whose selectors appear in verification conditions.

  This file tests all three fixes using a minimal program with a single-field
  datatype `Box` whose selector `Box..val` appears both in preconditions and
  in the postcondition.
-/

import Strata.MetaVerifier

open Strata

private def boxSelectorSeed : Strata.Program :=
#strata
program Boole;

datatype Box {
  Box_mk(val : int)
};

procedure inc_val(b : Box) returns (result : int)
spec {
  requires Box..val(b) >= 0;
  ensures result == Box..val(b) + 1;
}
{
  result := Box..val(b) + 1;
  exit inc_val;
};
#end

-- Fix 1 (SanitizedContext.ofCore) + Fix 2 (translateTerm datatype_op):
-- `Boole.verify` via cvc5 must succeed, and `gen_smt_vcs` must not throw
-- "datatype function not found in context".
/-- info:
Obligation: inc_val_pre_inc_val_requires_0_617_calls_Box..val_0
Property: assert
Result: ✅ pass

Obligation: inc_val_post_inc_val_ensures_1_646_calls_Box..val_0
Property: assert
Result: ✅ pass

Obligation: set_result_calls_Box..val_0
Property: assert
Result: ✅ pass

Obligation: inc_val_ensures_1_646
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval Strata.Boole.verify "cvc5" boxSelectorSeed (options := .quiet)

-- Fix 3 (denoteTerm datatype_op):
-- `smtVCsCorrect` must not reduce to `False`; all 4 VCs must be provable
-- with `gen_smt_vcs`.
example : Strata.smtVCsCorrect boxSelectorSeed := by
  gen_smt_vcs
  all_goals (try grind)
