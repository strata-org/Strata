/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.MetaVerifier

open Strata

/-
Near-upstream anchors from `differential_status.md`:
- `vlir-tests:rec_adt_structural`
- `verus-examples:quantifiers`
- `verus-examples:guide/integers`
- `verus-examples:power_of_2`
-/

private def natIntBoundarySeed : Strata.Program :=
#strata
program Boole;

// This file keeps the native-`nat` pressure explicit: abstract `nat`, explicit
// coercions, and an obligation that should become trivial once `nat` is modeled
// natively instead of via uninterpreted functions.

type nat;

function nat_to_int(n: nat) : int;
function int_to_nat(i: int) : nat;

axiom (forall i: int :: 0 <= i ==> nat_to_int(int_to_nat(i)) == i);

procedure nat_int_boundary_seed(n: nat, i: int) returns ()
spec {
  requires 0 <= i;
  ensures nat_to_int(int_to_nat(i)) == i;
}
{
  assume 0 <= nat_to_int(n);
  assert nat_to_int(int_to_nat(i)) == i;
};
#end

#guard_msgs (drop info) in
#eval Strata.Boole.verify "cvc5" natIntBoundarySeed

example : Strata.smtVCsCorrect natIntBoundarySeed := by
  gen_smt_vcs
  all_goals (try grind)
