/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.MetaVerifier

open Strata

/-
Near-upstream anchors from `differential_status.md`:
- `verus-examples:guide/datatypes`
- `verus-examples:adts`
- `vlir-tests:rec_adt_structural`
-/

private def datatypeSelectorsSeed : Strata.Program :=
#strata
program Boole;

datatype OptionInt () { None(), Some(val: int) };

// This is the Boole-local analogue of the upstream datatype-constructor /
// selector cases: constructor tests, selector application, and datatype VCs.

procedure datatype_selector_seed(x: int) returns (ok: bool)
spec {
  ensures ok;
}
{
  var o : OptionInt;

  o := Some(x);
  assert OptionInt..isSome(o);
  assert OptionInt..val(o) == x;

  ok := OptionInt..isSome(o) && OptionInt..val(o) == x;
};
#end

/-- info: Obligation: assert_1_687
Property: assert
Result: ✅ pass

Obligation: assert_assert_2_718_calls_OptionInt..val_0
Property: assert
Result: ✅ pass

Obligation: assert_2_718
Property: assert
Result: ✅ pass

Obligation: set_ok_calls_OptionInt..val_0
Property: assert
Result: ✅ pass

Obligation: datatype_selector_seed_ensures_0_631
Property: assert
Result: ✅ pass-/
#guard_msgs in
#eval Strata.Boole.verify "cvc5" datatypeSelectorsSeed (options := .quiet)

example : Strata.smtVCsCorrect datatypeSelectorsSeed := by
  gen_smt_vcs
  all_goals (try grind)
