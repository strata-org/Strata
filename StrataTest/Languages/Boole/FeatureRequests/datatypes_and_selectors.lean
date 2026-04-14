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
- Verus links:
  `guide/datatypes`: https://github.com/verus-lang/verus/blob/main/examples/guide/datatypes.rs
  `adts`: https://github.com/verus-lang/verus/blob/main/examples/adts.rs
- Current status: this small constructor/selector seed passes
- Remaining gap: richer datatype examples can still produce failed VCs even
  when Strata emits the expected VC shape
-/

private def datatypeSelectorsSeed : Strata.Program :=
#strata
program Boole;

datatype OptionInt () { None(), Some(val: int) };

// This is the Boole-local analogue of the upstream datatype-constructor /
// selector cases: constructor tests, selector application, and datatype VCs.
//
// This small example passes. Larger datatype examples can still fail on richer
// generated obligations.

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

/-- info:
Obligation: assert_1_1159
Property: assert
Result: ✅ pass

Obligation: assert_assert_2_1190_calls_OptionInt..val_0
Property: assert
Result: ✅ pass

Obligation: assert_2_1190
Property: assert
Result: ✅ pass

Obligation: set_ok_calls_OptionInt..val_0
Property: assert
Result: ✅ pass

Obligation: datatype_selector_seed_ensures_0_1103
Property: assert
Result: ✅ pass-/
#guard_msgs in
#eval Strata.Boole.verify "cvc5" datatypeSelectorsSeed (options := .quiet)

example : Strata.smtVCsCorrect datatypeSelectorsSeed := by
  gen_smt_vcs
  all_goals (try grind)
