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

#eval Strata.Boole.verify "cvc5" datatypeSelectorsSeed

example : Strata.smtVCsCorrect datatypeSelectorsSeed := by
  gen_smt_vcs
  all_goals (try grind)
