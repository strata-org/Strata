/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.MetaVerifier

open Strata

/-
Near-upstream anchors from `differential_status.md`:
- `verus-examples:guide/ext_equal`
- Gap: extensional equality lowered to ordinary equality
-/

private def mapExtensionalitySeed : Strata.Program :=
#strata
program Boole;

type IntMap := Map int int;

// Target shape once Boole/Strata distinguish extensional equality from `==`:
//
// spec {
//   requires forall i: int :: a[i] == b[i];
//   ensures a =~= b;
// }

procedure map_extensionality_seed(a: IntMap, b: IntMap) returns ()
spec {
  requires forall i: int :: a[i] == b[i];
  ensures a == b;
}
{
  assert a == b;
};
#end

#eval Strata.Boole.verify "cvc5" mapExtensionalitySeed

example : Strata.smtVCsCorrect mapExtensionalitySeed := by
  gen_smt_vcs
  all_goals (try grind)
