/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.MetaVerifier

open Strata

/-
Near-upstream anchors from `differential_status.md`:
- `verus-examples:trigger_loops` (`choose_example`, `quantifier_example`)
- Gap: `choose` operator not faithfully translated
- Intended encoding: `havoc z; assume (exists z' :: g(z')) ==> g(z);`
-/

private def chooseOperatorSeed : Strata.Program :=
#strata
program Boole;

function good(z: int, x: int) : bool;

// Target shape once Boole has direct `choose` syntax:
//
// procedure choose_seed(x: int) returns (w: int)
// spec {
//   requires exists z: int :: good(z, x);
//   ensures good(w, x);
// }
// {
//   w := choose z: int :: good(z, x);
// };

procedure choose_seed(x: int) returns (w: int)
spec {
  requires exists z: int :: good(z, x);
  ensures good(w, x);
}
{
  havoc w;
  // TODO(feature:choose): allow `w := choose z: int :: good(z, x);`.
  assume good(w, x);
};
#end

#eval Strata.Boole.verify "cvc5" chooseOperatorSeed

example : Strata.smtVCsCorrect chooseOperatorSeed := by
  gen_smt_vcs
  all_goals (try grind)
