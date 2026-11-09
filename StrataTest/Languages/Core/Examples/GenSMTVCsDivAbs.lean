/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Core
import StrataDDM.Integration.Lean.HashCommands
import Strata.MetaVerifier

open StrataDDM (Program)
---------------------------------------------------------------------
/-!
## `gen_smt_vcs` on integer `abs`

(Unsigned bitvector division is covered in `GenSMTVCsDenotation`.) Core has no
`abs` operator; it reaches the SMT encoding through truncating division
`int.divT`, whose operands are wrapped in `abs`.
-/
namespace Strata

private def absPgm : Program :=
#strata
program Core;

procedure tdiv(a : int, out r : int)
spec {
  ensures int.le(int.mul(r, 2), a) || int.lt(a, 0);
}
{
  assert [divT_one]: int.divT(a, 1) == a;
  assert [divT_neg]: int.divT(int.neg(a), 2) == int.neg(int.divT(a, 2));
  r := int.divT(a, 2);
};
#end

theorem absCorrect : smtVCsCorrect absPgm := by
  gen_smt_vcs
  all_goals grind

end Strata
