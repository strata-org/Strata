/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Core
import StrataDDM.Integration.Lean.HashCommands
import Strata.MetaVerifier

open StrataDDM (Program)
---------------------------------------------------------------------
namespace Strata

private def testPgm : Program :=
#strata
program Core;

procedure min(n : int, m : int, out k : int)
spec {
  ensures (int.le(k, n) && int.le(k, m));
}
{
  k := if int.lt(n, m) then n else m;
  k := k;
};
#end


/--
info: [Strata.Core] Type checking succeeded.


VCs:
Label: min_ensures_0
Property: assert
Obligation:
int.le(if int.lt(n@1, m@1) then n@1 else m@1, n@1) && int.le(if int.lt(n@1, m@1) then n@1 else m@1, m@1)

---
info:
Obligation: min_ensures_0
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval Core.verify testPgm

theorem testPgm_correct : smtVCsCorrect testPgm := by
  gen_smt_vcs
  grind

end Strata
---------------------------------------------------------------------
