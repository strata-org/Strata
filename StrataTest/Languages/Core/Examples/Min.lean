/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

meta import Strata.Languages.Core.Core
import StrataDDM.Integration.Lean.HashCommands

meta section
open StrataDDM (Program)
---------------------------------------------------------------------
namespace Strata

private def testPgm : Program :=
#strata
program Core;

procedure min(n : int, m : int, out k : int)
spec {
  ensures ((k <= n) && (k <= m));
}
{
  k := if (n < m) then n else m;
  k := k;
};
#end


/--
info: [Strata.Core] Type checking succeeded.


VCs:
Label: min_ensures_0
Property: assert
Obligation:
if n@1 < m@1 then n@1 else m@1 <= n@1 && if n@1 < m@1 then n@1 else m@1 <= m@1

---
info:
Obligation: min_ensures_0
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval Core.verify testPgm

end Strata
end
---------------------------------------------------------------------
