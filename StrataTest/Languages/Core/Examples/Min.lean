/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Core.Verifier

---------------------------------------------------------------------
namespace Strata

private def testPgm : Program :=
#strata
program Core;

procedure min(n : int, m : int) returns (k : int)
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
if n@0 < m@1 then n@0 else m@1 <= n@0 && if n@0 < m@1 then n@0 else m@1 <= m@1

---
info:
Obligation: min_ensures_0
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval verify testPgm

---------------------------------------------------------------------
