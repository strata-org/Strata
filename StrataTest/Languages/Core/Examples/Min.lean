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
Assumptions:


Proof Obligation:
((~Bool.And ((~Int.Le (if ((~Int.Lt $__n0) $__m1) then $__n0 else $__m1)) $__n0)) ((~Int.Le (if ((~Int.Lt $__n0) $__m1) then $__n0 else $__m1)) $__m1))

---
info:
Obligation: min_ensures_0
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval verify "cvc5" testPgm

---------------------------------------------------------------------
