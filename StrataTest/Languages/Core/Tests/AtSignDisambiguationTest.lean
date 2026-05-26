/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Core.Verifier

/-! ## Test: parameter names containing `@` are disambiguated from `@N` suffixes

Strata identifiers can contain `@`, so a parameter named `g@1` could collide
with the `@N` disambiguation suffix of another variable `g`. This test verifies
that `genSym` decomposes `@N` suffixes and increments them rather than appending
a second `@`, producing `g@2` and `g@3` instead of `g@2` and `g@1@1`.
-/

namespace Strata

private def atSignDisambiguation : Program :=
#strata
program Core;
procedure Test(g : int, g@1 : int, out r : int)
spec {
  ensures (g == g@1);
}
{
  r := 0;
};
#end

/--
info: [Strata.Core] Type checking succeeded.


VCs:
Label: Test_ensures_0
Property: assert
Obligation:
g@2 == g@3

---
info:
Obligation: Test_ensures_0
Property: assert
Result: ❌ fail
Model:
(g@2, -(1)) (g@3, 0)
-/
#guard_msgs in
#eval verify atSignDisambiguation

---------------------------------------------------------------------
