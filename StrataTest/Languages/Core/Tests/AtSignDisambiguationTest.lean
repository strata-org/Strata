/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Core.Verifier

/-! ## Test: parameter names containing `@` are disambiguated from `@N` suffixes

Strata identifiers can contain `@`, so a parameter named `g@1` could collide
with the `@N` disambiguation suffix of another variable `g`. This test verifies
that the symbolic evaluator and SMT encoder produce distinct names for both.
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
g@2 == g@1@1

---
info:
Obligation: Test_ensures_0
Property: assert
Result: ❌ fail
Model:
(g@2, -(1)) (g@1@1, 0)
-/
#guard_msgs in
#eval verify atSignDisambiguation

---------------------------------------------------------------------
