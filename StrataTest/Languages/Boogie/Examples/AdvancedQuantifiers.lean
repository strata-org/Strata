/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Boogie.Verifier

---------------------------------------------------------------------
namespace Strata

def advQuantPgm :=
#strata
program Boogie;
axiom [mapAllValues0]: forall m: (Map int int), k: int :: m[k] == 0;
procedure Update(mArg: Map int int, kArg: int) returns (res: int)
spec {
  ensures mArg[kArg] == 0;
}
{
  assert [a]: mArg[kArg] == 0;
  res := mArg[kArg];
};
#end


/--
info: [Strata.Boogie] Type checking succeeded.


VCs:
Label: a
Property: assert
Assumptions:

(mapAllValues0, (∀ (∀ (((~select %1) %0) == #0))))
Proof Obligation:
(((~select $__mArg0) $__kArg1) == #0)

Label: Update_ensures_0
Property: assert
Assumptions:

(mapAllValues0, (∀ (∀ (((~select %1) %0) == #0))))
Proof Obligation:
(((~select $__mArg0) $__kArg1) == #0)

---
info:
Obligation: a
Property: assert
Result: ✅ pass

Obligation: Update_ensures_0
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval verify "cvc5" advQuantPgm
