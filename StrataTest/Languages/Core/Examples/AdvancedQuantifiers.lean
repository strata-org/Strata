/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

meta import Strata.Languages.Core.Verifier
import StrataDDM.Integration.Lean.HashCommands

meta section
---------------------------------------------------------------------
namespace Strata

def advQuantPgm :=
#strata
program Core;
axiom [mapAllValues0]: forall m: (Map int int), k: int :: m[k] == 0;
procedure Update(mArg: Map int int, kArg: int, out res: int)
spec {
  ensures mArg[kArg] == 0;
}
{
  assert [a]: mArg[kArg] == 0;
  res := mArg[kArg];
};
#end


/--
info: [Strata.Core] Type checking succeeded.


VCs:
Label: a
Property: assert
Assumptions:
mapAllValues0: forall m : (Map int int) :: forall k : int :: m[k] == 0
Obligation:
mArg@1[kArg@1] == 0

Label: Update_ensures_0
Property: assert
Assumptions:
mapAllValues0: forall m : (Map int int) :: forall k : int :: m[k] == 0
Obligation:
mArg@1[kArg@1] == 0

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
#eval verify advQuantPgm

end Strata
end
