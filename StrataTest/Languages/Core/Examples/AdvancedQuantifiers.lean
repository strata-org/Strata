/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Core.Verifier

---------------------------------------------------------------------
namespace Strata

def advQuantPgm :=
#strata
program Core;
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


/-

info: [Strata.Core] Type checking succeeded.
-/
#guard_msgs in
#eval verify "cvc5" advQuantPgm
