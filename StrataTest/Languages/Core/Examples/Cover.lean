/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Core.Verifier

---------------------------------------------------------------------
namespace Strata

def coverPgm1 :=
#strata
program Core;
procedure Test() returns ()
{
  var x : int;
  assume (x >= 0);

  if (false) {
    cover [unreachable_cover1]: (true);
    cover [unreachable_cover2]: (false);
    assert [unreachable_assert]: (false);
  } else {
    cover [reachable_cover]: (true);
    cover [unsatisfiable_cover]: (x == -1);
    assert [reachable_assert]: (true);
  }
};
#end


/--
info:
Obligation: unreachable_cover1
Property: cover
Result: ❌ fail

Obligation: unreachable_cover2
Property: cover
Result: ❌ fail

Obligation: unreachable_assert
Property: assert
Result: ✅ pass

Obligation: reachable_cover
Property: cover
Result: ✅ pass

Obligation: unsatisfiable_cover
Property: cover
Result: ❌ fail

Obligation: reachable_assert
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval verify coverPgm1 (options := Options.quiet)

---------------------------------------------------------------------

def coverPgm2 :=
#strata
program Core;
procedure Test(x : int) returns ()
spec {
  requires x > 1;
}
{
  if (x <= 1) {
    cover [ctest1]: (true);
  } else {
    cover [ctest2]: (x > 2);
    assert [atest2]: (x > 1);
  }
};
#end

/--
info:
Obligation: ctest1
Property: cover
Result: ❌ fail

Obligation: ctest2
Property: cover
Result: ✅ pass

Obligation: atest2
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval verify coverPgm2 (options := Options.quiet)

---------------------------------------------------------------------
