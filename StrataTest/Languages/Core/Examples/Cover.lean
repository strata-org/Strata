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
    @[checkAssumptionsSat:true] cover [unreachable_cover1]: (true);
    @[checkAssumptionsSat:false] cover [unreachable_cover2]: (false);
     assert [unreachable_assert]: (false);
  } else {
    cover [reachable_cover]: (true);
    @[checkAssumptionsSat:true] cover [unsatisfiable_cover]: (x == -1);
    @[checkAssumptionsSat:false] assert [reachable_assert]: (true);

  }
};
#end

/--
info:
Obligation: unreachable_cover1
Property: cover
Assumptions Sat Check: ❌ fail
Result: ❌ fail

Obligation: unreachable_cover2
Property: cover
Result: ❌ fail

Obligation: unreachable_assert
Property: assert
Assumptions Sat Check: ❌ fail
Result: ✅ pass

Obligation: reachable_cover
Property: cover
Assumptions Sat Check: ✅ pass
Result: ✅ pass
Model:
(init_x_0, 0)

Obligation: unsatisfiable_cover
Property: cover
Assumptions Sat Check: ✅ pass
Result: ❌ fail

Obligation: reachable_assert
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval verify "z3" coverPgm1
          (options := {Options.quiet with solverTimeout := 1,
                                          checkAssumptionsSat := true})

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
    @[checkAssumptionsSat:true] cover [ctest1]: (true);
  } else {
    cover [ctest2]: (x > 2);
    @[checkAssumptionsSat:true] assert [atest2]: (x > 1);
  }
};
#end

/--
info:
Obligation: ctest1
Property: cover
Assumptions Sat Check: ❌ fail
Result: ❌ fail

Obligation: ctest2
Property: cover
Result: ✅ pass
Model:
($__x0, 3)

Obligation: atest2
Property: assert
Assumptions Sat Check: ✅ pass
Result: ✅ pass
-/
#guard_msgs in
#eval verify "z3" coverPgm2
      (options := {Options.quiet with checkAssumptionsSat := false})

---------------------------------------------------------------------
