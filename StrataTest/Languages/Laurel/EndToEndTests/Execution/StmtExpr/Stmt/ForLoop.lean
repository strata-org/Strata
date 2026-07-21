/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import StrataTest.Util.TestLaurel

open StrataTest.Util
open Strata

#eval testLaurel
#strata
program Laurel;
procedure sumToThree()
  opaque
{
  var sum: int := 0;
  for (var i: int := 0; i < 3; i := i + 1)
    invariant sum >= 0
    invariant sum <= 3
    invariant i >= 0
    invariant i <= 3
    invariant sum == i
  {
    sum := sum + 1
  };
  assert sum == 3
};
#end

/-! ## `for`-loop invariant failures point at the specific invariant

Each failing invariant's diagnostic is pinned to that invariant's own source
range (per-invariant source ranges threaded through loop elimination), rather
than the whole loop. -/

/-! ### The initial invariant fails on entry -/

#eval testLaurel
#strata
program Laurel;
procedure forBadInitialInvariant()
  opaque
{
    var sum: int := -1;
    for(var i: int := 0; i < 10; i := i + 1)
      invariant sum >= 0
//              ^^^^^^^^ error: assertion does not hold
    {
        sum := sum + 1
    }
};
#end

/-! ### A later invariant fails while earlier ones hold -/

#eval testLaurel
#strata
program Laurel;
procedure forSecondInvFails()
  opaque
{
    var j: int := -1;
    for(var i: int := 0; i < 10; i := i + 1)
      invariant i >= 0
      invariant j >= 0
//              ^^^^^^ error: assertion does not hold
    {
        j := j + 1
    }
};
#end
