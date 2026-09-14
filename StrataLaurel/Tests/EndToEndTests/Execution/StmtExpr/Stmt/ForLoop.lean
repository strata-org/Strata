/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import StrataLaurel.Tests.Util.TestLaurel

open StrataTest.Util
open Strata

#eval testLaurelExecution {}
#strata
program Laurel;
procedure sumToThree()
  entry
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

-- Verification only: a loop invariant is a proof annotation, not a runtime check.
-- Concrete execution runs the real loop, so the interpreter reports nothing here.
#eval testLaurelExecution { skipCoreInterpreter := true }
#strata
program Laurel;
procedure forBadInitialInvariant()
  entry
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

-- Verification only, for the same reason as above.
#eval testLaurelExecution { skipCoreInterpreter := true }
#strata
program Laurel;
procedure forSecondInvFails()
  entry
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
