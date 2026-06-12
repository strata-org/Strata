/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import StrataTest.Util.TestLaurel

open StrataTest.Util
open Strata

/-! ## Loop-invariant failures point at the specific invariant

These negative tests pin each failing loop invariant's diagnostic to that
invariant's own source range (per-invariant source ranges threaded through
loop elimination), rather than the whole loop. -/

#eval testLaurel
#strata
program Laurel;
procedure badInitialInvariant()
  opaque
{
    var i: int := -1;
    while(i < 10)
      invariant i >= 0
//              ^^^^^^ error: assertion does not hold
    {
        i := i + 1
    }
};
#end

#eval testLaurel
#strata
program Laurel;
procedure secondInvariantFails()
  opaque
{
    var i: int := 0;
    var j: int := -1;
    while(i < 10)
      invariant i >= 0
      invariant j >= 0
//              ^^^^^^ error: assertion does not hold
    {
        i := i + 1;
        j := j + 1
    }
};
#end

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
