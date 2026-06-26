/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import StrataTest.Util.TestLaurel

open StrataTest.Util
open Strata

/-! ## `for`-loop invariant failures point at the specific invariant

The negative counterpart of `ForLoop.lean`. Like `WhileLoopsError.lean`, each
failing invariant's diagnostic is pinned to that invariant's own source range
(per-invariant source ranges threaded through loop elimination), rather than
the whole loop. -/

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
