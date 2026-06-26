/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import StrataTest.Util.TestLaurel

open StrataTest.Util
open Strata

/-! ## `do-while` invariant / assertion failures

The negative counterpart of `DoWhile.lean`. `do BODY while(COND) invariant I`
desugars (via `EliminateDoWhile`) to a pre-test `while(true)` whose invariant is
checked at the loop head — *before* the first BODY runs — so an invariant that
is false on entry is rejected exactly as for `while`. Each failing invariant's
diagnostic is pinned to that invariant's own source range. -/

/-! ### The initial invariant fails on entry -/

#eval testLaurel
#strata
program Laurel;
procedure doWhileBadInitialInvariant()
  opaque
{
    var i: int := -1;
    do {
      i := i + 1
    } while(i < 10)
      invariant i >= 0
//              ^^^^^^ error: assertion does not hold
};
#end

/-! ### A later invariant fails while earlier ones hold -/

#eval testLaurel
#strata
program Laurel;
procedure doWhileSecondInvFails()
  opaque
{
    var i: int := 0;
    var j: int := -1;
    do {
      i := i + 1;
      j := j + 1
    } while(i < 10)
      invariant i >= 0
      invariant j >= 0
//              ^^^^^^ error: assertion does not hold
};
#end
