/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import StrataTest.Util.TestLaurel

open StrataTest.Util
open Strata

/-! ## Post-test `do-while`

`do BODY while(COND) invariant I` is a post-test loop: BODY runs once before
COND is first tested. It parses to a post-test `While` (`postTest := true`),
desugared by the `EliminateDoWhile` pass to a pre-test `while(true)` whose body
ends with `if (!COND) exit`. The invariant `I` is checked at the loop head —
*before* each BODY runs, matching `while`. Gotcha: because the guard is re-tested
only after BODY, an invariant must hold of the *pre-body* state. For
`do { x := x+1 } while(x<3)` the loop exits at x==3, but the head invariant sees
the pre-increment value, so the bound is `x <= 2` (not `x <= 3`). -/

#eval testLaurel
#strata
program Laurel;
procedure basic()
  opaque
{
  var x: int := 0;
  do {
    x := x + 1
  } while(x < 3)
    invariant 0 <= x && x <= 2;
  assert x == 3
};

procedure runsAtLeastOnce()
  opaque
{
  var x: int := 5;
  do {
    x := x + 1
  } while(x < 3)
    invariant x == 5;
  assert x == 6
};

procedure nested()
  opaque
{
  var x: int := 0;
  do {
    var y: int := 0;
    do {
      y := y + 1
    } while(y < 3)
      invariant 0 <= y
      invariant y <= 2;
    x := x + 1
  } while(x < 3)
    invariant 0 <= x
    invariant x <= 2;
  assert x == 3
};

procedure breakOut()
  opaque
{
  var x: int := 0;
  {
    do {
      x := x + 1;
      if (x >= 2) then { exit early }
    } while(x < 5)
      invariant 0 <= x && x <= 2
  } early;
  assert 2 <= x && x <= 3
};

procedure noInvariant()
  opaque
{
  var x: int := 0;
  do {
    x := x + 1
  } while(x < 3);
  assert x >= 3
};
#end

/-! ## A false postcondition is still rejected

Confirms the `while(true)` desugar isn't vacuous: the body's effect reaches the
assertion, so an unprovable assert is reported (not discharged vacuously). -/

#eval testLaurel
#strata
program Laurel;
procedure falsePostRejected()
  opaque
{
  var x: int := 0;
  do {
    x := x + 1
  } while(x < 3)
    invariant 0 <= x && x <= 2;
  assert x == 99
//^^^^^^^^^^^^^^ error: assertion could not be proved
};
#end
