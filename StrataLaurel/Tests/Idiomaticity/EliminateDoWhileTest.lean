/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

/-
Tests that the `EliminateDoWhile` pass lowers a post-test `do … while` loop
to the pre-test form (see EliminateDoWhile.lean for the desugaring).

Uses `runPassForIdiomaticity`, the shared idiomaticity driver: it parses the
`#strata` program, resolves it, runs the one pass, and prints the result for the
`#guard_msgs` golden. An idiomaticity test does no more than that.
-/

import StrataLaurel.Tests.Util.TestLaurel

open StrataTest.Util
open Strata

-- A single do-while; lowered form is in the `#guard_msgs` block below.
/--
info: procedure basic()
  opaque
{
  var x: int := 0;
  {
    while(true)
      invariant 0 <= x && x <= 2 {
      {
        x := x + 1
      };
      if !(x < 3)
        then exit $dowhile_exit_0
    }
  }$dowhile_exit_0;
  assert x == 3
};
-/
#guard_msgs in
#eval runPassForIdiomaticity Strata.Laurel.eliminateDoWhilePass <|
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
#end

-- Nested do-whiles get distinct fresh exit labels (`_0` inner, `_1` outer).
/--
info: procedure nested()
  opaque
{
  var x: int := 0;
  {
    while(true)
      invariant 0 <= x {
      {
        var y: int := 0;
        {
          while(true)
            invariant 0 <= y {
            {
              y := y + 1
            };
            if !(y < 3)
              then exit $dowhile_exit_0
          }
        }$dowhile_exit_0;
        x := x + 1
      };
      if !(x < 3)
        then exit $dowhile_exit_1
    }
  }$dowhile_exit_1;
  assert x == 3
};
-/
#guard_msgs in
#eval runPassForIdiomaticity Strata.Laurel.eliminateDoWhilePass <|
#strata
program Laurel;
procedure nested()
  opaque
{
  var x: int := 0;
  do {
    var y: int := 0;
    do {
      y := y + 1
    } while(y < 3)
      invariant 0 <= y;
    x := x + 1
  } while(x < 3)
    invariant 0 <= x;
  assert x == 3
};
#end
