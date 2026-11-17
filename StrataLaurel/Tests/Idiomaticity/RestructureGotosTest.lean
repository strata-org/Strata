/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

/-
Tests that the `RestructureGotos` pass lowers a block that is the target of a
backward `goto` to a `while(true)` loop, and a block with invariants but no
backward `goto` to entry assertions (see RestructureGotos.lean).

Uses `runPassForIdiomaticity`, the shared idiomaticity driver.
-/

import StrataLaurel.Tests.Util.TestLaurel

open StrataTest.Util
open Strata

-- A do-while spelled with a backward `goto`: the block becomes a loop whose
-- invariant sits on the loop head.
/-- info: procedure countUp()
  opaque
{
  var i: int := 0;
  {
    while(true)
      invariant 0 <= i && i <= 3 {
      i := i + 1;
      if i < 3
        then {
          exit $goto_start_0
        };
      exit again
    }$goto_start_0
  }again;
  assert i == 3
};
-/
#guard_msgs in
#eval runPassForIdiomaticity Strata.Laurel.restructureGotosPass <|
#strata
program Laurel;
procedure countUp()
  opaque
{
  var i: int := 0;
  {
    i := i + 1;
    if (i < 3) then { goto again }
  } again
    invariant 0 <= i && i <= 3;
  assert i == 3
};
#end

-- Nested loops: an inner `goto outer` leaves the inner loop and re-enters the
-- outer one, and an `exit` keeps leaving its block.
/-- info: procedure nested()
  opaque
{
  var i: int := 0;
  {
    while(true) {
      {
        while(true) {
          i := i + 1;
          if i < 3
            then {
              exit $goto_start_0
            };
          if i < 6
            then {
              exit $goto_start_1
            };
          exit outer
        }$goto_start_0
      }inner;
      exit outer
    }$goto_start_1
  }outer
};
-/
#guard_msgs in
#eval runPassForIdiomaticity Strata.Laurel.restructureGotosPass <|
#strata
program Laurel;
procedure nested()
  opaque
{
  var i: int := 0;
  {
    {
      i := i + 1;
      if (i < 3) then { goto inner };
      if (i < 6) then { goto outer };
      exit outer
    } inner
  } outer
};
#end

-- A block with invariants that no `goto` targets is not a loop: its invariants
-- are asserted on entry.
/-- info: procedure noBackwardJump()
  opaque
{
  var i: int := 0;
  {
    assert i == 0;
    {
      i := i + 1
    }once
  }
};
-/
#guard_msgs in
#eval runPassForIdiomaticity Strata.Laurel.restructureGotosPass <|
#strata
program Laurel;
procedure noBackwardJump()
  opaque
{
  var i: int := 0;
  {
    i := i + 1
  } once
    invariant i == 0
};
#end

-- Two forward jumps whose ranges overlap without nesting: each target becomes
-- the code after a block that the jumps to it leave.
/--
info: procedure overlapping(p: bool, q: bool)
  opaque
{
  var r: int;
  r := 0;
  {
    {
      if p
        then {
          exit $goto_join_2
        }
        else {
          r := r + 1;
          if q
            then {
              exit $goto_join_1
            }
            else {
              r := r + 10;
              exit $goto_join_2
            }
        }
    }$goto_join_2;
    r := r + 100
  }$goto_join_1;
  assert r >= 0
};
-/
#guard_msgs in
#eval runPassForIdiomaticity Strata.Laurel.restructureGotosPass <|
#strata
program Laurel;
procedure overlapping(p: bool, q: bool)
  opaque
{
  var r: int := 0;
  { if (p) then { goto c }; r := r + 1 } a;
  { if (q) then { goto d }; r := r + 10 } b;
  { r := r + 100 } c;
  { assert r >= 0 } d
};
#end

-- A loop entered by falling into `head` and closed by a jump back to it from a
-- block nested in a later sibling: `head` becomes the loop's block.
/--
info: procedure closedFromNested()
  opaque
{
  var i: int;
  i := 0;
  {
    {
      while(true)
        invariant 0 <= i {
        i := i + 1;
        if i < 3
          then {
            exit $goto_start_2
          }
          else {
            exit $goto_join_1
          }
      }$goto_start_2
    }head
  }$goto_join_1;
  assert i >= 3
};
-/
#guard_msgs in
#eval runPassForIdiomaticity Strata.Laurel.restructureGotosPass <|
#strata
program Laurel;
procedure closedFromNested()
  opaque
{
  var i: int := 0;
  { i := i + 1 } head
    invariant 0 <= i;
  {
    { if (i < 3) then { goto head } } inner
  } tail;
  assert i >= 3
};
#end
