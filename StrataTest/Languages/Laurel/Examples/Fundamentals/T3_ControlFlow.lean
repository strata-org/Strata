/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import StrataTest.Util.TestLaurel

open StrataTest.Util
open Strata

/-- info: 34:2-28  error: assertion does not hold
37:2-32  error: assertion does not hold
54:2-14  error: assertion does not hold
67:2-47  error: assertion does not hold -/
#guard_msgs in
#eval testLaurelExpect <|
#strata_expect
program Laurel;
function returnAtEnd(x: int) returns (r: int) {
  if x > 0 then {
    if x == 1 then {
      return 1
    } else {
      return 2
    }
  } else {
    return 3
  }
};

function elseWithCall(): int {
  if true then 3 else returnAtEnd(3)
};

function guardInFunction(x: int) returns (r: int) {
  if x > 0 then {
    if x == 1 then {
      return 1
    } else {
      return 2
    }
  };

  return 3
};

procedure testFunctions()
  opaque
{
  assert returnAtEnd(1) == 1;
  assert returnAtEnd(1) == 2;

  assert guardInFunction(1) == 1;
  assert guardInFunction(1) == 2
};

procedure guards(a: int) returns (r: int)
  opaque
{
  var b: int := a + 2;
  if b > 2 then {
      var c: int := b + 3;
      if c > 3 then {
          return c + 4
      };
      var d: int := c + 5;
      return d + 6
  };
  var e: int := b + 1;
  assert e <= 3;
  assert e < 3;
  return e
};

procedure dag(a: int) returns (r: int)
  opaque
{
  var b: int;

  if a > 0 then {
    b := 1
  };
  assert if a > 0 then { b == 1 } else { true };
  assert if a > 0 then { b == 2 } else { true };
  return b
};
#end
