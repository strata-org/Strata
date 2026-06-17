/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import StrataTest.Util.TestLaurel

open StrataTest.Util
open Strata

#guard_msgs (drop info) in
#eval testLaurel <|
#strata
program Laurel;

procedure letExpressionsInTransparent() returns (r: int) {
  var x: int := 0;
  var y: int := x + 1;
  var z: int := y + 1;
  return z
};

procedure callLetExpressionsInTransparent() opaque {
  var x: int := letExpressionsInTransparent();
  assert x == 2
};

procedure assertAndAssumeInTransparent(a: int) returns (r: int)
{
  assert 2 == 3;
//^^^^^^^^^^^^^ error: assertion does not hold
  assume true;
  return a
};

procedure returnAtEnd(x: int) returns (r: int) {
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

procedure elseWithCall(): int
{
  return if true then 3 else returnAtEnd(3)
};

procedure testFunctions()
  opaque
{
  assert returnAtEnd(1) == 1;
  assert returnAtEnd(1) == 2;
//^^^^^^^^^^^^^^^^^^^^^^^^^^ error: assertion could not be proved

  assert guardInFunction(1) == 1;
  assert guardInFunction(1) == 2
//^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ error: assertion could not be proved
};

procedure guardInFunction(x: int) returns (r: int)
{
  if x > 0 then {
    if x == 1 then {
      return 1
    } else {
      return 2
    }
  };

  return 3
};

procedure guards(a: int) returns (r: int)
{
  if a > 2 then {
      if a > 3 then {
          return 4
      };
      return 6
  };
  assert a <= 2;
  assert a < 2;
//^^^^^^^^^^^^ error: assertion does not hold
  return 5
};

//
// procedure guards(a: int) returns (r: int)
// {
//   var b: int := a + 2;
//   if b > 2 then {
//       var c: int := b + 3;
//       if c > 3 then {
//           return c + 4
//       };
//       //var d: int := c + 5;
//       return d + 6
//   };
//   //var e: int := b + 1;
//   assert e <= 3;
//   assert e < 3;
//   return e
// };

procedure dag(a: int) returns (r: int)
  opaque
{
  var b: int;

  if a > 0 then {
    b := 1
  };
  assert if a > 0 then { b == 1 } else { true };
  assert if a > 0 then { b == 2 } else { true };
//^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ error: assertion does not hold
  return b
};

// Valueless early return (issue #1353): a bare `return` parses to `.Return none`.
// Must verify cleanly — no value, used as an early exit.
procedure valuelessEarlyReturn(b: bool)
  opaque
{
  if b then {
    return
  };
  assert true
};
#end
