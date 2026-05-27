/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import StrataTest.Util.TestDiagnostics
import StrataTest.Languages.Laurel.TestExamples

open StrataTest.Util
open Strata

namespace Strata.Laurel

def program := r"
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
//^^^^^^^^^^^^^^^^^^^^^^^^^^ error: assertion does not hold

  assert guardInFunction(1) == 1;
  assert guardInFunction(1) == 2
//^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ error: assertion does not hold
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
//^^^^^^^^^^^^ error: assertion does not hold
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
//^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ error: assertion does not hold
  return b
};
"

#guard_msgs (error, drop all) in
#eval! testInputWithOffset "ControlFlow" program 14 processLaurelFile
