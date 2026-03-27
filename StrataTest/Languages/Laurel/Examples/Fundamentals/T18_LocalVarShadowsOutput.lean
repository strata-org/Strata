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
// Issue #567: local variable with the same name as an output parameter
// shadows it, causing the return value to be lost.

// Case 1: expression initializer (auto-generated `result` name)
procedure double(x: int) returns (result: int)
  ensures result == x + x
{
  var result: int := x + x;
  return result
};

procedure testDouble() {
  var y: int := double(3);
  assert y == 6
};

// Case 2: expression initializer (user-named output param)
procedure triple(x: int) returns (r: int)
  ensures r == x + x + x
{
  var r: int := x + x + x;
  return r
};

procedure testTriple() {
  var y: int := triple(2);
  assert y == 6
};

// Case 3: no initializer (havoc path)
procedure nondetPositive() returns (r: int)
  ensures r > 0
{
  var r: int;
  assume r > 0;
  return r
};

// Case 4: procedure call as initializer
procedure helper(x: int) returns (out: int)
  ensures out == x * 2
{
  out := x * 2
};

procedure callInit(x: int) returns (out: int)
  ensures out == x * 2
{
  var out: int := helper(x);
  return out
};

procedure testCallInit() {
  var y: int := callInit(5);
  assert y == 10
};

// Case 5: output param used as scratch, then overwritten by return
procedure scratch(x: int) returns (r: int)
  ensures r == x
{
  var r: int := 99;
  r := x;
  return r
};

procedure testScratch() {
  var y: int := scratch(7);
  assert y == 7
};
"

#guard_msgs (drop info, error) in
#eval testInputWithOffset "LocalVarShadowsOutput" program 15 processLaurelFile

end Laurel
