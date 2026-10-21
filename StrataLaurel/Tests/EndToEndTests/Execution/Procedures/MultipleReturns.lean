/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
import StrataLaurel.Tests.Util.TestLaurel

open StrataTest.Util
open Strata

#eval testLaurelExecution {} <|
#strata
program Laurel;
procedure multipleReturns() returns (x: int, y: int, z: int)
  opaque
  ensures x == 1 && y == 2 && z == 3
{
  x := 1;
  y := 2;
  z := 3
};

procedure caller()
  entry
  opaque
{
  var y: int;
  assign var x: int, y, var z: int := multipleReturns();
  assert x == 1;
  assert y == 2;
  assert z == 3;

  var a: int;
  assign a, var b: int, var c: int := multipleReturns();
  assert a == 1;
  assert b == 2;
  assert c == 3;

  var m: int := 3;
  var n: int;
  n := 4
};
#end
