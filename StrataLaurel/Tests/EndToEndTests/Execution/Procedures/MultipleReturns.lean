/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
import StrataLaurel.Tests.Util.TestLaurel

open StrataTest.Util
open Strata

-- No interpreters: `multipleReturns` has no body, so the Laurel interpreter refuses the call, and Core says "condition did not reduce to bool".
#eval testLaurelExecution { skipCoreInterpreter := true, skipLaurelInterpreter := true } <|
#strata
program Laurel;
procedure multipleReturns() returns (x: int, y: int, z: int)
  opaque
  ensures x == 1 && y == 2 && z == 3;

procedure caller()
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

-- A variable assigned from two results of one call is refused as an ill-formed call.
#eval testLaurelExecution { skipCoreInterpreter := true, skipLaurelInterpreter := true } <|
#strata
program Laurel;
procedure multipleReturns() returns (x: int, y: int, z: int)
  opaque
  ensures x == 1 && y == 2 && z == 3;

procedure repeatedAssignTarget()
  opaque
{
  var x: int;
  assign x, x, x := multipleReturns();
//^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ error: the call to multipleReturns passes the variable x for more than one out parameter; the results of a call must be distinct variables
  assert false
};
#end
