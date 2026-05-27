/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import StrataTest.Util.TestLaurel

open StrataTest.Util
open Strata

/-- info: 7:2-14  error: assertion does not hold
14:2-30  error: precondition does not hold
27:2-44  error: assertion does not hold
42:2-39  error: precondition does not hold
56:2-43  error: assertion does not hold -/
#guard_msgs in
#eval testLaurelExpect <|
#strata_expect
program Laurel;
procedure hasRequires(x: int) returns (r: int)
  requires x > 2
  opaque
{
  assert x > 0;
  assert x > 3;
  x + 1
};

procedure caller()
  opaque
{
  var x: int := hasRequires(1);
  var y: int := hasRequires(3)
};

function aFunctionWithPrecondition(x: int): int
  requires x == 10
{
  x
};

procedure aFunctionWithPreconditionCaller()
  opaque
{
  var x: int := aFunctionWithPrecondition(0)
};

procedure multipleRequires(x: int, y: int) returns (r: int)
  requires x > 0
  requires y > 0
  opaque
{
  x + y
};

procedure multipleRequiresCaller()
  opaque
{
  var a: int := multipleRequires(1, 2);
  var b: int := multipleRequires(-1, 2)
};

function funcMultipleRequires(x: int, y: int): int
  requires x > 0
  requires y > 0
{
  x + y
};

procedure funcMultipleRequiresCaller()
  opaque
{
  var a: int := funcMultipleRequires(1, 2);
  var b: int := funcMultipleRequires(1, -1)
};
#end
