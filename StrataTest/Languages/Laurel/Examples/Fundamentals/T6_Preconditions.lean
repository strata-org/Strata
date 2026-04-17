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
procedure hasRequires(x: int) returns (r: int)
  requires x > 2
// Call elimination reports precondition errors at the call site,
// not at the requires clause definition.
//
  opaque
{
  assert x > 0;
  assert x > 3;
//^^^^^^^^^^^^ error: assertion does not hold
  x + 1
};

procedure caller()
  opaque
{
  var x: int := hasRequires(1);
//^^^^^^^^^^^^^^^^^^^^^^^^^^^^ error: precondition does not hold
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
//^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ error: assertion does not hold
// Error ranges are too wide because Core does not use expression locations
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
//^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ error: precondition does not hold
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
//^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ error: assertion does not hold
};
"

#guard_msgs (drop info, error) in
#eval testInputWithOffset "Preconditions" program 14 processLaurelFile
