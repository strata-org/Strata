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
//         ^^^^^ error: assertion could not be proved
// Core does not seem to report precondition errors correctly.
// This should occur at the call site and with a different message
{
  assert x > 0;
  assert x > 3;
//^^^^^^^^^^^^ error: assertion could not be proved
  x + 1
};

procedure caller() {
  var x: int := hasRequires(1);
  var y: int := hasRequires(3)
};

function aFunctionWithPrecondition(x: int): int
  requires x == 10
{
  x
};

procedure aFunctionWithPreconditionCaller() {
  var x: int := aFunctionWithPrecondition(0)
//^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ error: assertion could not be proved
// Error ranges are too wide because Core does not use expression locations
};

procedure multipleRequires(x: int, y: int) returns (r: int)
  requires x > 0
  requires y > 0
{
  x + y
};

// This test fails because Core incorrectly report error locations on procedure preconditions
// procedure multipleRequiresCaller() {
//  var a: int := multipleRequires(1, 2);
//  var b: int := multipleRequires(-1, 2);
// error: assertion could not be proved
// };

function funcMultipleRequires(x: int, y: int): int
  requires x > 0
  requires y > 0
{
  x + y
};

procedure funcMultipleRequiresCaller() {
  var a: int := funcMultipleRequires(1, 2);
  var b: int := funcMultipleRequires(1, -1)
//^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ error: assertion could not be proved
};
"

#guard_msgs (drop info, error) in
#eval testInputWithOffset "Preconditions" program 14 processLaurelFile
