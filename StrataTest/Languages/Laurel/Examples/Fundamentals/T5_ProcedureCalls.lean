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
procedure fooReassign(): int {
  var x: int := 0;
  x := x + 1;
  assert x == 1;
  x := x + 1;
  x
}

procedure fooSingleAssign(): int {
  var x: int := 0;
  var x2: int := x + 1;
  var x3: int := x2 + 1;
  x3
}

procedure fooProof() {
  var x: int := fooReassign();
  var y: int := fooSingleAssign();
// The following assertions fails while it should succeed,
// because Core does not yet support transparent procedures
//  assert x == y;
}

function aFunction(x: int): int
{
  x
}

procedure aFunctionCaller() {
  var x: int := aFunction(3);
  assert x == 3;
}
"

/--
error: Parse errors:
  39:0: Syntax error: unrecognized syntax or unexpected token
-/
#guard_msgs (drop info, error) in
#eval testInputWithOffset "ProcedureCalls" program 14 processLaurelFile
