/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import StrataTest.Util.TestDiagnostics
import StrataTest.Languages.Laurel.TestExamples

open StrataTest.Util
open Strata

namespace Strata.Laurel

def program: String := r"
procedure nestedImpureStatements() {
  var y: int := 0;
  var x: int := y;
  var z: int := y := y + 1;;
    assert x == y;
//  ^^^^^^^^^^^^^^ error: assertion does not hold
  assert z == y;
}

procedure multipleAssignments() {
  var x: int := 1;
  var y: int := x + ((x := 2;) + x) + (x := 3;);
  assert y == 8;
}

procedure conditionalAssignmentInExpression(x: int) {
  var y: int := 0;
  var z: int := (if (x > 0) { y := y + 1; } else { 0 }) + y;
  if (x > 0) {
    assert y == 1;
    assert z == 2;
  } else {
    assert z == 0;
    assert y == 0;
  }
}

procedure anotherConditionAssignmentInExpression(c: bool) {
  var b: bool := c;
  var z: bool := (if (b) { b := false; } else (b := true;)) || b;
    assert z;
//  ^^^^^^^^^ error: assertion could not be proved
}

procedure blockWithTwoAssignmentsInExpression() {
  var x: int := 0;
  var y: int := 0;
  var z: int := { x := 1; y := 2; };
  assert x == 1;
  assert y == 2;
  assert z == 2;
}
"

#guard_msgs (error, drop all) in
#eval! testInputWithOffset "NestedImpureStatements" program 14 processLaurelFile


end Laurel
