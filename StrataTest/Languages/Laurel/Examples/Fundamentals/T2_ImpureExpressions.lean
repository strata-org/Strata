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
//^^^^^^^^^^^^^^ error: assertion does not hold
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
//^^^^^^^^^ error: assertion does not hold
}

procedure blockWithTwoAssignmentsInExpression() {
  var x: int := 0;
  var y: int := 0;
  var z: int := { x := 1; y := 2; };
  assert x == 1;
  assert y == 2;
  assert z == 2;
}

procedure nestedImpureStatementsAndOpaque()
  ensures true
{
  var y: int := 0;
  var x: int := y;
  var z: int := y := y + 1;;
  assert x == y;
//^^^^^^^^^^^^^^ error: assertion does not hold
  assert z == y;
}

// An imperative procedure call in expression position is lifted before the
// surrounding expression is evaluated.
procedure imperativeProc(x: int) returns (r: int)
   // ensures clause required because Core does not support transparent proceduces yet
  ensures r == x + 1
{
  r := x + 1;
  r
}

procedure imperativeCallInExpressionPosition() {
  var x: int := 0;
  // imperativeProc(x) is lifted out; its argument is evaluated before the call,
  // so the result is 1 (imperativeProc(0)), and x is still 0 afterwards.
  var y: int := imperativeProc(x) + x;
  assert y == 1;
  assert x == 0;
}

// An imperative call inside a conditional expression is also lifted.
procedure imperativeCallInConditionalExpression(b: bool) {
  var counter: int := 0;
  // The imperative call in the then-branch is lifted out of the expression.
  var result: int := (if (b) { imperativeProc(counter) } else { 0 }) + counter;
  if (b) {
    assert result == 1;
  } else {
    assert result == 0;
  }
}
"

#guard_msgs (error, drop all) in
#eval! testInputWithOffset "NestedImpureStatements" program 14 processLaurelFile


end Laurel
