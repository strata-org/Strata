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
procedure nestedImpureStatements()
  opaque
{
  var y: int := 0;
  var x: int := y;
  var z: int := y := y + 1;
  assert x == y;
//^^^^^^^^^^^^^ error: assertion does not hold
  assert z == y
};

procedure multipleAssignments()
  opaque
{
  var x: int := 1;
  var y: int := x + ((x := 2) + x) + (x := 3);
  assert y == 8
};

procedure conditionalAssignmentInExpression(x: int)
  opaque
{
  var y: int := 0;
  var z: int := (if x > 0 then { y := y + 1 } else { 0 }) + y;
  if x > 0 then {
    assert y == 1;
    assert z == 2
  } else {
    assert z == 0;
    assert y == 0
  }
};

procedure anotherConditionAssignmentInExpression(c: bool)
  opaque
{
  var b: bool := c;
  var z: bool := (if b then { b := false } else (b := true)) || b;
  assert z
//^^^^^^^^ error: assertion does not hold
};

procedure blockWithTwoAssignmentsInExpression()
  opaque
{
  var x: int := 0;
  var y: int := 0;
  var z: int := { x := 1; y := 2 };
  assert x == 1;
  assert y == 2;
  assert z == 2
};

procedure nestedImpureStatementsAndOpaque()
  opaque
{
  var y: int := 0;
  var x: int := y;
  var z: int := y := y + 1;
  assert x == y;
//^^^^^^^^^^^^^ error: assertion does not hold
  assert z == y
};

// An imperative procedure call in expression position is lifted before the
// surrounding expression is evaluated.
procedure imperativeProc(x: int) returns (r: int)
   // ensures clause required because Core's symbolic verification does not support transparent proceduces yet
  opaque
  ensures r == x + 1
{
  r := x + 1;
  r
};

procedure imperativeCallInExpressionPosition()
  opaque
{
  var x: int := 0;
  // imperativeProc(x) is lifted out; its argument is evaluated before the call,
  // so the result is 1 (imperativeProc(0)), and x is still 0 afterwards.
  var y: int := imperativeProc(x) + x;
  assert y == 1;
  assert x == 0
};

// An imperative call inside a conditional expression is also lifted.
procedure imperativeCallInConditionalExpression(b: bool)
  opaque
{
  var counter: int := 0;
  // The imperative call in the then-branch is lifted out of the expression.
  var result: int := (if b then { imperativeProc(counter) } else { 0 }) + counter;
  if b then {
    assert result == 1
  } else {
    assert result == 0
  }
};

function add(x: int, y: int): int
{
  x + y
};

procedure repeatedBlockExpressions()
  opaque
{
  var x: int := 2;
  var y: int := { x := 1; x } + { x := x + 10; x };
  var z: int := add({ x := 1; x }, { x := x + 10; x });
  assert y == 1 + 11;
  assert z == 1 + 11
};

procedure addProc(a: int, b: int) returns (r: int)
  opaque
  ensures r == a + b {
  return a + b
};

procedure addProcCaller(): int
  opaque
{
  var x: int := 0;
  var y: int := addProc({x := 1; x}, {x := x + 10; x});
  assert y == 11

  // The next statement is not translated correctly.
  // I think it's a bug in the handling of StaticCall
  // Where a reference is substituted when it should not be
  // var z: int := addProc({x := 1; x}, {x := x + 10; x}) + (x := 3);
  // assert z == 14
};
"

#guard_msgs (error, drop all) in
#eval! testInputWithOffset "NestedImpureStatements" program 14 processLaurelFile


end Laurel
