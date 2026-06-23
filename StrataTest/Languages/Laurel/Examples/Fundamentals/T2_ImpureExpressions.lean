/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import StrataTest.Util.TestLaurel

open StrataTest.Util
open Strata

#guard_msgs (drop info) in
#eval testLaurel <|
#strata
program Laurel;
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

procedure add(x: int, y: int): int
{
  return x + y
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
  assert y == 12

  // The next statement is not translated correctly.
  // I think it's a bug in the handling of StaticCall
  // Where a reference is substituted when it should not be
  // var z: int := addProc({x := 1; x}, {x := x + 10; x}) + (x := 3);
  // assert z == 15
};

procedure assertInsideConditionalExpression(a: int): int
  return if a > 2
    then 4
    else {
      assert a <= 2;
      assert a < 2;
//    ^^^^^^^^^^^^ error: assertion does not hold
      5
    };

procedure assertInBlockExpr()
opaque {
  var x: int := 0;
  var y: int := { assert x == 0; x := 1; x };
  assert y == 1
};

procedure transparentProc(x: int) returns (r: int)
{
  return x + 1
};

procedure assignmentInExpressionAfterProcCall()
opaque {
  var x: int := 0;
  var y: int := transparentProc(x) + (x := 2);
  assert y == 3
};

procedure liftInsideAssignmentInExpression()
opaque {
  var x: int := 0;
  var y: int := ((x := 1) + transparentProc(x));
  assert y == 3
};

procedure hasMultipleOutputs() returns (x: int, y: int) opaque {
  x := 1;
  y := 2
};

procedure liftWithMultipleOutputs() opaque {
  var x: int := { assign var y: int, var z: int := hasMultipleOutputs() ; y + z }
};

// Regression test for a fresh-name collision in LiftImperativeExpressionsPass.
//
// `nameCollisionHelper` has no contract, so ContractPass leaves its calls in
// place; the lift pass is what hoists them out of expression position via its
// `asLifted` helper. In the first statement the call sits in expression position
// (the `+ 1` keeps it from being a direct assignment RHS) and its argument is a
// conditional containing another such call. Lifting that argument allocates a
// fresh `$cndtn_` variable *inside* `asLifted`, and that declaration escapes into
// the surrounding scope. Previously `asLifted` saved and restored the entire lift
// state, rolling the fresh-name counter back even though the name had already
// escaped. The conditional expression in the second statement then reused the
// rolled-back number, producing a duplicate `$cndtn_` definition and a
// "Duplicate definition" resolution error after the pass.
procedure nameCollisionHelper(x: int) returns (r: int)
  opaque
{
  r := x + 1;
  r
};

procedure liftedCallArgDoesNotReuseCondName(b: bool)
  opaque
{
  var y: int := nameCollisionHelper(if b then { nameCollisionHelper(0) } else { 1 }) + 1;
  var z: int := (if b then { nameCollisionHelper(5) } else { 6 }) + 1
};

#end
