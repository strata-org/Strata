/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import StrataTest.Util.TestDiagnostics
import StrataTest.Languages.Laurel.TestExamples

open StrataTest.Util

namespace Strata
namespace Laurel

/-
End-to-end verification of Java-style `++` and `--` operators.

Covers:
* Bare statement form (`x++;`, `--x`).
* Prefix in expression position (yields the new value).
* Postfix in expression position (yields the old value, like Java).
* Mixed prefix and postfix in a single expression.
* Postfix decrement.
* Use as a `for`-loop step.
* Increment as an argument to a (pure) function call.
* Increment in an if-then-else condition.
* Increment on the right-hand side of a short-circuit `&&` (with both
  evaluated and skipped paths).
* Mixing prefix and postfix forms with arithmetic operators.
* Intentional failing asserts to confirm error reporting still flows.

Increment of a composite-type field is verified separately in
`T23b_IncrDecrField.lean` (the composite type triggers heap
parameterization which interacts poorly with counterexample search
for the failing tests in this file).
-/
def program := r"
procedure stmtForm()
  opaque
{
  var x: int := 5;
  x++;
  assert x == 6;
  x--;
  assert x == 5;
  ++x;
  assert x == 6;
  --x;
  assert x == 5
};

procedure preIncrYieldsNew()
  opaque
{
  var x: int := 0;
  var y: int := ++x;
  assert x == 1;
  assert y == 1
};

procedure postIncrYieldsOld()
  opaque
{
  var x: int := 0;
  var y: int := x++;
  assert x == 1;
  assert y == 0
};

procedure repeatedPostIncr()
  opaque
{
  var x: int := 0;
  // Java semantics: (x++)+(x++) reads 0 then 1, x ends at 2, sum = 1.
  var y: int := x++ + x++;
  assert x == 2;
  assert y == 1
};

procedure repeatedPreIncr()
  opaque
{
  var x: int := 0;
  // Java semantics: (++x)+(++x) writes 1 then 2, x ends at 2, sum = 3.
  var y: int := ++x + ++x;
  assert x == 2;
  assert y == 3
};

procedure mixedPrePostIncr()
  opaque
{
  var x: int := 10;
  // (x++) yields 10 (old), (++x) yields 12 (new), so sum = 22.
  var y: int := x++ + ++x;
  assert x == 12;
  assert y == 22
};

procedure preDecrYieldsNew()
  opaque
{
  var x: int := 5;
  var y: int := --x;
  assert x == 4;
  assert y == 4
};

procedure postDecrYieldsOld()
  opaque
{
  var x: int := 5;
  var y: int := x--;
  assert x == 4;
  assert y == 5
};

procedure forLoopStep()
  opaque
{
  var sum: int := 0;
  var i: int := 0;
  for (i := 0; i < 3; i++)
  invariant 0 <= i
  invariant i <= 3
  invariant sum == i
  {
    sum := sum + 1
  };
  assert sum == 3
};

// --- More complex scenarios -------------------------------------------------

function double(n: int): int { 2 * n };

procedure incrementAsFunctionArgument()
  opaque
{
  var x: int := 3;
  // double(x++) reads the OLD x (3), so r = double(3) = 6, and x = 4 after.
  var r: int := double(x++);
  assert x == 4;
  assert r == 6
};

procedure preIncrementAsFunctionArgument()
  opaque
{
  var x: int := 3;
  // double(++x) reads the NEW x (4), so r = double(4) = 8, and x = 4 after.
  var r: int := double(++x);
  assert x == 4;
  assert r == 8
};

procedure postIncrementInIfCondition()
  opaque
{
  var x: int := 0;
  var hitThen: bool := false;
  var hitElse: bool := false;
  // Postfix: x++ yields the OLD value (0), so condition `0 > 0` is false.
  // The else branch runs, but x has already been incremented to 1.
  if x++ > 0 then {
    hitThen := true
  } else {
    hitElse := true
  };
  assert hitElse;
  assert !hitThen;
  assert x == 1
};

procedure preIncrementInIfCondition()
  opaque
{
  var x: int := 0;
  var hitThen: bool := false;
  var hitElse: bool := false;
  // Prefix: ++x yields the NEW value (1), so condition `1 > 0` is true.
  if ++x > 0 then {
    hitThen := true
  } else {
    hitElse := true
  };
  assert hitThen;
  assert !hitElse;
  assert x == 1
};

procedure incrementInShortCircuitTaken()
  opaque
{
  var y: int := 10;
  // First operand `y > 0` is true → RHS is evaluated.
  // y++ yields 10 (old y); 10 > 5 is true; y becomes 11.
  var b: bool := y > 0 && y++ > 5;
  assert b;
  assert y == 11
};

procedure incrementInShortCircuitSkipped()
  opaque
{
  var x: int := 0;
  var y: int := 0;
  // First operand `x > 0` is false → short-circuit → y++ NOT evaluated.
  var b: bool := x > 0 && y++ > 5;
  assert !b;
  // Crucially: y has NOT been incremented because of short-circuit semantics.
  assert y == 0
};

procedure mixedIncrInArithmetic()
  opaque
{
  var x: int := 1;
  // `x++ * 2 + ++x - x--` parses as `((x++ * 2) + ++x) - x--`.
  // Lift evaluates right-to-left:
  //   x-- → snapshot $x_0 (= 1), x := 0;     (yielded value: $x_0 = 1)
  // wait, let me re-trace... actually with our pass, the values seen are:
  //   x    starts at 1
  //   x++  yields 1, x := 2
  //   ++x  yields 3 (NEW), x := 3
  //   x--  yields 3 (old), x := 2
  // Final x = 2; r = 1*2 + 3 - 3 = 2.
  var r: int := x++ * 2 + ++x - x--;
  assert x == 2;
  assert r == 2
};

procedure failingAssertOnPostIncr()
  opaque
{
  var x: int := 0;
  var y: int := x++;
  assert y == 1
//^^^^^^^^^^^^^ error: assertion does not hold
};

procedure failingAssertOnVarAfterPostIncr()
  opaque
{
  // After `x++`, x is 1. Asserting `x == 0` should fail — this guards the
  // `x` side of postfix semantics: the variable IS updated even though the
  // expression yields the old value.
  var x: int := 0;
  var y: int := x++;
  assert x == 0
//^^^^^^^^^^^^^ error: assertion does not hold
};

procedure failingAssertOnSkippedShortCircuit()
  opaque
{
  // y++ is on the right-hand side of `&&` whose left operand is false, so
  // short-circuit semantics skip y++ entirely and y stays at 0. Asserting
  // `y == 1` confirms the skip is real (the assertion fails).
  var x: int := 0;
  var y: int := 0;
  var b: bool := x > 0 && y++ > 5;
  assert y == 1
//^^^^^^^^^^^^^ error: assertion does not hold
};
"

#guard_msgs(drop info, error) in
#eval testInputWithOffset "IncrDecr" program 14 processLaurelFile

end Laurel

