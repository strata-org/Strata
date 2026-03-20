/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import StrataTest.Languages.Laurel.ConcreteEval.TestHelper

/-!
# Transform Preservation Tests

Runs every string-based ConcreteEval test after the full
Laurel→Laurel lowering pipeline from LaurelToCoreTranslator.translate.

## Status
- Passing: 77 / 94 tests (output matches direct mode)
- Failing: 17 / 94 tests (output differs from direct mode)

## Known failure categories
- heapParameterization (12 tests): all tests using composite types / heap
  objects fail because the evaluator does not handle heap-parameterized
  programs (field accesses become map select/store operations).
- liftExpressionAssignments (5 tests): nested procedure calls in expression
  position are lifted into temporaries, and side-effect evaluation order
  changes break tests that depend on left-to-right argument evaluation.
-/

namespace Strata.Laurel.ConcreteEval.TransformPreservationTest

open Strata.Laurel.ConcreteEval.TestHelper
open Strata.Laurel

/-! ## Primitives -/

/-! ### Primitives Test 1: Integer literal (positive) -/
/--
info: returned: 42
-/
#guard_msgs in
#eval! do
  let prog ← parseLaurelTransformed r"
procedure main() { return 42 };
"
  IO.println (toString (runProgram prog))

/-! ### Primitives Test 2: Integer literal (negative) -/
/--
info: returned: -7
-/
#guard_msgs in
#eval! do
  let prog ← parseLaurelTransformed r"
procedure main() { return -7 };
"
  IO.println (toString (runProgram prog))

/-! ### Primitives Test 3: Integer literal (zero) -/
/--
info: returned: 0
-/
#guard_msgs in
#eval! do
  let prog ← parseLaurelTransformed r"
procedure main() { return 0 };
"
  IO.println (toString (runProgram prog))

/-! ### Primitives Test 4: Boolean true -/
/--
info: returned: 1
-/
#guard_msgs in
#eval! do
  let prog ← parseLaurelTransformed r"
procedure main() {
  if (true) { return 1 } else { return 0 }
};
"
  IO.println (toString (runProgram prog))

/-! ### Primitives Test 5: Boolean false -/
/--
info: returned: 0
-/
#guard_msgs in
#eval! do
  let prog ← parseLaurelTransformed r"
procedure main() {
  if (false) { return 1 } else { return 0 }
};
"
  IO.println (toString (runProgram prog))

/-! ### Primitives Test 6: String literal equality -/
/--
info: returned: 1
-/
#guard_msgs in
#eval! do
  let prog ← parseLaurelTransformed r#"
procedure main() {
  if ("hello" == "hello") { return 1 } else { return 0 }
};
"#
  IO.println (toString (runProgram prog))

/-! ### Primitives Test 7: Empty string equality -/
/--
info: returned: 1
-/
#guard_msgs in
#eval! do
  let prog ← parseLaurelTransformed r#"
procedure main() {
  if ("" == "") { return 1 } else { return 0 }
};
"#
  IO.println (toString (runProgram prog))

/-! ### Primitives Test 8: Void procedure -/
/--
info: returned: 0
-/
#guard_msgs in
#eval! do
  let prog ← parseLaurelTransformed r"
procedure noop() { var x: int := 1 };
procedure main() { noop(); return 0 };
"
  IO.println (toString (runProgram prog))

/-! ## Arithmetic -/

/-! ### Arithmetic Test 1: Addition -/
/--
info: returned: 7
-/
#guard_msgs in
#eval! do
  let prog ← parseLaurelTransformed r"
procedure main() { return 3 + 4 };
"
  IO.println (toString (runProgram prog))

/-! ### Arithmetic Test 2: Subtraction -/
/--
info: returned: 7
-/
#guard_msgs in
#eval! do
  let prog ← parseLaurelTransformed r"
procedure main() { return 10 - 3 };
"
  IO.println (toString (runProgram prog))

/-! ### Arithmetic Test 3: Multiplication -/
/--
info: returned: 42
-/
#guard_msgs in
#eval! do
  let prog ← parseLaurelTransformed r"
procedure main() { return 6 * 7 };
"
  IO.println (toString (runProgram prog))

/-! ### Arithmetic Test 4: Euclidean division -/
/--
info: returned: 3
-/
#guard_msgs in
#eval! do
  let prog ← parseLaurelTransformed r"
procedure main() { return 7 / 2 };
"
  IO.println (toString (runProgram prog))

/-! ### Arithmetic Test 5: Euclidean modulus -/
/--
info: returned: 1
-/
#guard_msgs in
#eval! do
  let prog ← parseLaurelTransformed r"
procedure main() { return 7 % 2 };
"
  IO.println (toString (runProgram prog))

/-! ### Arithmetic Test 6: Negation via subtraction -/
/--
info: returned: -5
-/
#guard_msgs in
#eval! do
  let prog ← parseLaurelTransformed r"
procedure main() { return 0 - 5 };
"
  IO.println (toString (runProgram prog))

/-! ### Arithmetic Test 7: Division by zero — stuck -/
/--
info: error: fuel exhausted
-/
#guard_msgs in
#eval! do
  let prog ← parseLaurelTransformed r"
procedure main() { return 1 / 0 };
"
  IO.println (toString (runProgram prog))

/-! ### Arithmetic Test 8: Modulus by zero — stuck -/
/--
info: error: fuel exhausted
-/
#guard_msgs in
#eval! do
  let prog ← parseLaurelTransformed r"
procedure main() { return 1 % 0 };
"
  IO.println (toString (runProgram prog))

/-! ### Arithmetic Test 9: Large integers -/
/--
info: returned: 1000000000000000000
-/
#guard_msgs in
#eval! do
  let prog ← parseLaurelTransformed r"
procedure main() { return 1000000000 * 1000000000 };
"
  IO.println (toString (runProgram prog))

/-! ### Arithmetic Test 10: Compound expression -/
/--
info: returned: 15
-/
#guard_msgs in
#eval! do
  let prog ← parseLaurelTransformed r"
procedure main() { return (2 + 3) * (4 - 1) };
"
  IO.println (toString (runProgram prog))

/-! ### Arithmetic Test 11: Negative arithmetic -/
/--
info: returned: -7
-/
#guard_msgs in
#eval! do
  let prog ← parseLaurelTransformed r"
procedure main() { return (-3) + (-4) };
"
  IO.println (toString (runProgram prog))

/-! ### Arithmetic Test 12: DivT -/
/--
info: returned: 3
-/
#guard_msgs in
#eval! do
  let prog ← parseLaurelTransformed r"
procedure main() { return 7 /t 2 };
"
  IO.println (toString (runProgram prog))

/-! ### Arithmetic Test 13: ModT -/
/--
info: returned: 1
-/
#guard_msgs in
#eval! do
  let prog ← parseLaurelTransformed r"
procedure main() { return 7 %t 2 };
"
  IO.println (toString (runProgram prog))

/-! ### Arithmetic Test 14: DivT with negative dividend -/
/--
info: returned: -3
-/
#guard_msgs in
#eval! do
  let prog ← parseLaurelTransformed r"
procedure main() { return (-7) /t 2 };
"
  IO.println (toString (runProgram prog))

/-! ### Arithmetic Test 15: ModT with negative dividend -/
/--
info: returned: -1
-/
#guard_msgs in
#eval! do
  let prog ← parseLaurelTransformed r"
procedure main() { return (-7) %t 2 };
"
  IO.println (toString (runProgram prog))

/-! ### Arithmetic Test 16: DivT by zero — stuck -/
/--
info: error: fuel exhausted
-/
#guard_msgs in
#eval! do
  let prog ← parseLaurelTransformed r"
procedure main() { return 7 /t 0 };
"
  IO.println (toString (runProgram prog))

/-! ### Arithmetic Test 17: ModT by zero — stuck -/
/--
info: error: fuel exhausted
-/
#guard_msgs in
#eval! do
  let prog ← parseLaurelTransformed r"
procedure main() { return 7 %t 0 };
"
  IO.println (toString (runProgram prog))

/-! ## BooleanOps -/

/-! ### BooleanOps Test 1: Comparison operators -/
/--
info: returned: 1
-/
#guard_msgs in
#eval! do
  let prog ← parseLaurelTransformed r"
procedure main() {
  var a: bool := 1 < 2;
  var b: bool := 2 <= 2;
  var c: bool := 3 > 2;
  var d: bool := 2 >= 2;
  if (a && b && c && d) { return 1 } else { return 0 }
};
"
  IO.println (toString (runProgram prog))

/-! ### BooleanOps Test 2: Eq and Neq on integers -/
/--
info: returned: 1
-/
#guard_msgs in
#eval! do
  let prog ← parseLaurelTransformed r"
procedure main() {
  if (5 == 5 && 5 != 6) { return 1 } else { return 0 }
};
"
  IO.println (toString (runProgram prog))

/-! ### BooleanOps Test 3: Eq and Neq on booleans -/
/--
info: returned: 1
-/
#guard_msgs in
#eval! do
  let prog ← parseLaurelTransformed r"
procedure main() {
  if (true == true && true != false) { return 1 } else { return 0 }
};
"
  IO.println (toString (runProgram prog))

/-! ### BooleanOps Test 4: Eq and Neq on strings -/
/--
info: returned: 1
-/
#guard_msgs in
#eval! do
  let prog ← parseLaurelTransformed r#"
procedure main() {
  if ("abc" == "abc" && "abc" != "def") { return 1 } else { return 0 }
};
"#
  IO.println (toString (runProgram prog))

/-! ### BooleanOps Test 5: Not operator -/
/--
info: returned: 1
-/
#guard_msgs in
#eval! do
  let prog ← parseLaurelTransformed r"
procedure main() {
  if (!false && !(!true)) { return 1 } else { return 0 }
};
"
  IO.println (toString (runProgram prog))

/-! ### BooleanOps Test 6: String concatenation -/
/--
info: returned: 1
-/
#guard_msgs in
#eval! do
  let prog ← parseLaurelTransformed r#"
procedure main() {
  if ("ab" ++ "cd" == "abcd") { return 1 } else { return 0 }
};
"#
  IO.println (toString (runProgram prog))

/-! ### BooleanOps Test 7: Short-circuit And — false && side-effect -/
/--
info: returned: 0
-/
#guard_msgs in
#eval! do
  let prog ← parseLaurelTransformed r"
procedure main() {
  var x: int := 0;
  var b: bool := false && {x := 1; true};
  return x
};
"
  IO.println (toString (runProgram prog))

/-! ### BooleanOps Test 8: Short-circuit And — true && side-effect -/
/--
info: returned: 1
-/
#guard_msgs in
#eval! do
  let prog ← parseLaurelTransformed r"
procedure main() {
  var x: int := 0;
  var b: bool := true && {x := 1; true};
  return x
};
"
  IO.println (toString (runProgram prog))

/-! ### BooleanOps Test 9: Nested short-circuit And -/
/--
info: returned: 0
-/
#guard_msgs in
#eval! do
  let prog ← parseLaurelTransformed r"
procedure main() {
  var x: int := 0;
  var b: bool := false && (true && {x := 1; true});
  return x
};
"
  IO.println (toString (runProgram prog))

/-! ### BooleanOps Test 10: Short-circuit Or — true || side-effect -/
/--
info: returned: 0
-/
#guard_msgs in
#eval! do
  let prog ← parseLaurelTransformed r"
procedure main() {
  var x: int := 0;
  var b: bool := true || {x := 1; false};
  return x
};
"
  IO.println (toString (runProgram prog))

/-! ### BooleanOps Test 11: Short-circuit Or — false || side-effect -/
/--
info: returned: 1
-/
#guard_msgs in
#eval! do
  let prog ← parseLaurelTransformed r"
procedure main() {
  var x: int := 0;
  var b: bool := false || {x := 1; true};
  return x
};
"
  IO.println (toString (runProgram prog))

/-! ### BooleanOps Test 12: Nested short-circuit Or -/
/--
info: returned: 0
-/
#guard_msgs in
#eval! do
  let prog ← parseLaurelTransformed r"
procedure main() {
  var x: int := 0;
  var b: bool := true || (false || {x := 1; true});
  return x
};
"
  IO.println (toString (runProgram prog))

/-! ### BooleanOps Test 13: Short-circuit Implies — false ==> side-effect -/
/--
info: returned: 0
-/
#guard_msgs in
#eval! do
  let prog ← parseLaurelTransformed r"
procedure main() {
  var x: int := 0;
  var b: bool := false ==> {x := 1; false};
  return x
};
"
  IO.println (toString (runProgram prog))

/-! ### BooleanOps Test 14: Short-circuit Implies — true ==> side-effect -/
/--
info: returned: 1
-/
#guard_msgs in
#eval! do
  let prog ← parseLaurelTransformed r"
procedure main() {
  var x: int := 0;
  var b: bool := true ==> {x := 1; true};
  return x
};
"
  IO.println (toString (runProgram prog))

/-! ### BooleanOps Test 15: Mixed short-circuit — FAILS after transforms
liftExpressionAssignments changes nested short-circuit with side effects.
The lifted code introduces temporary variables that break the evaluator.
TODO: Extend evaluator to handle lifted expression assignments.
-/
/--
info: error: fuel exhausted
-/
#guard_msgs in
#eval! do
  let prog ← parseLaurelTransformed r"
procedure main() {
  var x: int := 0;
  var b: bool := (true || {x := x + 1; true}) && (false || {x := x + 10; true});
  return x
};
"
  IO.println (toString (runProgram prog))

/-! ## ControlFlow -/

/-! ### ControlFlow Test 1: If-then-else, true branch -/
/--
info: returned: 1
-/
#guard_msgs in
#eval! do
  let prog ← parseLaurelTransformed r"
procedure main() {
  if (true) { return 1 } else { return 2 }
};
"
  IO.println (toString (runProgram prog))

/-! ### ControlFlow Test 2: If-then-else, false branch -/
/--
info: returned: 2
-/
#guard_msgs in
#eval! do
  let prog ← parseLaurelTransformed r"
procedure main() {
  if (false) { return 1 } else { return 2 }
};
"
  IO.println (toString (runProgram prog))

/-! ### ControlFlow Test 3: If-then without else (true) -/
/--
info: returned: 1
-/
#guard_msgs in
#eval! do
  let prog ← parseLaurelTransformed r"
procedure main() {
  if (true) { return 1 };
  return 0
};
"
  IO.println (toString (runProgram prog))

/-! ### ControlFlow Test 4: If-then without else (false) -/
/--
info: returned: 0
-/
#guard_msgs in
#eval! do
  let prog ← parseLaurelTransformed r"
procedure main() {
  var x: int := 0;
  if (false) { x := 1 };
  return x
};
"
  IO.println (toString (runProgram prog))

/-! ### ControlFlow Test 5: Nested if-then-else -/
/--
info: returned: 2
-/
#guard_msgs in
#eval! do
  let prog ← parseLaurelTransformed r"
procedure main() {
  var x: int := 15;
  if (x > 10) {
    if (x > 20) { return 3 } else { return 2 }
  } else { return 1 }
};
"
  IO.println (toString (runProgram prog))

/-! ### ControlFlow Test 6: While loop — zero iterations -/
/--
info: returned: 0
-/
#guard_msgs in
#eval! do
  let prog ← parseLaurelTransformed r"
procedure main() {
  var x: int := 0;
  while (false) { x := 1 };
  return x
};
"
  IO.println (toString (runProgram prog))

/-! ### ControlFlow Test 7: While loop — single iteration -/
/--
info: returned: 42
-/
#guard_msgs in
#eval! do
  let prog ← parseLaurelTransformed r"
procedure main() {
  var x: int := 0;
  var done: bool := false;
  while (!done) { x := 42; done := true };
  return x
};
"
  IO.println (toString (runProgram prog))

/-! ### ControlFlow Test 8: While loop with early return -/
/--
info: returned: 5
-/
#guard_msgs in
#eval! do
  let prog ← parseLaurelTransformed r"
procedure main() {
  var i: int := 0;
  while (i < 100) {
    if (i == 5) { return i };
    i := i + 1
  };
  return -1
};
"
  IO.println (toString (runProgram prog))

/-! ### ControlFlow Test 9: Return from nested blocks -/
/--
info: returned: 42
-/
#guard_msgs in
#eval! do
  let prog ← parseLaurelTransformed r"
procedure main() {
  var x: int := 0;
  if (true) {
    if (true) {
      return 42
    }
  };
  return 0
};
"
  IO.println (toString (runProgram prog))

/-! ### ControlFlow Test 10: Nested while loops -/
/--
info: returned: 1
-/
#guard_msgs in
#eval! do
  let prog ← parseLaurelTransformed r"
procedure main() {
  var sum: int := 0;
  var i: int := 0;
  var j: int := 0;
  while (i < 1) {
    j := 0;
    while (j < 1) {
      sum := sum + 1;
      j := j + 1
    };
    i := i + 1
  };
  return sum
};
"
  IO.println (toString (runProgram prog))

/-! ### ControlFlow Test 11: Fuel exhaustion on infinite loop -/
/--
info: error: fuel exhausted
-/
#guard_msgs in
#eval! do
  let prog ← parseLaurelTransformed r"
procedure main() {
  var x: int := 0;
  while (true) { x := x + 1 };
  return 0
};
"
  IO.println (toString (runProgram prog))

/-! ### ControlFlow Test 12: Variable re-declaration inside loop body -/
/--
info: error: fuel exhausted
-/
#guard_msgs in
#eval! do
  let prog ← parseLaurelTransformed r"
procedure main() {
  while (true) { var x: int := 0 };
  return 0
};
"
  IO.println (toString (runProgram prog))

/-! ## Variables -/

/-! ### Variables Test 1: Local var with initializer -/
/--
info: returned: 5
-/
#guard_msgs in
#eval! do
  let prog ← parseLaurelTransformed r"
procedure main() { var x: int := 5; return x };
"
  IO.println (toString (runProgram prog))

/-! ### Variables Test 2: Local var without initializer -/
/--
info: returned: 0
-/
#guard_msgs in
#eval! do
  let prog ← parseLaurelTransformed r"
procedure main() { var x: int; return 0 };
"
  IO.println (toString (runProgram prog))

/-! ### Variables Test 3: Block expression returns last value -/
/--
info: returned: 42
-/
#guard_msgs in
#eval! do
  let prog ← parseLaurelTransformed r"
procedure main() { var x: int := 0; return {x := 42; x} };
"
  IO.println (toString (runProgram prog))

/-! ### Variables Test 4: Multiple assignments -/
/--
info: returned: 3
-/
#guard_msgs in
#eval! do
  let prog ← parseLaurelTransformed r"
procedure main() { var x: int := 1; x := 2; x := 3; return x };
"
  IO.println (toString (runProgram prog))

/-! ### Variables Test 5: Variable scoping -/
/--
info: returned: 3
-/
#guard_msgs in
#eval! do
  let prog ← parseLaurelTransformed r"
procedure main() {
  var x: int := 1;
  if (true) { var y: int := 2; x := x + y };
  return x
};
"
  IO.println (toString (runProgram prog))

/-! ## Procedures -/

/-! ### Procedures Test 1: Call by value -/
/--
info: returned: 5
-/
#guard_msgs in
#eval! do
  let prog ← parseLaurelTransformed r"
procedure inc(x: int) { x := x + 1; return x };
procedure main() { var a: int := 5; var b: int := inc(a); return a };
"
  IO.println (toString (runProgram prog))

/-! ### Procedures Test 2: Shared heap — FAILS after transforms
heapParameterization changes calling convention for heap objects.
TODO: Extend evaluator to handle heap-parameterized programs.
-/
/--
info: error: fuel exhausted
-/
#guard_msgs in
#eval! do
  let prog ← parseLaurelTransformed r"
composite Point { var x: int }
procedure setX(p: Point, v: int) { p#x := v };
procedure main() {
  var p: Point := new Point; p#x := 1; setX(p, 42); return p#x
};
"
  IO.println (toString (runProgram prog))

/-! ### Procedures Test 3: Parameter reassignment — FAILS after transforms
heapParameterization changes calling convention for heap objects.
-/
/--
info: error: fuel exhausted
-/
#guard_msgs in
#eval! do
  let prog ← parseLaurelTransformed r"
composite Point { var x: int }
procedure replace(p: Point) { p := new Point; p#x := 99 };
procedure main() {
  var p: Point := new Point; p#x := 1; replace(p); return p#x
};
"
  IO.println (toString (runProgram prog))

/-! ### Procedures Test 4: Simple return value -/
/--
info: returned: 42
-/
#guard_msgs in
#eval! do
  let prog ← parseLaurelTransformed r"
procedure double(x: int) { return x * 2 };
procedure main() { return double(21) };
"
  IO.println (toString (runProgram prog))

/-! ### Procedures Test 5: Nested procedure calls — FAILS after transforms
liftExpressionAssignments lifts nested calls into temporaries that the
evaluator cannot resolve.
-/
/--
info: error: fuel exhausted
-/
#guard_msgs in
#eval! do
  let prog ← parseLaurelTransformed r"
procedure add(a: int, b: int) { return a + b };
procedure mul(a: int, b: int) { return a * b };
procedure main() { return add(mul(2, 3), mul(4, 5)) };
"
  IO.println (toString (runProgram prog))

/-! ### Procedures Test 6: Procedure modifying heap — FAILS after transforms
heapParameterization changes calling convention for heap objects.
-/
/--
info: error: fuel exhausted
-/
#guard_msgs in
#eval! do
  let prog ← parseLaurelTransformed r"
composite Counter { var n: int }
procedure increment(c: Counter) { c#n := c#n + 1 };
procedure main() {
  var c: Counter := new Counter; c#n := 0;
  increment(c); increment(c); increment(c);
  return c#n
};
"
  IO.println (toString (runProgram prog))

/-! ### Procedures Test 7: Callee cannot see caller's locals -/
/--
info: error: fuel exhausted
-/
#guard_msgs in
#eval! do
  let prog ← parseLaurelTransformed r"
procedure readX() { return x };
procedure main() { var x: int := 42; return readX() };
"
  IO.println (toString (runProgram prog))

/-! ### Procedures Test 8: Void procedure -/
/--
info: returned: 0
-/
#guard_msgs in
#eval! do
  let prog ← parseLaurelTransformed r"
procedure noop() { var x: int := 1 };
procedure main() { noop(); return 0 };
"
  IO.println (toString (runProgram prog))

/-! ## SideEffects -/

/-! ### SideEffects Test 1: Left-to-right argument evaluation — FAILS after transforms
liftExpressionAssignments lifts block expressions out of argument positions into
preceding statements. The lifting traverses arguments right-to-left, creating
snapshot variables that capture each variable's value *before* the block's
assignment. Both lifted blocks independently see the original x=0: the first
block's snapshot captures x=0 and assigns 0 to its temporary, and the second
block's snapshot also captures x=0 and assigns 0 to its temporary. The call
then receives add(0, 0) = 0. Direct mode: returned 12. After transforms: returned 0.
-/
/--
info: returned: 0
-/
#guard_msgs in
#eval! do
  let prog ← parseLaurelTransformed r"
procedure add(a: int, b: int) { return a + b };
procedure main() {
  var x: int := 0;
  return add({x := 1; x}, {x := x + 10; x})
};
"
  IO.println (toString (runProgram prog))

/-! ### SideEffects Test 2: Assignment in argument position -/
/--
info: returned: 84
-/
#guard_msgs in
#eval! do
  let prog ← parseLaurelTransformed r"
procedure id(x: int) { return x };
procedure main() {
  var a: int := 0;
  var b: int := id({a := 42; a});
  return a + b
};
"
  IO.println (toString (runProgram prog))

/-! ### SideEffects Test 3: Block expression as argument — FAILS after transforms
liftExpressionAssignments lifts the block expression, introducing a local
variable that the evaluator cannot resolve.
-/
/--
info: error: fuel exhausted
-/
#guard_msgs in
#eval! do
  let prog ← parseLaurelTransformed r"
procedure id(x: int) { return x };
procedure main() {
  return id({var t: int := 10; t + 5})
};
"
  IO.println (toString (runProgram prog))

/-! ### SideEffects Test 4: Side effects in if condition -/
/--
info: returned: 11
-/
#guard_msgs in
#eval! do
  let prog ← parseLaurelTransformed r"
procedure main() {
  var x: int := 0;
  if ({x := 1; x == 1}) { return x + 10 } else { return x }
};
"
  IO.println (toString (runProgram prog))

/-! ### SideEffects Test 5: Side effects persist across loop iterations -/
/--
info: returned: 30
-/
#guard_msgs in
#eval! do
  let prog ← parseLaurelTransformed r"
procedure id(x: int) { return x };
procedure main() {
  var x: int := 0;
  var i: int := 0;
  while (i < 3) {
    x := id({x := x + 10; x});
    i := i + 1
  };
  return x
};
"
  IO.println (toString (runProgram prog))

/-! ### SideEffects Test 6: Nested calls with side effects — FAILS after transforms
liftExpressionAssignments lifts nested calls into temporaries that the
evaluator cannot resolve.
-/
/--
info: error: fuel exhausted
-/
#guard_msgs in
#eval! do
  let prog ← parseLaurelTransformed r"
procedure add(a: int, b: int) { return a + b };
procedure main() {
  var x: int := 1;
  return add(add({x := x * 2; x}, {x := x + 3; x}), x)
};
"
  IO.println (toString (runProgram prog))

/-! ## Recursion -/

/-! ### Recursion Test 1: Factorial -/
/--
info: returned: 120
-/
#guard_msgs in
#eval! do
  let prog ← parseLaurelTransformed r"
procedure fact(n: int) {
  if (n <= 1) { return 1 } else { return n * fact(n - 1) }
};
procedure main() { return fact(5) };
"
  IO.println (toString (runProgram prog))

/-! ### Recursion Test 2: Mutual recursion — even/odd -/
/--
info: returned: 1
-/
#guard_msgs in
#eval! do
  let prog ← parseLaurelTransformed r"
procedure isEven(n: int) {
  if (n == 0) { return true } else { return isOdd(n - 1) }
};
procedure isOdd(n: int) {
  if (n == 0) { return false } else { return isEven(n - 1) }
};
procedure main() { if (isEven(4)) { return 1 } else { return 0 } };
"
  IO.println (toString (runProgram prog))

/-! ### Recursion Test 3: Deep recursion — fuel exhaustion -/
/--
info: error: fuel exhausted
-/
#guard_msgs in
#eval! do
  let prog ← parseLaurelTransformed r"
procedure deep(n: int) {
  if (n == 0) { return 0 } else { return deep(n - 1) }
};
procedure main() { return deep(100000) };
"
  IO.println (toString (runProgram prog))

/-! ### Recursion Test 4: Recursion with heap effects — FAILS after transforms
heapParameterization changes calling convention for heap objects.
-/
/--
info: error: fuel exhausted
-/
#guard_msgs in
#eval! do
  let prog ← parseLaurelTransformed r"
composite Box { var v: int }
procedure fill(b: Box, n: int) {
  if (n <= 0) { return 0 }
  else { b#v := b#v + n; return fill(b, n - 1) }
};
procedure main() {
  var b: Box := new Box; b#v := 0;
  fill(b, 5);
  return b#v
};
"
  IO.println (toString (runProgram prog))

/-! ### Recursion Test 5: Fibonacci -/
/--
info: returned: 55
-/
#guard_msgs in
#eval! do
  let prog ← parseLaurelTransformed r"
procedure fib(n: int) {
  if (n <= 1) { return n }
  else { return fib(n - 1) + fib(n - 2) }
};
procedure main() { return fib(10) };
"
  IO.println (toString (runProgram prog))

/-! ## Aliasing -/

/-! ### Aliasing Test 1: Simple aliasing — FAILS after transforms
heapParameterization changes calling convention for heap objects.
-/
/--
info: error: fuel exhausted
-/
#guard_msgs in
#eval! do
  let prog ← parseLaurelTransformed r"
composite Point { var x: int }
procedure main() {
  var p: Point := new Point; p#x := 1;
  var q: Point := p;
  q#x := 42;
  return p#x
};
"
  IO.println (toString (runProgram prog))

/-! ### Aliasing Test 2: Aliasing through procedure call — FAILS after transforms
heapParameterization changes calling convention for heap objects.
-/
/--
info: error: fuel exhausted
-/
#guard_msgs in
#eval! do
  let prog ← parseLaurelTransformed r"
composite Box { var v: int }
procedure swap(a: Box, b: Box) {
  var tmp: int := a#v; a#v := b#v; b#v := tmp
};
procedure main() {
  var b: Box := new Box; b#v := 5;
  swap(b, b);
  return b#v
};
"
  IO.println (toString (runProgram prog))

/-! ### Aliasing Test 3: Distinct objects — FAILS after transforms
heapParameterization changes calling convention for heap objects.
-/
/--
info: error: fuel exhausted
-/
#guard_msgs in
#eval! do
  let prog ← parseLaurelTransformed r"
composite Point { var x: int }
procedure main() {
  var p: Point := new Point; p#x := 1;
  var q: Point := new Point; q#x := 2;
  p#x := 99;
  return q#x
};
"
  IO.println (toString (runProgram prog))

/-! ### Aliasing Test 4: Alias survives procedure call — FAILS after transforms
heapParameterization changes calling convention for heap objects.
-/
/--
info: error: fuel exhausted
-/
#guard_msgs in
#eval! do
  let prog ← parseLaurelTransformed r"
composite Box { var v: int }
procedure setV(b: Box, x: int) { b#v := x };
procedure main() {
  var a: Box := new Box; a#v := 0;
  var b: Box := a;
  setV(a, 42);
  return b#v
};
"
  IO.println (toString (runProgram prog))

/-! ## HeapObjects -/

/-! ### HeapObjects Test 1: New object allocation — FAILS after transforms
heapParameterization changes calling convention for heap objects.
-/
/--
info: error: fuel exhausted
-/
#guard_msgs in
#eval! do
  let prog ← parseLaurelTransformed r"
composite Point { var x: int }
procedure main() { var p: Point := new Point; return 0 };
"
  IO.println (toString (runProgram prog))

/-! ### HeapObjects Test 2: Field write and read — FAILS after transforms
heapParameterization changes calling convention for heap objects.
-/
/--
info: error: fuel exhausted
-/
#guard_msgs in
#eval! do
  let prog ← parseLaurelTransformed r"
composite Point { var x: int }
procedure main() { var p: Point := new Point; p#x := 42; return p#x };
"
  IO.println (toString (runProgram prog))

/-! ### HeapObjects Test 3: Multiple fields — FAILS after transforms
heapParameterization changes calling convention for heap objects.
-/
/--
info: error: fuel exhausted
-/
#guard_msgs in
#eval! do
  let prog ← parseLaurelTransformed r"
composite Point { var x: int  var y: int }
procedure main() {
  var p: Point := new Point; p#x := 1; p#y := 2;
  return p#x + p#y
};
"
  IO.println (toString (runProgram prog))

/-! ### HeapObjects Test 4: Multiple objects — FAILS after transforms
heapParameterization changes calling convention for heap objects.
-/
/--
info: error: fuel exhausted
-/
#guard_msgs in
#eval! do
  let prog ← parseLaurelTransformed r"
composite Box { var v: int }
procedure main() {
  var a: Box := new Box; a#v := 10;
  var b: Box := new Box; b#v := 20;
  return a#v + b#v
};
"
  IO.println (toString (runProgram prog))

/-! ## Verification -/

/-! ### Verification Test 1: Assert true -/
/--
info: returned: 1
-/
#guard_msgs in
#eval! do
  let prog ← parseLaurelTransformed r"
procedure main() { assert true; return 1 };
"
  IO.println (toString (runProgram prog))

/-! ### Verification Test 2: Assert false — stuck -/
/--
info: error: fuel exhausted
-/
#guard_msgs in
#eval! do
  let prog ← parseLaurelTransformed r"
procedure main() { assert false; return 1 };
"
  IO.println (toString (runProgram prog))

/-! ### Verification Test 3: Assume true -/
/--
info: returned: 1
-/
#guard_msgs in
#eval! do
  let prog ← parseLaurelTransformed r"
procedure main() { assume true; return 1 };
"
  IO.println (toString (runProgram prog))

/-! ### Verification Test 4: Assume false — stuck -/
/--
info: error: fuel exhausted
-/
#guard_msgs in
#eval! do
  let prog ← parseLaurelTransformed r"
procedure main() { assume false; return 1 };
"
  IO.println (toString (runProgram prog))

/-! ### Verification Test 5: Assert purity -/
/--
info: returned: 0
-/
#guard_msgs in
#eval! do
  let prog ← parseLaurelTransformed r"
procedure main() {
  var x: int := 0;
  assert {x := 1; true};
  return x
};
"
  IO.println (toString (runProgram prog))

/-! ## EdgeCases -/

/-! ### EdgeCases Test 1: No main procedure -/
/--
info: error: no 'main' procedure found
-/
#guard_msgs in
#eval! do
  let prog ← parseLaurelTransformed r"
procedure notMain() { return 1 };
"
  IO.println (toString (runProgram prog))

/-! ### EdgeCases Test 3: Division by zero -/
/--
info: error: fuel exhausted
-/
#guard_msgs in
#eval! do
  let prog ← parseLaurelTransformed r"
procedure main() { return 1 / 0 };
"
  IO.println (toString (runProgram prog))

/-! ### EdgeCases Test 6: Empty main body -/
/--
info: success: void
-/
#guard_msgs in
#eval! do
  let prog ← parseLaurelTransformed r"
procedure main() { };
"
  IO.println (toString (runProgram prog))

/-! ### EdgeCases Test 7: Nonexistent callee -/
/--
info: error: fuel exhausted
-/
#guard_msgs in
#eval! do
  let prog ← parseLaurelTransformed r"
procedure main() { return ghost() };
"
  IO.println (toString (runProgram prog))

/-! ### EdgeCases Test 8: Deeply nested blocks -/
/--
info: returned: 42
-/
#guard_msgs in
#eval! do
  let prog ← parseLaurelTransformed r"
procedure main() {
  if (true) { if (true) { if (true) { return 42 } } }
};
"
  IO.println (toString (runProgram prog))

end Strata.Laurel.ConcreteEval.TransformPreservationTest
