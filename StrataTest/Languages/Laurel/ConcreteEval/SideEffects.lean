/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import StrataTest.Languages.Laurel.ConcreteEval.TestHelper

/-!
# Side Effects and Evaluation Order Tests

Tests for side effects in expression position and left-to-right evaluation
order of arguments. The evaluation order is directly from `interpArgs`.

The `interpArgs` function in `LaurelInterpreter.lean` evaluates arguments
left-to-right, threading store and heap through each argument evaluation.
These tests are prescriptive — they define the intended evaluation order.
-/

namespace Strata.Laurel.ConcreteEval.SideEffectsTest

open Strata.Laurel.ConcreteEval.TestHelper
open Strata.Laurel

/-! ## Test 1: Left-to-right argument evaluation order

First arg: x becomes 1, evaluates to 1.
Second arg: x (now 1) becomes 1+10=11, evaluates to 11.
add(1, 11) = 12.
-/

/--
info: returned: 12
-/
#guard_msgs in
#eval! do
  let prog ← parseLaurel r"
procedure add(a: int, b: int) { return a + b };
procedure main() {
  var x: int := 0;
  return add({x := 1; x}, {x := x + 10; x})
};
"
  IO.println (toString (interpProgram prog))

/-! ## Test 2: Assignment in argument position

Side effect sets a=42, id returns 42, so b=42. a+b = 84.
-/

/--
info: returned: 84
-/
#guard_msgs in
#eval! do
  let prog ← parseLaurel r"
procedure id(x: int) { return x };
procedure main() {
  var a: int := 0;
  var b: int := id({a := 42; a});
  return a + b
};
"
  IO.println (toString (interpProgram prog))

/-! ## Test 3: Block expression as argument

Block declares local t=10, evaluates to t+5=15. id(15) = 15.
-/

/--
info: returned: 15
-/
#guard_msgs in
#eval! do
  let prog ← parseLaurel r"
procedure id(x: int) { return x };
procedure main() {
  return id({var t: int := 10; t + 5})
};
"
  IO.println (toString (interpProgram prog))

/-! ## Test 4: Side effects in if condition

Block in condition sets x=1 and evaluates to true (1==1).
Then-branch reads x=1, returns 1+10=11.
-/

/--
info: returned: 11
-/
#guard_msgs in
#eval! do
  let prog ← parseLaurel r"
procedure main() {
  var x: int := 0;
  if ({x := 1; x == 1}) then { return x + 10 } else { return x }
};
"
  IO.println (toString (interpProgram prog))

/-! ## Test 5: Side effects persist across loop iterations

Each iteration: side effect adds 10 to x, id returns that value which is
assigned back. After 3 iterations: x = 30.

This test uses side effects in call arguments inside the loop body.
-/

/--
info: returned: 30
-/
#guard_msgs in
#eval! do
  let prog ← parseLaurel r"
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
  IO.println (toString (interpProgram prog))

/-! ## Test 6: Multiple side effects across nested calls

Inner add: first arg: x=1*2=2, val=2; second arg: x=2+3=5, val=5; add(2,5)=7.
Outer add: first arg=7; second arg: x is now 5, val=5; add(7,5)=12.
-/

/--
info: returned: 12
-/
#guard_msgs in
#eval! do
  let prog ← parseLaurel r"
procedure add(a: int, b: int) { return a + b };
procedure main() {
  var x: int := 1;
  return add(add({x := x * 2; x}, {x := x + 3; x}), x)
};
"
  IO.println (toString (interpProgram prog))

end Strata.Laurel.ConcreteEval.SideEffectsTest
