/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import StrataTest.Languages.Laurel.ConcreteEval.TestHelper

/-!
# Procedure Call Semantics Tests

Tests for call-by-value semantics, shared heap behavior, parameter
reassignment, nested calls, and void returns.
-/

namespace Strata.Laurel.ConcreteEval.ProceduresTest

open Strata.Laurel.ConcreteEval.TestHelper
open Strata.Laurel

/-! ## Test 1: Call by value — primitive not modified in caller -/

/--
info: returned: 5
-/
#guard_msgs in
#eval! do
  let prog ← parseLaurel r"
procedure inc(x: int) { x := x + 1; return x };
procedure main() { var a: int := 5; var b: int := inc(a); return a };
"
  IO.println (toString (runProgram prog))

/-! ## Test 2: Shared heap — field mutation through passed ref is visible -/

/--
info: returned: 42
-/
#guard_msgs in
#eval! do
  let prog ← parseLaurel r"
composite Point { var x: int }
procedure setX(p: Point, v: int) { p#x := v };
procedure main() {
  var p: Point := new Point; p#x := 1; setX(p, 42); return p#x
};
"
  IO.println (toString (runProgram prog))

/-! ## Test 3: Parameter reassignment — callee rebinding does not affect caller -/

/--
info: returned: 1
-/
#guard_msgs in
#eval! do
  let prog ← parseLaurel r"
composite Point { var x: int }
procedure replace(p: Point) { p := new Point; p#x := 99 };
procedure main() {
  var p: Point := new Point; p#x := 1; replace(p); return p#x
};
"
  IO.println (toString (runProgram prog))

/-! ## Test 4: Simple return value from callee -/

/--
info: returned: 42
-/
#guard_msgs in
#eval! do
  let prog ← parseLaurel r"
procedure double(x: int) { return x * 2 };
procedure main() { return double(21) };
"
  IO.println (toString (runProgram prog))

/-! ## Test 5: Nested procedure calls -/

/--
info: returned: 26
-/
#guard_msgs in
#eval! do
  let prog ← parseLaurel r"
procedure add(a: int, b: int) { return a + b };
procedure mul(a: int, b: int) { return a * b };
procedure main() { return add(mul(2, 3), mul(4, 5)) };
"
  IO.println (toString (runProgram prog))

/-! ## Test 6: Procedure modifying heap, caller reads updated heap -/

/--
info: returned: 3
-/
#guard_msgs in
#eval! do
  let prog ← parseLaurel r"
composite Counter { var n: int }
procedure increment(c: Counter) { c#n := c#n + 1 };
procedure main() {
  var c: Counter := new Counter; c#n := 0;
  increment(c); increment(c); increment(c);
  return c#n
};
"
  IO.println (toString (runProgram prog))

/-! ## Test 7: Callee cannot see caller's locals -/

-- Note: "fuel exhausted" is reported because `readX()` looks up `x` in an
-- empty store (bindParams creates a fresh store for a zero-parameter procedure),
-- causing the evaluator to get stuck (returns `none`). `runProgram` maps any
-- `none` to `.fuelExhausted`, so stuck states and true fuel exhaustion are
-- indistinguishable in the output.
/--
info: error: fuel exhausted
-/
#guard_msgs in
#eval! do
  let prog ← parseLaurel r"
procedure readX() { return x };
procedure main() { var x: int := 42; return readX() };
"
  IO.println (toString (runProgram prog))

/-! ## Test 8: Procedure with no return — returns void -/

/--
info: returned: 0
-/
#guard_msgs in
#eval! do
  let prog ← parseLaurel r"
procedure noop() { var x: int := 1 };
procedure main() { noop(); return 0 };
"
  IO.println (toString (runProgram prog))

end Strata.Laurel.ConcreteEval.ProceduresTest
