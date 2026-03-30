/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import StrataTest.Languages.Laurel.ConcreteEval.TestHelper

/-!
# Boolean Operations and Short-Circuit Semantics Tests

Tests for comparison operators, boolean operations, and short-circuit
semantics. Short-circuit tests verify that side effects do NOT occur
in the unevaluated branch.

All tests use `parseLaurel`. The interpreter (`interpStmt`)
evaluates `AndThen`/`OrElse`/`Implies` with proper short-circuit semantics,
while `And`/`Or` are evaluated eagerly via `interpPrimOp`.
-/

namespace Strata.Laurel.ConcreteEval.BooleanOpsTest

open Strata.Laurel.ConcreteEval.TestHelper
open Strata.Laurel

/-! ## Comparison Operators -/

/-! ### Test 1: Lt, Leq, Gt, Geq on integers -/

/--
info: returned: 1
-/
#guard_msgs in
#eval! do
  let prog ← parseLaurel r"
procedure main() {
  var a: bool := 1 < 2;
  var b: bool := 2 <= 2;
  var c: bool := 3 > 2;
  var d: bool := 2 >= 2;
  if (a && b && c && d) { return 1 } else { return 0 }
};
"
  IO.println (toString (interpProgram prog))

/-! ### Test 2: Eq and Neq on integers -/

/--
info: returned: 1
-/
#guard_msgs in
#eval! do
  let prog ← parseLaurel r"
procedure main() {
  if (5 == 5 && 5 != 6) { return 1 } else { return 0 }
};
"
  IO.println (toString (interpProgram prog))

/-! ### Test 3: Eq and Neq on booleans -/

/--
info: returned: 1
-/
#guard_msgs in
#eval! do
  let prog ← parseLaurel r"
procedure main() {
  if (true == true && true != false) { return 1 } else { return 0 }
};
"
  IO.println (toString (interpProgram prog))

/-! ### Test 4: Eq and Neq on strings -/

/--
info: returned: 1
-/
#guard_msgs in
#eval! do
  let prog ← parseLaurel r#"
procedure main() {
  if ("abc" == "abc" && "abc" != "def") { return 1 } else { return 0 }
};
"#
  IO.println (toString (interpProgram prog))

/-! ### Test 5: Not operator -/

/--
info: returned: 1
-/
#guard_msgs in
#eval! do
  let prog ← parseLaurel r"
procedure main() {
  if (!false && !(!true)) { return 1 } else { return 0 }
};
"
  IO.println (toString (interpProgram prog))

/-! ### Test 6: String concatenation -/

/--
info: returned: 1
-/
#guard_msgs in
#eval! do
  let prog ← parseLaurel r#"
procedure main() {
  if ("ab" ++ "cd" == "abcd") { return 1 } else { return 0 }
};
"#
  IO.println (toString (interpProgram prog))

/-! ## Short-Circuit And -/

/-! ### Test 7: false && <side-effect> — RHS not evaluated -/

/--
info: returned: 0
-/
#guard_msgs in
#eval! do
  let prog ← parseLaurel r"
procedure main() {
  var x: int := 0;
  var b: bool := false && {x := 1; true};
  return x
};
"
  IO.println (toString (interpProgram prog))

/-! ### Test 8: true && <side-effect> — RHS IS evaluated -/

/--
info: returned: 1
-/
#guard_msgs in
#eval! do
  let prog ← parseLaurel r"
procedure main() {
  var x: int := 0;
  var b: bool := true && {x := 1; true};
  return x
};
"
  IO.println (toString (interpProgram prog))

/-! ### Test 9: Nested short-circuit And -/

/--
info: returned: 0
-/
#guard_msgs in
#eval! do
  let prog ← parseLaurel r"
procedure main() {
  var x: int := 0;
  var b: bool := false && (true && {x := 1; true});
  return x
};
"
  IO.println (toString (interpProgram prog))

/-! ## Short-Circuit Or -/

/-! ### Test 10: true || <side-effect> — RHS not evaluated -/

/--
info: returned: 0
-/
#guard_msgs in
#eval! do
  let prog ← parseLaurel r"
procedure main() {
  var x: int := 0;
  var b: bool := true || {x := 1; false};
  return x
};
"
  IO.println (toString (interpProgram prog))

/-! ### Test 11: false || <side-effect> — RHS IS evaluated -/

/--
info: returned: 1
-/
#guard_msgs in
#eval! do
  let prog ← parseLaurel r"
procedure main() {
  var x: int := 0;
  var b: bool := false || {x := 1; true};
  return x
};
"
  IO.println (toString (interpProgram prog))

/-! ### Test 12: Nested short-circuit Or -/

/--
info: returned: 0
-/
#guard_msgs in
#eval! do
  let prog ← parseLaurel r"
procedure main() {
  var x: int := 0;
  var b: bool := true || (false || {x := 1; true});
  return x
};
"
  IO.println (toString (interpProgram prog))

/-! ## Short-Circuit Implies -/

/-! ### Test 13: false ==> <side-effect> — RHS not evaluated -/

/--
info: returned: 0
-/
#guard_msgs in
#eval! do
  let prog ← parseLaurel r"
procedure main() {
  var x: int := 0;
  var b: bool := false ==> {x := 1; false};
  return x
};
"
  IO.println (toString (interpProgram prog))

/-! ### Test 14: true ==> <side-effect> — RHS IS evaluated -/

/--
info: returned: 1
-/
#guard_msgs in
#eval! do
  let prog ← parseLaurel r"
procedure main() {
  var x: int := 0;
  var b: bool := true ==> {x := 1; true};
  return x
};
"
  IO.println (toString (interpProgram prog))

/-! ## Combined -/

/-! ### Test 15: Mixed short-circuit with side effects -/

/--
info: returned: 10
-/
#guard_msgs in
#eval! do
  let prog ← parseLaurel r"
procedure main() {
  var x: int := 0;
  var b: bool := (true || {x := x + 1; true}) && (false || {x := x + 10; true});
  return x
};
"
  IO.println (toString (interpProgram prog))

end Strata.Laurel.ConcreteEval.BooleanOpsTest
