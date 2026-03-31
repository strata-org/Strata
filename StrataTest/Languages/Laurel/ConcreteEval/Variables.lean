/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import StrataTest.Languages.Laurel.ConcreteEval.TestHelper

/-!
# Variable Semantics Tests

Tests for local variable declaration (with/without initializer), assignment,
multiple assignments, variable scoping, and uninitialized variable reads.
-/

namespace Strata.Laurel.ConcreteEval.VariablesTest

open Strata.Laurel.ConcreteEval.TestHelper
open Strata.Laurel

/-! ## Test 1: Local var with initializer -/

/--
info: returned: 5
-/
#guard_msgs in
#eval! do
  let prog ← parseLaurel r"
procedure main() { var x: int := 5; return x };
"
  IO.println (toString (interpProgram prog))

/-! ## Test 2: Local var without initializer — x is vVoid but never read -/

/--
info: returned: 0
-/
#guard_msgs in
#eval! do
  let prog ← parseLaurel r"
procedure main() { var x: int; return 0 };
"
  IO.println (toString (interpProgram prog))

/-! ## Test 3: Block expression returns last value after side effects -/

/--
info: returned: 42
-/
#guard_msgs in
#eval! do
  let prog ← parseLaurel r"
procedure main() { var x: int := 0; return {x := 42; x} };
"
  IO.println (toString (interpProgram prog))

/-! ## Test 4: Multiple assignments -/

/--
info: returned: 3
-/
#guard_msgs in
#eval! do
  let prog ← parseLaurel r"
procedure main() { var x: int := 1; x := 2; x := 3; return x };
"
  IO.println (toString (interpProgram prog))

/-! ## Test 5: Variable scoping — inner block variable -/

/--
info: returned: 3
-/
#guard_msgs in
#eval! do
  let prog ← parseLaurel r"
procedure main() {
  var x: int := 1;
  if (true) then { var y: int := 2; x := x + y };
  return x
};
"
  IO.println (toString (interpProgram prog))

/-! ## Test 6: Uninitialized variable read → stuck

Programmatic AST: read a variable that was never declared.
The evaluator returns `none` (stuck), which `interpProgram` maps to `.fuelExhausted`.
-/

#guard
  let body := StmtExpr.Block [
    mk (.Return (some (mk (.Identifier "undeclared"))))
  ] none
  let prog := mkProgram [mkProc "main" [] body]
  match interpProgram prog with
  | .fuelExhausted => true
  | _ => false

end Strata.Laurel.ConcreteEval.VariablesTest
