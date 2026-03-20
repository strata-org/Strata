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
  IO.println (toString (runProgram prog))

/-! ## Test 2: Local var without initializer — x is vVoid but never read -/

/--
info: returned: 0
-/
#guard_msgs in
#eval! do
  let prog ← parseLaurel r"
procedure main() { var x: int; return 0 };
"
  IO.println (toString (runProgram prog))

/-! ## Test 3: Assignment returns assigned value (impure expression position)

The default lift pass handles the block expression `{x := 42; x}` in argument
position.
-/

/--
info: returned: 42
-/
#guard_msgs in
#eval! do
  let prog ← parseLaurel r"
procedure id(x: int) { return x };
procedure main() { var x: int := 0; return id({x := 42; x}) };
"
  IO.println (toString (runProgram prog))

/-! ## Test 4: Multiple assignments -/

/--
info: returned: 3
-/
#guard_msgs in
#eval! do
  let prog ← parseLaurel r"
procedure main() { var x: int := 1; x := 2; x := 3; return x };
"
  IO.println (toString (runProgram prog))

/-! ## Test 5: Variable scoping — inner block variable -/

/--
info: returned: 3
-/
#guard_msgs in
#eval! do
  let prog ← parseLaurel r"
procedure main() {
  var x: int := 1;
  if (true) { var y: int := 2; x := x + y };
  return x
};
"
  IO.println (toString (runProgram prog))

/-! ## Test 6: Uninitialized variable read → stuck

Programmatic AST: read a variable that was never declared.
The evaluator returns `none` (stuck), which `runProgram` maps to `.fuelExhausted`.
-/

#guard
  let body := StmtExpr.Block [
    mk (.Return (some (mk (.Identifier "undeclared"))))
  ] none
  let prog := mkProgram [mkProc "main" [] body]
  match runProgram prog with
  | .fuelExhausted => true
  | _ => false

end Strata.Laurel.ConcreteEval.VariablesTest
