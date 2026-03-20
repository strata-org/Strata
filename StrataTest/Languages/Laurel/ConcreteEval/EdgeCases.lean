/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import StrataTest.Languages.Laurel.ConcreteEval.TestHelper

/-!
# Edge Case Tests

Tests for missing main, opaque body, division by zero, uninitialized
variables, field access on non-ref, empty body, nonexistent callee,
and deeply nested blocks.
-/

namespace Strata.Laurel.ConcreteEval.EdgeCasesTest

open Strata.Laurel.ConcreteEval.TestHelper
open Strata.Laurel

/-! ## Test 1: No main procedure → noMain -/

/--
info: error: no 'main' procedure found
-/
#guard_msgs in
#eval! do
  let prog ← parseLaurel r"
procedure notMain() { return 1 };
"
  IO.println (toString (runProgram prog))

/-! ## Test 2: Main with opaque body → noBody (programmatic AST) -/

/--
info: error: 'main' has no body
-/
#guard_msgs in
#eval! do
  let proc : Procedure := {
    name := mkId "main", inputs := [], outputs := [],
    preconditions := [], determinism := .deterministic none,
    isFunctional := false, decreases := none,
    body := .Opaque [] none [], md := emd
  }
  let prog := mkProgram [proc]
  IO.println (toString (runProgram prog))

/-! ## Test 3: Division by zero → stuck -/

/--
info: error: fuel exhausted
-/
#guard_msgs in
#eval! do
  let prog ← parseLaurel r"
procedure main() { return 1 / 0 };
"
  IO.println (toString (runProgram prog))

/-! ## Test 4: Uninitialized variable read → stuck (programmatic AST)

Read a variable not in the store. The Identifier case returns none.
-/

#guard
  let body := StmtExpr.Return (some (mk (.Identifier "ghost")))
  let prog := mkProgram [mkProc "main" [] body]
  (evalProgram prog).isNone

/-! ## Test 5: Field access on non-ref → stuck (programmatic AST)

`FieldSelect (LiteralInt 5) "x"` — target is not a vRef, so FieldSelect
pattern match fails.
-/

#guard
  let body := StmtExpr.Return (some (mk (.FieldSelect (mk (.LiteralInt 5)) "x")))
  let prog := mkProgram [mkProc "main" [] body]
  (evalProgram prog).isNone

/-! ## Test 6: Empty main body

An empty block evaluates to `(.normal .vVoid)`, which `runProgram` maps
to `.success void`. The procedure does not return, so the outcome is
`success` (not `returned`).
-/

/--
info: success: void
-/
#guard_msgs in
#eval! do
  let prog ← parseLaurel r"
procedure main() { };
"
  IO.println (toString (runProgram prog))

/-! ## Test 7: Procedure calling nonexistent procedure → stuck -/

/--
info: error: fuel exhausted
-/
#guard_msgs in
#eval! do
  let prog ← parseLaurel r"
procedure main() { return ghost() };
"
  IO.println (toString (runProgram prog))

/-! ## Test 8: Deeply nested blocks -/

/--
info: returned: 42
-/
#guard_msgs in
#eval! do
  let prog ← parseLaurel r"
procedure main() {
  if (true) { if (true) { if (true) { return 42 } } }
};
"
  IO.println (toString (runProgram prog))

end Strata.Laurel.ConcreteEval.EdgeCasesTest
