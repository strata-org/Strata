/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import StrataTest.Languages.Laurel.ConcreteEval.TestHelper

/-!
# Control Flow Tests

Tests for if-then-else, while loops, early return, nested control flow,
fuel exhaustion, and labeled block exit (break).
-/

namespace Strata.Laurel.ConcreteEval.ControlFlowTest

open Strata.Laurel.ConcreteEval.TestHelper
open Strata.Laurel

/-! ## Test 1: If-then-else, true branch -/

/--
info: returned: 1
-/
#guard_msgs in
#eval! do
  let prog ← parseLaurel r"
procedure main() {
  if (true) { return 1 } else { return 2 }
};
"
  IO.println (toString (interpProgram prog))

/-! ## Test 2: If-then-else, false branch -/

/--
info: returned: 2
-/
#guard_msgs in
#eval! do
  let prog ← parseLaurel r"
procedure main() {
  if (false) { return 1 } else { return 2 }
};
"
  IO.println (toString (interpProgram prog))

/-! ## Test 3: If-then without else (true) — returns result of then branch -/

/--
info: returned: 1
-/
#guard_msgs in
#eval! do
  let prog ← parseLaurel r"
procedure main() {
  if (true) { return 1 };
  return 0
};
"
  IO.println (toString (interpProgram prog))

/-! ## Test 4: If-then without else (false) — falls through -/

/--
info: returned: 0
-/
#guard_msgs in
#eval! do
  let prog ← parseLaurel r"
procedure main() {
  var x: int := 0;
  if (false) { x := 1 };
  return x
};
"
  IO.println (toString (interpProgram prog))

/-! ## Test 5: Nested if-then-else -/

/--
info: returned: 2
-/
#guard_msgs in
#eval! do
  let prog ← parseLaurel r"
procedure main() {
  var x: int := 15;
  if (x > 10) {
    if (x > 20) { return 3 } else { return 2 }
  } else { return 1 }
};
"
  IO.println (toString (interpProgram prog))

/-! ## Test 6: While loop — zero iterations -/

/--
info: returned: 0
-/
#guard_msgs in
#eval! do
  let prog ← parseLaurel r"
procedure main() {
  var x: int := 0;
  while (false) { x := 1 };
  return x
};
"
  IO.println (toString (interpProgram prog))

/-! ## Test 7: While loop — single iteration -/

/--
info: returned: 42
-/
#guard_msgs in
#eval! do
  let prog ← parseLaurel r"
procedure main() {
  var x: int := 0;
  var done: bool := false;
  while (!done) { x := 42; done := true };
  return x
};
"
  IO.println (toString (interpProgram prog))

/-! ## Test 8: While loop with early return -/

/--
info: returned: 5
-/
#guard_msgs in
#eval! do
  let prog ← parseLaurel r"
procedure main() {
  var i: int := 0;
  while (i < 100) {
    if (i == 5) { return i };
    i := i + 1
  };
  return -1
};
"
  IO.println (toString (interpProgram prog))

/-! ## Test 9: Return from nested blocks propagates -/

/--
info: returned: 42
-/
#guard_msgs in
#eval! do
  let prog ← parseLaurel r"
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
  IO.println (toString (interpProgram prog))

/-! ## Test 10: Nested while loops

Variable declarations inside loop bodies fail on re-entry because `initStore`
rejects already-bound names. We declare all variables before the loops.
We use small bounds (1 iteration each) to keep heartbeat usage low while
still exercising the nesting semantics.
-/

/--
info: returned: 1
-/
#guard_msgs in
#eval! do
  let prog ← parseLaurel r"
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
  IO.println (toString (interpProgram prog))

/-! ## Test 11: Fuel exhaustion on infinite loop

An infinite loop with no exit path. The loop body only assigns to an
existing variable, so it runs until fuel is exhausted.
-/

/--
info: error: fuel exhausted
-/
#guard_msgs in
#eval! do
  let prog ← parseLaurel r"
procedure main() {
  var x: int := 0;
  while (true) { x := x + 1 };
  return 0
};
"
  IO.println (toString (interpProgram prog))

/-! ## Test 12: Variable re-declaration inside loop body

Declaring a variable inside a loop body causes `initStore` to reject the
re-declaration on the second iteration (the variable is already bound).
`interpProgram` returns `none`, which `interpProgram` maps to `.fuelExhausted`.
This is a known limitation — not true fuel exhaustion.
-/

/--
info: error: fuel exhausted
-/
#guard_msgs in
#eval! do
  let prog ← parseLaurel r"
procedure main() {
  while (true) { var x: int := 0 };
  return 0
};
"
  IO.println (toString (interpProgram prog))

/-! ## Test 13: Labeled block exit (break)

Laurel concrete syntax does not have `break`/`continue` keywords.
Instead, `Exit` targets a labeled `Block`. We construct the AST
programmatically: a while(true) loop whose body increments x and
exits a labeled block wrapping the loop when x reaches 5.
-/

/--
info: returned: 5
-/
#guard_msgs in
#eval! do
  -- Build: procedure main() {
  --   var x: int := 0;
  --   { while (true) { x := x + 1; if (x == 5) { exit loopBlock } } } loopBlock;
  --   return x
  -- }
  let xId : WithMetadata StmtExpr := ⟨.Identifier (mkId "x"), .empty⟩
  let varX := mk (.LocalVariable (mkId "x") ⟨.TInt, .empty⟩ (some ⟨.LiteralInt 0, .empty⟩))
  let incrX := mk (.Assign [xId]
    ⟨.PrimitiveOp .Add [xId, ⟨.LiteralInt 1, .empty⟩], .empty⟩)
  let exitBlock := mk (.Exit "loopBlock")
  let guard := mk (.IfThenElse
    ⟨.PrimitiveOp .Eq [xId, ⟨.LiteralInt 5, .empty⟩], .empty⟩
    ⟨.Block [exitBlock] none, .empty⟩
    none)
  let whileLoop := mk (.While ⟨.LiteralBool true, .empty⟩ [] none
    ⟨.Block [incrX, guard] none, .empty⟩)
  let labeledBlock := mk (.Block [whileLoop] (some "loopBlock"))
  let ret := mk (.Return (some xId))
  let body := StmtExpr.Block [varX, labeledBlock, ret] none
  let proc := mkProc "main" [] body
  let prog := mkProgram [proc]
  IO.println (toString (interpProgram prog))

end Strata.Laurel.ConcreteEval.ControlFlowTest
