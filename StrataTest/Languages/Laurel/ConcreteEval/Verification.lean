/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import StrataTest.Languages.Laurel.ConcreteEval.TestHelper

/-!
# Verification Construct Tests

Tests for assert, assume, assert/assume purity, and ProveBy semantics.
-/

namespace Strata.Laurel.ConcreteEval.VerificationTest

open Strata.Laurel.ConcreteEval.TestHelper
open Strata.Laurel

/-! ## Test 1: Assert true → succeeds -/

/--
info: returned: 1
-/
#guard_msgs in
#eval! do
  let prog ← parseLaurel r"
procedure main() { assert true; return 1 };
"
  IO.println (toString (runProgram prog))

/-! ## Test 2: Assert false → stuck -/

/--
info: error: fuel exhausted
-/
#guard_msgs in
#eval! do
  let prog ← parseLaurel r"
procedure main() { assert false; return 1 };
"
  IO.println (toString (runProgram prog))

/-! ## Test 3: Assume true → succeeds -/

/--
info: returned: 1
-/
#guard_msgs in
#eval! do
  let prog ← parseLaurel r"
procedure main() { assume true; return 1 };
"
  IO.println (toString (runProgram prog))

/-! ## Test 4: Assume false → stuck -/

/--
info: error: fuel exhausted
-/
#guard_msgs in
#eval! do
  let prog ← parseLaurel r"
procedure main() { assume false; return 1 };
"
  IO.println (toString (runProgram prog))

/-! ## Test 5: Assert purity — side effects in condition discarded

The semantics evaluates the condition but returns the original σ and h.
We use `parseLaurel true` (with lift) so the impure expression `{x := 1; true}`
is handled. After assert, x should still be 0.
-/

/--
info: returned: 0
-/
#guard_msgs in
#eval! do
  let prog ← parseLaurel (applyLift := true) r"
procedure main() {
  var x: int := 0;
  assert {x := 1; true};
  return x
};
"
  IO.println (toString (runProgram prog))

/-! ## Test 6: ProveBy — semantics of value, proof ignored (programmatic AST) -/

#guard
  let body := StmtExpr.Return (some (mk (.ProveBy (mk (.LiteralInt 42)) (mk (.LiteralBool true)))))
  let prog := mkProgram [mkProc "main" [] body]
  getOutcome (evalProgram prog) = some (.ret (some (.vInt 42)))

end Strata.Laurel.ConcreteEval.VerificationTest
