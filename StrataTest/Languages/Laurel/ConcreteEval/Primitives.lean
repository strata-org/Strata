/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import StrataTest.Languages.Laurel.ConcreteEval.TestHelper

/-!
# Primitive Literal Tests

Tests for integer literals (positive, negative, zero), boolean literals,
string literals, and void procedures.
-/

namespace Strata.Laurel.ConcreteEval.PrimitivesTest

open Strata.Laurel.ConcreteEval.TestHelper
open Strata.Laurel

/-! ## Test 1: Integer literal (positive) -/

/--
info: returned: 42
-/
#guard_msgs in
#eval! do
  let prog ← parseLaurel r"
procedure main() { return 42 };
"
  IO.println (toString (interpProgram prog))

/-! ## Test 2: Integer literal (negative) -/

/--
info: returned: -7
-/
#guard_msgs in
#eval! do
  let prog ← parseLaurel r"
procedure main() { return -7 };
"
  IO.println (toString (interpProgram prog))

/-! ## Test 3: Integer literal (zero) -/

/--
info: returned: 0
-/
#guard_msgs in
#eval! do
  let prog ← parseLaurel r"
procedure main() { return 0 };
"
  IO.println (toString (interpProgram prog))

/-! ## Test 4: Boolean true -/

/--
info: returned: 1
-/
#guard_msgs in
#eval! do
  let prog ← parseLaurel r"
procedure main() {
  if (true) { return 1 } else { return 0 }
};
"
  IO.println (toString (interpProgram prog))

/-! ## Test 5: Boolean false -/

/--
info: returned: 0
-/
#guard_msgs in
#eval! do
  let prog ← parseLaurel r"
procedure main() {
  if (false) { return 1 } else { return 0 }
};
"
  IO.println (toString (interpProgram prog))

/-! ## Test 6: String literal — equality -/

/--
info: returned: 1
-/
#guard_msgs in
#eval! do
  let prog ← parseLaurel r#"
procedure main() {
  if ("hello" == "hello") { return 1 } else { return 0 }
};
"#
  IO.println (toString (interpProgram prog))

/-! ## Test 7: Empty string — equality -/

/--
info: returned: 1
-/
#guard_msgs in
#eval! do
  let prog ← parseLaurel r#"
procedure main() {
  if ("" == "") { return 1 } else { return 0 }
};
"#
  IO.println (toString (interpProgram prog))

/-! ## Test 8: Void — procedure with no return value -/

/--
info: returned: 0
-/
#guard_msgs in
#eval! do
  let prog ← parseLaurel r"
procedure noop() { var x: int := 1 };
procedure main() { noop(); return 0 };
"
  IO.println (toString (interpProgram prog))

end Strata.Laurel.ConcreteEval.PrimitivesTest
