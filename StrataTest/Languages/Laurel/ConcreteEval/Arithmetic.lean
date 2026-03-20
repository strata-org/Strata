/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import StrataTest.Languages.Laurel.ConcreteEval.TestHelper

/-!
# Arithmetic Operations Tests

Tests for basic arithmetic (add, sub, mul, div, mod), negation via
subtraction, division/modulus by zero, large integers, compound
expressions, and DivT/ModT stuck behavior.
-/

namespace Strata.Laurel.ConcreteEval.ArithmeticTest

open Strata.Laurel.ConcreteEval.TestHelper
open Strata.Laurel

/-! ## Test 1: Addition -/

/--
info: returned: 7
-/
#guard_msgs in
#eval! do
  let prog ← parseLaurel r"
procedure main() { return 3 + 4 };
"
  IO.println (toString (runProgram prog))

/-! ## Test 2: Subtraction -/

/--
info: returned: 7
-/
#guard_msgs in
#eval! do
  let prog ← parseLaurel r"
procedure main() { return 10 - 3 };
"
  IO.println (toString (runProgram prog))

/-! ## Test 3: Multiplication -/

/--
info: returned: 42
-/
#guard_msgs in
#eval! do
  let prog ← parseLaurel r"
procedure main() { return 6 * 7 };
"
  IO.println (toString (runProgram prog))

/-! ## Test 4: Euclidean division -/

/--
info: returned: 3
-/
#guard_msgs in
#eval! do
  let prog ← parseLaurel r"
procedure main() { return 7 / 2 };
"
  IO.println (toString (runProgram prog))

/-! ## Test 5: Euclidean modulus -/

/--
info: returned: 1
-/
#guard_msgs in
#eval! do
  let prog ← parseLaurel r"
procedure main() { return 7 % 2 };
"
  IO.println (toString (runProgram prog))

/-! ## Test 6: Negation via subtraction -/

/--
info: returned: -5
-/
#guard_msgs in
#eval! do
  let prog ← parseLaurel r"
procedure main() { return 0 - 5 };
"
  IO.println (toString (runProgram prog))

/-! ## Test 7: Division by zero — stuck -/

/--
info: error: fuel exhausted
-/
#guard_msgs in
#eval! do
  let prog ← parseLaurel r"
procedure main() { return 1 / 0 };
"
  IO.println (toString (runProgram prog))

/-! ## Test 8: Modulus by zero — stuck -/

/--
info: error: fuel exhausted
-/
#guard_msgs in
#eval! do
  let prog ← parseLaurel r"
procedure main() { return 1 % 0 };
"
  IO.println (toString (runProgram prog))

/-! ## Test 9: Large integers (arbitrary precision) -/

/--
info: returned: 1000000000000000000
-/
#guard_msgs in
#eval! do
  let prog ← parseLaurel r"
procedure main() { return 1000000000 * 1000000000 };
"
  IO.println (toString (runProgram prog))

/-! ## Test 10: Compound expression -/

/--
info: returned: 15
-/
#guard_msgs in
#eval! do
  let prog ← parseLaurel r"
procedure main() { return (2 + 3) * (4 - 1) };
"
  IO.println (toString (runProgram prog))

/-! ## Test 11: Negative arithmetic -/

/--
info: returned: -7
-/
#guard_msgs in
#eval! do
  let prog ← parseLaurel r"
procedure main() { return (-3) + (-4) };
"
  IO.println (toString (runProgram prog))

/-! ## Test 12: DivT — truncation division -/

/--
info: returned: 3
-/
#guard_msgs in
#eval! do
  let prog ← parseLaurel r"
procedure main() { return 7 /t 2 };
"
  IO.println (toString (runProgram prog))

/-! ## Test 13: ModT — truncation modulus -/

/--
info: returned: 1
-/
#guard_msgs in
#eval! do
  let prog ← parseLaurel r"
procedure main() { return 7 %t 2 };
"
  IO.println (toString (runProgram prog))

/-! ## Test 14: DivT with negative dividend (truncation toward zero) -/

/--
info: returned: -3
-/
#guard_msgs in
#eval! do
  let prog ← parseLaurel r"
procedure main() { return (-7) /t 2 };
"
  IO.println (toString (runProgram prog))

/-! ## Test 15: ModT with negative dividend -/

/--
info: returned: -1
-/
#guard_msgs in
#eval! do
  let prog ← parseLaurel r"
procedure main() { return (-7) %t 2 };
"
  IO.println (toString (runProgram prog))

/-! ## Test 16: DivT by zero — stuck -/

/--
info: error: fuel exhausted
-/
#guard_msgs in
#eval! do
  let prog ← parseLaurel r"
procedure main() { return 7 /t 0 };
"
  IO.println (toString (runProgram prog))

/-! ## Test 17: ModT by zero — stuck -/

/--
info: error: fuel exhausted
-/
#guard_msgs in
#eval! do
  let prog ← parseLaurel r"
procedure main() { return 7 %t 0 };
"
  IO.println (toString (runProgram prog))

end Strata.Laurel.ConcreteEval.ArithmeticTest
