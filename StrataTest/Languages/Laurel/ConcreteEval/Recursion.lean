/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import StrataTest.Languages.Laurel.ConcreteEval.TestHelper

/-!
# Recursion Semantics Tests

Tests for simple recursion (factorial), mutual recursion (even/odd),
deep recursion (fuel exhaustion), recursion with heap effects, and fibonacci.
-/

namespace Strata.Laurel.ConcreteEval.RecursionTest

open Strata.Laurel.ConcreteEval.TestHelper
open Strata.Laurel

/-! ## Test 1: Simple recursion — factorial -/

/--
info: returned: 120
-/
#guard_msgs in
#eval! do
  let prog ← parseLaurel r"
procedure fact(n: int) {
  if (n <= 1) { return 1 } else { return n * fact(n - 1) }
};
procedure main() { return fact(5) };
"
  IO.println (toString (runProgram prog))

/-! ## Test 2: Mutual recursion — even/odd -/

/--
info: returned: 1
-/
#guard_msgs in
#eval! do
  let prog ← parseLaurel r"
procedure isEven(n: int) {
  if (n == 0) { return true } else { return isOdd(n - 1) }
};
procedure isOdd(n: int) {
  if (n == 0) { return false } else { return isEven(n - 1) }
};
procedure main() { if (isEven(4)) { return 1 } else { return 0 } };
"
  IO.println (toString (runProgram prog))

/-! ## Test 3: Deep recursion — fuel exhaustion

Default fuel is 10000; `deep(100000)` exceeds it.
-/

/--
info: error: fuel exhausted
-/
#guard_msgs in
#eval! do
  let prog ← parseLaurel r"
procedure deep(n: int) {
  if (n == 0) { return 0 } else { return deep(n - 1) }
};
procedure main() { return deep(100000) };
"
  IO.println (toString (runProgram prog))

/-! ## Test 4: Recursion with heap effects

`fill(b, 5)` adds 5+4+3+2+1 = 15 to `b#v`.
-/

/--
info: returned: 15
-/
#guard_msgs in
#eval! do
  let prog ← parseLaurel r"
composite Box { var v: int }
procedure fill(b: Box, n: int) {
  if (n <= 0) { return 0 }
  else { b#v := b#v + n; return fill(b, n - 1) }
};
procedure main() {
  var b: Box := new Box; b#v := 0;
  fill(b, 5);
  return b#v
};
"
  IO.println (toString (runProgram prog))

/-! ## Test 5: Fibonacci -/

/--
info: returned: 55
-/
#guard_msgs in
#eval! do
  let prog ← parseLaurel r"
procedure fib(n: int) {
  if (n <= 1) { return n }
  else { return fib(n - 1) + fib(n - 2) }
};
procedure main() { return fib(10) };
"
  IO.println (toString (runProgram prog))

end Strata.Laurel.ConcreteEval.RecursionTest
