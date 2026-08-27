/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

/-
Demonstrates that the per-yield guarantee assert is meaningful — NOT
vacuous — when the loop body has actual code between yields. Three
tests, each pinning a specific semantic:

  * **Positive (monotonic):** body increments `x`, guarantee says
    `old(x) <= x`. Verifies. The assert at every yield discharges
    `x(p) <= x($heap)` where `x(p)` is the resume value of the prior
    iteration and `x($heap)` is the just-incremented value.

  * **Negative (modify with equality guarantee):** body increments `x`
    but guarantee claims `old(x) == x`. Fails — the assert at the yield
    cannot discharge `prev == prev+1`. The exit assert fails for the
    same reason (the final segment leaves `x` above the step's start).

  * **Negative (decrement with `<=` guarantee):** body decrements `x`
    but guarantee claims `old(x) <= x`. Fails — `prev <= prev-1` is
    refutable, at the yield and again at the exit.
-/

import StrataTest.Languages.Laurel.EndToEndTests.Verification.Concurrency.CoroutineTest

open StrataTest.Util.Concurrency

/-! ## Positive: incrementing body, monotonic guarantee. -/

#eval testCoroutine <|
#strata
program Laurel;

composite Cell { var x: int }

coroutine incMonotonic(s: Cell)
  requires s#x == 0
  relies     old(s#x) <= s#x
  guarantees old(s#x) <= s#x
  modifies *
{
  while (s#x < 10)
    invariant s#x >= 0
    invariant oldGuarantee(s#x) <= s#x
  {
    s#x := s#x + 1;
    yield
  }
};
#end

/-! ## Negative: incrementing body, equality guarantee. -/

#eval testCoroutine <|
#strata
program Laurel;

composite Cell { var x: int }

coroutine incBreaksEquality(s: Cell)
  requires s#x == 0
  relies     old(s#x) == s#x
  guarantees old(s#x) == s#x
//           ^^^^^^^^^^^^^^^ error: coroutine exit: guarantee could not be proved
  modifies *
{
  while (s#x < 10)
    invariant s#x >= 0
  {
    s#x := s#x + 1;
    yield
//  ^^^^^ error: coroutine yield: guarantee could not be proved
  }
};
#end

/-! ## Negative: decrementing body, monotonic guarantee. -/

#eval testCoroutine <|
#strata
program Laurel;

composite Cell { var x: int }

coroutine decBreaksMonotonic(s: Cell)
  requires s#x == 10
  relies     old(s#x) <= s#x
  guarantees old(s#x) <= s#x
//           ^^^^^^^^^^^^^^^ error: coroutine exit: guarantee could not be proved
  modifies *
{
  while (s#x > 0)
  {
    s#x := s#x - 1;
    yield
//  ^^^^^ error: coroutine yield: guarantee could not be proved
  }
};
#end
