/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

/-
Sanity check for the YieldElim `old(...)` semantics across multiple
yields. Under our framework `old($heap)` in:

  * a **guarantee** binds to `$h_yield_prev` (state at the start of the
    *current* coroutine step = state right after the *previous* yield's
    env havoc + assume; procedure entry for the first yield);
  * a **rely** binds to `$h_r_old` (state right before the *current*
    yield's env havoc).

Both snapshots are reassigned at every yield, so `old` is *per-yield*,
not "procedure entry". This file pins that behavior with two kinds of
test:

  * **Positive** — a multi-yield body where the rely correctly carries
    a *changing* value across env steps. Verifies only because `old`
    in the rely is per-yield (under a procedure-entry interpretation
    the second assert would fail).

  * **Negative (localization)** — a body where a field is written only
    between yield N-1 and yield N. Under per-yield semantics, **only
    yield N's guarantee fails**, not yield N+1's. The annotation pins
    exactly one failure; if yield N+1 also failed (which would happen
    under procedure-entry semantics), the annotation pin would break.
-/

import StrataTest.Languages.Laurel.EndToEndTests.Verification.Concurrency.CoroutineTest

open StrataTest.Util.Concurrency

/-
Positive test: the rely's `old` is per-yield, so it correctly
preserves the *current* heap value across each env step — even when
the body changes that value between yields.
-/

#eval testCoroutine <|
#strata
program Laurel;

composite Cell {
  var x: int
}

coroutine relyOldIsPerYield(s: Cell)
  requires s#x == 0
  relies old(s#x) == s#x
  guarantees old(s#x) <= s#x
  modifies *
{
  yield;
  assert s#x == 0;
  s#x := 7;
  yield;
  assert s#x == 7
};
#end

/-
Negative test (two-yield localization): the body writes `s#x` between
procedure entry and yield 1. Under per-yield semantics:
  * yield 1's guarantee fails (`old(x) = 0`, `x = 7`),
  * yield 2's guarantee holds (`old(x)` rebinds to `7`, `x = 7`).
If `old` were procedure-entry, yield 2 would also fail.
-/

#eval testCoroutine <|
#strata
program Laurel;

composite Cell {
  var x: int
}

coroutine guaranteeOldLocalizedTwoYields(s: Cell)
  requires s#x == 0
  relies old(s#x) == s#x
  guarantees old(s#x) == s#x
  modifies *
{
  s#x := 7;
  yield;
//^^^^^ error: coroutine yield: guarantee does not hold
  yield
};
#end

/-
Negative test (three-yield localization): the body writes `s#x`
between yield 2 and yield 3. Under per-yield semantics:
  * yields 1 and 2 hold vacuously (no writes since the prior snapshot),
  * yield 3's guarantee fails (`old(x) = 0`, `x = 7`),
  * yield 4's guarantee holds (`old(x)` rebinds to `7`, `x = 7`).
Confirms `$h_yield_prev` tracks the *most recent* yield, not any
earlier one.
-/

#eval testCoroutine <|
#strata
program Laurel;

composite Cell {
  var x: int
}

coroutine guaranteeOldLocalizedThirdYield(s: Cell)
  requires s#x == 0
  relies old(s#x) == s#x
  guarantees old(s#x) == s#x
  modifies *
{
  yield;
  yield;
  s#x := 7;
  yield;
//^^^^^ error: coroutine yield: guarantee does not hold
  yield
};
#end
