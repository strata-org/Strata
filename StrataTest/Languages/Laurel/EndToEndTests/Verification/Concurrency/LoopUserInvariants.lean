/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

/-
Direct VCG does not auto-inject per-yield guarantees as loop
invariants. The user writes them explicitly using the surface form
`oldGuarantee(...)`, which the pass lowers to a read against the
internal snapshot variable `$h_yield_prev`. The symmetric
`oldRelies(...)` is available for rely-side invariants.

This file pins three cases:

  * **(1) Yields-last, explicit invariant — verifies.** Body
    `body; yield` with `oldGuarantee` invariant carries the
    snapshot relationship across iterations.

  * **(2) Yields-not-last — invariant fails at back-edge.** Body
    `yield; tail` where `tail` mutates state the invariant
    constrains. The invariant fails at the loop back-edge before
    exit. User-facing guidance: prefer `body; yield` ordering, or
    weaken the invariant to one the back-edge state still
    satisfies.

  * **(3) Missing invariant — rejected.** If the user forgets the
    `oldGuarantee` invariant on a yield-containing loop, the
    post-iteration yield's assert fails because the loop head
    havoced the snapshot relationship.
-/

import StrataTest.Languages.Laurel.EndToEndTests.Verification.Concurrency.CoroutineTest

open StrataTest.Util.Concurrency

/-! ## (1) Explicit `oldGuarantee` invariant — verifies. -/

#eval testCoroutine <|
#strata
program Laurel;

composite Cell { var x: int }

coroutine writeThenYieldExplicit(s: Cell)
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

/-! ## (2) Yield-then-write-then-exit — back-edge invariant fails.

   The body's tail (`s#x := 1`) breaks the only obvious snapshot
   invariant (`oldGuarantee(s#x) == s#x`) at the loop back-edge.
   The Boogie while rule havocs the snapshot at the loop head, so
   the next yield's assert needs *some* invariant relating
   `$h_yield_prev` to `$heap` — but the user-written candidate
   fails to be inductive across the back-edge. To verify, the user
   must either:
     (a) restructure to put yield last (T9 style); or
     (b) weaken the invariant to one preserved at the back-edge.

   We pin the back-edge invariant failure here so the trade-off
   is documented in test form. -/

#eval testCoroutine <|
#strata
program Laurel;

composite Cell { var x: int }

coroutine yieldThenWriteExits(s: Cell)
  requires s#x == 0
  relies     old(s#x) == s#x
  guarantees old(s#x) == s#x
  modifies *
{
  while (s#x < 1)
    invariant oldGuarantee(s#x) == s#x
//            ^^^^^^^^^^^^^^^^^^^^^^^^ error: assertion could not be proved
  {
    yield;
    s#x := 1
  }
};
#end

/-! ## (3) Missing invariant — second-yield assert fails.

   `incMonotonic`-style body, but without the `oldGuarantee`
   invariant. The first yield discharges trivially (the loop just
   started — `$h_yield_prev` was set to procedure-entry `$heap`).
   But after one iteration, the loop havocs `$h_yield_prev`, so the
   next yield's `assert old(s#x) <= s#x` (= `$h_yield_prev #x <=
   $heap #x`) has no fact to discharge.

   Same missing fact fails the exit guarantee: at loop exit only
   `invariant s#x >= 0` survives, which does not relate
   `$h_yield_prev` to `$heap`. So both the yield and the exit pin
   fail, from the one missing `oldGuarantee` invariant. -/

#eval testCoroutine <|
#strata
program Laurel;

composite Cell { var x: int }

coroutine incMonotonicMissingInvariant(s: Cell)
  requires s#x == 0
  relies     old(s#x) <= s#x
  guarantees old(s#x) <= s#x
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
