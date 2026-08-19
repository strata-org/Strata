/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

/-
Peterson's mutual-exclusion algorithm, single parametric coroutine
`peterson(s, me)` with `me ∈ {0, 1}`. Verified via the YieldElim rely/guarantee pass.

The `while` busy-wait contains a yield, so the user must add loop
invariants that mirror the per-yield guarantee: without them, the
loop-head havoc loses the snapshot relationship between
`$h_yield_prev` and `$heap`, and the next yield's assert cannot
discharge.
-/

import StrataTest.Languages.Laurel.EndToEndTests.Verification.Concurrency.CoroutineTest

open StrataTest.Util.Concurrency

#eval testCoroutine <|
#strata
program Laurel;

composite Shared {
  var flag0: bool   // thread 0 wants to enter CS
  var flag1: bool   // thread 1 wants to enter CS
  var turn:  int    // 0 or 1: whose turn to defer
  var cs0:   bool   // ghost: thread 0 is currently in CS
  var cs1:   bool   // ghost: thread 1 is currently in CS
}

coroutine peterson(s: Shared, me: int)
  requires me == 0 | me == 1
  requires (me == 0 & !s#flag0 & !s#cs0) | (me == 1 & !s#flag1 & !s#cs1)

  // Env doesn't touch my flag or my CS bit.
  relies   (me == 0) ==> (old(s#flag0) == s#flag0)
  relies   (me == 1) ==> (old(s#flag1) == s#flag1)
  relies   (me == 0) ==> (old(s#cs0) == s#cs0)
  relies   (me == 1) ==> (old(s#cs1) == s#cs1)

  // I don't touch the other thread's flag or its CS bit.
  guarantees (me == 0) ==> (old(s#flag1) == s#flag1)
  guarantees (me == 1) ==> (old(s#flag0) == s#flag0)
  guarantees (me == 0) ==> (old(s#cs1) == s#cs1)
  guarantees (me == 1) ==> (old(s#cs0) == s#cs0)
  modifies *
{
  if me == 0 then { s#flag0 := true } else { s#flag1 := true };
  yield;
  if me == 0 then { s#turn := 1 } else { s#turn := 0 };
  yield;
  // Loop invariants: the user threads the guarantee through the
  // loop head manually using `oldGuarantee(...)`. Auto-injection is
  // intentionally absent — see LoopUserInvariants.
  while ( (me == 0 & s#flag1 & s#turn == 1)
        | (me == 1 & s#flag0 & s#turn == 0) )
    invariant (me == 0) ==> (oldGuarantee(s#flag1) == s#flag1)
    invariant (me == 1) ==> (oldGuarantee(s#flag0) == s#flag0)
    invariant (me == 0) ==> (oldGuarantee(s#cs1) == s#cs1)
    invariant (me == 1) ==> (oldGuarantee(s#cs0) == s#cs0)
  {
    yield
  };
  if me == 0 then { s#cs0 := true } else { s#cs1 := true };
  yield;
  if me == 0 then { s#cs0 := false } else { s#cs1 := false };
  yield;
  if me == 0 then { s#flag0 := false } else { s#flag1 := false }
};
#end
