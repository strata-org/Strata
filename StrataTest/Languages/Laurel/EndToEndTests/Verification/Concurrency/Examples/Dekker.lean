/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

/-
Dekker's mutual-exclusion algorithm (1965): the first known software
solution to two-thread mutex, predating Peterson's by ~15 years. Like
Peterson it uses two interest flags and a `turn` arbiter, but the
arbitration discipline differs: Dekker only consults `turn` *inside*
the busy-wait, and the flag is dropped while deferring (not held).

Single parametric coroutine `dekker(s, me)` with `me ∈ {0, 1}`.
Verified compositionally via rely/guarantee under the YieldElim pass. Per-yield
guarantees: I don't touch the other thread's flag or critical-section
bit. Per-yield relies: env doesn't touch mine. Identical contract
shape to Peterson — what we're really testing here is whether the
YieldElim pass handles the *control flow* (nested `while` with a yield
in each, a flag drop/raise around the inner spin).

Both loops need user-supplied `oldGuarantee(...)` invariants so the
SMT solver can carry the snapshot relationship across iterations.
-/

import StrataTest.Languages.Laurel.EndToEndTests.Verification.Concurrency.CoroutineTest

open StrataTest.Util.Concurrency

#eval testCoroutine <|
#strata
program Laurel;

composite Shared {
  var flag0: bool   // thread 0 wants to enter CS
  var flag1: bool   // thread 1 wants to enter CS
  var turn:  int    // 0 or 1: whose turn to defer (Dekker arbitrates only inside busy-wait)
  var cs0:   bool   // ghost: thread 0 is currently in CS
  var cs1:   bool   // ghost: thread 1 is currently in CS
}

coroutine dekker(s: Shared, me: int)
  requires me == 0 | me == 1
  requires (me == 0 & !s#flag0 & !s#cs0) | (me == 1 & !s#flag1 & !s#cs1)

  // Env doesn't touch my flag.
  relies   (me == 0) ==> (old(s#flag0) == s#flag0)
  relies   (me == 1) ==> (old(s#flag1) == s#flag1)
  // Env doesn't touch my CS bit.
  relies   (me == 0) ==> (old(s#cs0) == s#cs0)
  relies   (me == 1) ==> (old(s#cs1) == s#cs1)

  // I don't touch the other thread's flag.
  guarantees (me == 0) ==> (old(s#flag1) == s#flag1)
  guarantees (me == 1) ==> (old(s#flag0) == s#flag0)
  // I don't touch the other thread's CS bit.
  guarantees (me == 0) ==> (old(s#cs1) == s#cs1)
  guarantees (me == 1) ==> (old(s#cs0) == s#cs0)
  modifies *
{
  // Express interest.
  if me == 0 then { s#flag0 := true } else { s#flag1 := true };
  // Outer busy-wait: while the other thread wants in, arbitrate via turn.
  while ( (me == 0 & s#flag1) | (me == 1 & s#flag0) )
    invariant (me == 0) ==> (oldGuarantee(s#flag1) == s#flag1)
    invariant (me == 1) ==> (oldGuarantee(s#flag0) == s#flag0)
    invariant (me == 0) ==> (oldGuarantee(s#cs1) == s#cs1)
    invariant (me == 1) ==> (oldGuarantee(s#cs0) == s#cs0)
  {
    // If it's not my turn, defer: drop my flag, wait, re-raise.
    if (me == 0 & s#turn == 1) | (me == 1 & s#turn == 0) then {
      if me == 0 then { s#flag0 := false } else { s#flag1 := false };
      // Inner spin: wait for turn to come back to me.
      while ( (me == 0 & s#turn == 1) | (me == 1 & s#turn == 0) )
        invariant (me == 0) ==> (oldGuarantee(s#flag1) == s#flag1)
        invariant (me == 1) ==> (oldGuarantee(s#flag0) == s#flag0)
        invariant (me == 0) ==> (oldGuarantee(s#cs1) == s#cs1)
        invariant (me == 1) ==> (oldGuarantee(s#cs0) == s#cs0)
      {
        yield
      };
      // Turn is mine — re-raise interest and re-check outer condition.
      if me == 0 then { s#flag0 := true } else { s#flag1 := true }
    } else {
      // Holding my flag, waiting for the other to drop theirs.
      yield
    }
  };
  // Enter the critical section.
  if me == 0 then { s#cs0 := true } else { s#cs1 := true };
  yield;
  // Leave the critical section.
  if me == 0 then { s#cs0 := false } else { s#cs1 := false };
  yield;
  // Hand off `turn` and release interest.
  if me == 0 then { s#turn := 1 } else { s#turn := 0 };
  if me == 0 then { s#flag0 := false } else { s#flag1 := false }
};
#end
