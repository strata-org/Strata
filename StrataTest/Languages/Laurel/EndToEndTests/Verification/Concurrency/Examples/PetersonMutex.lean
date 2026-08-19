/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

/-
Mutual exclusion for Peterson, expressed as an inline `assert` at the
critical-section entry. Each thread proves its own half:

  me==0 — right before `s#cs0 := true`, assert `!s#cs1`.
  me==1 — right before `s#cs1 := true`, assert `!s#cs0`.

By symmetry the two halves give the full mutex theorem `!(cs0 & cs1)`.

Non-interference is encoded by hand as part of each thread's rely:
me==0 assumes me==1 maintains the protocol invariant
`cs1 ==> (flag1 & (!flag0 | turn==1))`, and symmetrically establishes
the dual as its own guarantee. The v2 non-interference VC pass would
generate this rely automatically from the other thread's guarantee.

The bound `turn==0 | turn==1` is maintained as a free rely/guarantee so
the guarantee at the post-CS-entry yield can close
`!flag1 | turn==0` from the busy-wait exit fact `!(flag1 & turn==1)`.
-/

import StrataTest.Languages.Laurel.EndToEndTests.Verification.Concurrency.CoroutineTest

open StrataTest.Util.Concurrency

#eval testCoroutine <|
#strata
program Laurel;

composite Shared {
  var flag0: bool
  var flag1: bool
  var turn:  int
  var cs0:   bool
  var cs1:   bool
}

coroutine peterson(s: Shared, me: int)
  requires me == 0 | me == 1
  requires (me == 0 & !s#flag0 & !s#cs0) | (me == 1 & !s#flag1 & !s#cs1)
  requires s#turn == 0 | s#turn == 1

  // Frame relies: env doesn't touch my fields.
  relies (me == 0) ==> (old(s#flag0) == s#flag0)
  relies (me == 1) ==> (old(s#flag1) == s#flag1)
  relies (me == 0) ==> (old(s#cs0) == s#cs0)
  relies (me == 1) ==> (old(s#cs1) == s#cs1)
  // Turn stays in {0,1}.
  relies s#turn == 0 | s#turn == 1
  // Non-interference: env (other thread) maintains its protocol invariant.
  relies (me == 0) ==> (s#cs1 ==> (s#flag1 & (!s#flag0 | s#turn == 1)))
  relies (me == 1) ==> (s#cs0 ==> (s#flag0 & (!s#flag1 | s#turn == 0)))

  // Frame guarantees.
  guarantees (me == 0) ==> (old(s#flag1) == s#flag1)
  guarantees (me == 1) ==> (old(s#flag0) == s#flag0)
  guarantees (me == 0) ==> (old(s#cs1) == s#cs1)
  guarantees (me == 1) ==> (old(s#cs0) == s#cs0)
  guarantees s#turn == 0 | s#turn == 1
  // Protocol guarantee: I maintain my half of the invariant.
  guarantees (me == 0) ==> (s#cs0 ==> (s#flag0 & (!s#flag1 | s#turn == 0)))
  guarantees (me == 1) ==> (s#cs1 ==> (s#flag1 & (!s#flag0 | s#turn == 1)))
  modifies *
{
  if me == 0 then { s#flag0 := true } else { s#flag1 := true };
  yield;
  if me == 0 then { s#turn := 1 } else { s#turn := 0 };
  yield;
  while ( (me == 0 & s#flag1 & s#turn == 1)
        | (me == 1 & s#flag0 & s#turn == 0) )
    // Per-yield guarantee carried through the loop head.
    invariant (me == 0) ==> (oldGuarantee(s#flag1) == s#flag1)
    invariant (me == 1) ==> (oldGuarantee(s#flag0) == s#flag0)
    invariant (me == 0) ==> (oldGuarantee(s#cs1) == s#cs1)
    invariant (me == 1) ==> (oldGuarantee(s#cs0) == s#cs0)
    // Local protocol facts.
    invariant (me == 0) ==> s#flag0
    invariant (me == 1) ==> s#flag1
    invariant (me == 0) ==> !s#cs0
    invariant (me == 1) ==> !s#cs1
    invariant s#turn == 0 | s#turn == 1
    invariant (me == 0) ==> (s#cs1 ==> (s#flag1 & (!s#flag0 | s#turn == 1)))
    invariant (me == 1) ==> (s#cs0 ==> (s#flag0 & (!s#flag1 | s#turn == 0)))
  {
    yield
  };
  if me == 0 then { s#cs0 := true } else { s#cs1 := true };
  // Non-vacuous mutex: I just set my cs to true, so this requires
  // the other thread's cs to be false. Same proof obligation as the
  // split `me == 0 ==> !s#cs1` and `me == 1 ==> !s#cs0`.
  assert !(s#cs0 & s#cs1);
  yield;
  if me == 0 then { s#cs0 := false } else { s#cs1 := false };
  yield;
  if me == 0 then { s#flag0 := false } else { s#flag1 := false }
};
#end
