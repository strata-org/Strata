/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

/-
Negative sanity tests for the Peterson YieldElim path: the framework
must reject programs that violate the declared rely/guarantee.

  * **Guarantee violation** — body writes the other thread's flag.
    Fails at the next `yield`'s synthesized assert.

  * **Rely violation** — body uses a fact across a yield that the
    declared relies don't preserve. Fails at the user-written
    `assert` downstream of the yield.
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

coroutine petersonGuaranteeBad(s: Shared, me: int)
  requires me == 0 | me == 1

  relies   (me == 0) ==> (old(s#flag0) == s#flag0)
  relies   (me == 1) ==> (old(s#flag1) == s#flag1)

  guarantees (me == 0) ==> (old(s#flag1) == s#flag1)
  guarantees (me == 1) ==> (old(s#flag0) == s#flag0)
  modifies *
{
  if me == 0 then { s#flag1 := true } else { s#flag0 := true };
  yield
//^^^^^ error: coroutine yield: guarantee could not be proved
};
#end

#eval testCoroutine <|
#strata
program Laurel;

composite Shared {
  var flag0: bool
  var flag1: bool
  var turn:  int
}

coroutine petersonReliesBad(s: Shared, me: int)
  requires me == 0 | me == 1

  relies   (me == 0) ==> (old(s#flag0) == s#flag0)
  relies   (me == 1) ==> (old(s#flag1) == s#flag1)

  guarantees (me == 0) ==> (old(s#flag1) == s#flag1)
  guarantees (me == 1) ==> (old(s#flag0) == s#flag0)
  modifies *
{
  if me == 0 then { s#turn := 1 } else { s#turn := 0 };
  yield;
  assert (me == 0) ==> s#turn == 1
//^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ error: assertion could not be proved
};
#end
