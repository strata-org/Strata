/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

/-
Negative sanity tests for Dekker under the YieldElim rely/guarantee pass.

  * **Guarantee violation** — body sets the other thread's flag during
    the busy-wait loop. Fails at the inner `yield`'s synthesized assert.

  * **Rely violation** — body asserts that the *other* thread's flag is
    unchanged across a yield, which the rely doesn't preserve (the rely
    only constrains my own flag).
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
}

coroutine dekkerGuaranteeBad(s: Shared, me: int)
  requires me == 0 | me == 1

  relies   (me == 0) ==> (old(s#flag0) == s#flag0)
  relies   (me == 1) ==> (old(s#flag1) == s#flag1)

  guarantees (me == 0) ==> (old(s#flag1) == s#flag1)
//           ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ error: coroutine exit: guarantee could not be proved
  guarantees (me == 1) ==> (old(s#flag0) == s#flag0)
  modifies *
{
  if me == 0 then { s#flag0 := true } else { s#flag1 := true };
  while ( (me == 0 & s#flag1) | (me == 1 & s#flag0) )
  {
    if me == 0 then { s#flag1 := false } else { s#flag0 := false };
    yield
//  ^^^^^ error: coroutine yield: guarantee could not be proved
  }
};
#end

#eval testCoroutine <|
#strata
program Laurel;

composite Shared {
  var flag0: bool
  var flag1: bool
}

coroutine dekkerReliesBad(s: Shared, me: int)
  requires me == 0 | me == 1

  relies   (me == 0) ==> (old(s#flag0) == s#flag0)
  relies   (me == 1) ==> (old(s#flag1) == s#flag1)

  guarantees (me == 0) ==> (old(s#flag1) == s#flag1)
  guarantees (me == 1) ==> (old(s#flag0) == s#flag0)
  modifies *
{
  yield;
  assert (me == 0) ==> !s#flag1
//^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ error: assertion could not be proved
};
#end
