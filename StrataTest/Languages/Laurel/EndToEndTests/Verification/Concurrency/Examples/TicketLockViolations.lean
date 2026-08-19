/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

/-
Negative sanity tests for the ticket lock under the YieldElim rely/guarantee pass.

  * **Guarantee violation** — body writes `nowServing` during the
    spin. The guarantee says it stays put across my step; the
    synthesized assert at the next yield fails.

  * **Rely violation** — drop the no-overshoot rely. Env may now
    advance `nowServing` past `myTicket`, so the spin invariant fails
    to inductively hold across the env havoc.
-/

import StrataTest.Languages.Laurel.EndToEndTests.Verification.Concurrency.CoroutineTest

open StrataTest.Util.Concurrency

#eval testCoroutine <|
#strata
program Laurel;

composite TLState {
  var nowServing: int
}

coroutine ticketLockGuaranteeBad(s: TLState, myTicket: int)
  requires myTicket >= s#nowServing

  relies old(s#nowServing) <= s#nowServing
  relies (old(s#nowServing) <= myTicket) ==> (s#nowServing <= myTicket)

  guarantees old(s#nowServing) == s#nowServing
  modifies *
{
  s#nowServing := s#nowServing + 1;
  yield
//^^^^^ error: coroutine yield: guarantee could not be proved
};
#end

#eval testCoroutine <|
#strata
program Laurel;

composite TLState {
  var nowServing: int
}

coroutine ticketLockReliesBad(s: TLState, myTicket: int)
  requires myTicket >= s#nowServing

  relies old(s#nowServing) <= s#nowServing

  guarantees old(s#nowServing) == s#nowServing
//           ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ error: coroutine exit: guarantee could not be proved
  modifies *
{
  while (myTicket > s#nowServing)
    invariant myTicket >= s#nowServing
//            ^^^^^^^^^^^^^^^^^^^^^^^^ error: assertion could not be proved
  {
    yield
//  ^^^^^ error: coroutine yield: guarantee could not be proved
  }
};
#end
