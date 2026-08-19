/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

/-
Ticket lock — one client, framed *after* fetch and *with* release.

The fetch step is modeled as a precondition (`myTicket >= s#nowServing`,
i.e. "I hold a valid ticket"). Fetch atomicity is out of scope for a
single-coroutine model; encoding it would need either a separate
`fetchTicket` procedure or atomic-block primitives, both v2+ work.

What this single-client procedure verifies:

  1. **Spin termination semantics**: after the loop, `s#nowServing == myTicket`,
     i.e. the lock is mine. The user threads the per-yield guarantee
     through the loop head via `oldGuarantee(s#nowServing) <= s#nowServing`.

  2. **Release correctness**: on release I advance `nowServing` from
     `myTicket` to `myTicket + 1`, and this advance satisfies my
     guarantee that I only ever push `nowServing` forward. The release
     would be observed by other clients as a one-step advance — the
     dual of their no-overshoot rely.

  3. **No-overshoot rely**: env may advance `nowServing` but never past
     `myTicket` while I'm waiting. This is what makes the spin invariant
     `myTicket >= s#nowServing` inductive across env steps. A v2 non-
     interference VC pass would *derive* this rely from another
     client's guarantee that says "I release only my own ticket and
     advance nowServing by exactly 1".
-/

import StrataTest.Languages.Laurel.EndToEndTests.Verification.Concurrency.CoroutineTest

open StrataTest.Util.Concurrency

#eval testCoroutine <|
#strata
program Laurel;

composite TLState {
  var nowServing: int
}

coroutine ticketClient(s: TLState, myTicket: int)
  // I hold a valid ticket.
  requires myTicket >= s#nowServing

  // Env: nowServing only advances (other clients releasing), and
  // never past my ticket while I'm still waiting. Together these
  // make the spin's loop invariant inductive.
  relies old(s#nowServing) <= s#nowServing
  relies (old(s#nowServing) <= myTicket) ==> (s#nowServing <= myTicket)

  // I only advance nowServing — never rewind. At every yield except
  // the release-step's, I haven't touched nowServing. At release I
  // advance by 1.
  guarantees old(s#nowServing) <= s#nowServing
  modifies *
{
  // Spin until served. The `oldGuarantee` invariant mirrors the
  // procedure's guarantee `old(s#nowServing) <= s#nowServing` so the
  // SMT solver can carry the snapshot relationship across iterations.
  while (s#nowServing < myTicket)
    invariant myTicket >= s#nowServing
    invariant oldGuarantee(s#nowServing) <= s#nowServing
  {
    yield
  };
  // The lock is mine.
  assert s#nowServing == myTicket;
  // Critical section (one yield to mark the boundary).
  yield;
  assert s#nowServing == myTicket;
  // Release: advance nowServing by exactly 1.
  s#nowServing := myTicket + 1
};
#end
