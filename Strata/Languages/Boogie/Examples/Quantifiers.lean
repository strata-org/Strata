/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Boogie.Verifier

---------------------------------------------------------------------
namespace Strata

def quantEnv : Environment :=
#strata
program Boogie;
procedure Test(x : int) returns (r : int)
spec {
  ensures [good]: (forall y : int :: exists z : int :: r + (z + y) == y + (z + r));
  ensures [bad]: (forall q : int :: q < x);
}
{
  assert [good_assert]: (forall l : int :: !(l == l + 1));
  r := x + 1;
};
#end

def triggerEnv : Environment :=
#strata
program Boogie;

function f(x : int): int;
function g(x : int, y : int): int;

axiom [f_pos]: forall x : int :: { f(x) } f(x) > 0;
axiom [g_neg]: forall x : int, y : int :: { g(x, y) } x > 0 ==> g(x, y) < 0;

procedure TestTriggers(x : int) returns (r : int)
spec {
  ensures [f_and_g]: r < 0;
}
{
  assert [trigger_assert]: f(x) > 0;
  r := g(f(x), x);
};
#end

/--
info: [Strata.Boogie] Type checking succeeded.


VCs:
Label: good_assert
Assumptions:
Proof Obligation:
(∀ (~Bool.Not (%0 == ((~Int.Add %0) #1))))

Label: good
Assumptions:
Proof Obligation:
(∀ (∃ (((~Int.Add ((~Int.Add $__x0) #1)) ((~Int.Add %0) %1)) == ((~Int.Add %1) ((~Int.Add %0) ((~Int.Add $__x0) #1))))))

Label: bad
Assumptions:
Proof Obligation:
(∀ ((~Int.Lt %0) $__x0))

Wrote problem to vcs/good_assert.smt2.
Wrote problem to vcs/good.smt2.
Wrote problem to vcs/bad.smt2.


Obligation bad: could not be proved!

Result: failed
CEx: ($__x0, 0)

Evaluated program:
(procedure Test :  ((x : int)) → ((r : int)))
modifies: []
preconditions: ⏎
postconditions: (good, (∀ (∃ ((((~Int.Add : (arrow int (arrow int int))) (r : int)) (((~Int.Add : (arrow int (arrow int int))) %0) %1)) == (((~Int.Add : (arrow int (arrow int int))) %1) (((~Int.Add : (arrow int (arrow int int))) %0) (r : int))))))) (bad, (∀ (((~Int.Lt : (arrow int (arrow int bool))) %0) (x : int))))
body: assert [good_assert] (∀ (~Bool.Not (%0 == ((~Int.Add %0) #1))))
r := ((~Int.Add $__x0) #1)
assert [good] (∀ (∃ (((~Int.Add ((~Int.Add $__x0) #1)) ((~Int.Add %0) %1)) == ((~Int.Add %1) ((~Int.Add %0) ((~Int.Add $__x0) #1))))))
assert [bad] (∀ ((~Int.Lt %0) $__x0))

---
info:
Obligation: good_assert
Result: verified

Obligation: good
Result: verified

Obligation: bad
Result: failed
CEx: ($__x0, 0)
-/
#guard_msgs in
#eval verify "cvc5" quantEnv (verbose := true)

/--
info: [Strata.Boogie] Type checking succeeded.


VCs:
Label: trigger_assert
Assumptions:
(g_neg, (∀ (∀ ((~Bool.Implies ((~Int.Gt %1) #0)) ((~Int.Lt ((~g %1) %0)) #0)))))
(f_pos, (∀ ((~Int.Gt (~f %0)) #0)))
Proof Obligation:
((~Int.Gt (~f $__x0)) #0)

Label: f_and_g
Assumptions:
(g_neg, (∀ (∀ ((~Bool.Implies ((~Int.Gt %1) #0)) ((~Int.Lt ((~g %1) %0)) #0)))))
(f_pos, (∀ ((~Int.Gt (~f %0)) #0)))
Proof Obligation:
((~Int.Lt ((~g (~f $__x0)) $__x0)) #0)

Wrote problem to vcs/trigger_assert.smt2.
Wrote problem to vcs/f_and_g.smt2.
---
info:
Obligation: trigger_assert
Result: verified

Obligation: f_and_g
Result: verified
-/
#guard_msgs in
#eval verify "cvc5" triggerEnv
