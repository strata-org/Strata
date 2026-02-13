/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Core.Verifier

---------------------------------------------------------------------
namespace Strata

def quantPgm :=
#strata
program Core;
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

def triggerPgm :=
#strata
program Core;

function f(x : int): int;
function g(x : int, y : int): int;

axiom [f_pos]: forall x : int :: { f(x) } f(x) > 0;
axiom [g_neg]: forall x : int, y : int :: { g(x, y) } x > 0 ==> g(x, y) < 0;
axiom [f_and_g]: forall x : int, y : int :: { g(x, y) } { f(x) } g(x, y) < f(x);
axiom [f_and_g2]: forall x : int, y : int :: { g(x, y), f(x) } g(x, y) < f(x);

procedure TestTriggers(x : int) returns (r : int)
spec {
  ensures [f_and_g]: r < 0;
}
{
  assert [trigger_assert]: f(x) > 0;
  assert [multi_trigger_assert]: forall y : int :: g(x, y) < f(x);
  r := g(f(x), x);
};
#end

/--
info: [Strata.Core] Type checking succeeded.


VCs:
Label: good_assert
Property: assert
Assumptions:


Proof Obligation:
(∀ (~Bool.Not (%0 == (~Int.Add %0 #1))))

Label: good
Property: assert
Assumptions:


Proof Obligation:
(∀ (∃ ((~Int.Add (~Int.Add $__x0 #1) (~Int.Add %0 %1)) == (~Int.Add %1 (~Int.Add %0 (~Int.Add $__x0 #1))))))

Label: bad
Property: assert
Assumptions:


Proof Obligation:
(∀ (~Int.Lt %0 $__x0))



Result: Obligation: bad
Property: assert
Result: ❌ fail
Model:
($__x0, 0)


Evaluated program:
procedure Test :  ((x : int)) → ((r : int))
  modifies: []
  preconditions: 
  postconditions: (good, (∀ (∃ (((~Int.Add : (arrow int (arrow int int)))
      (r : int)
      ((~Int.Add : (arrow int (arrow int int)))
       %0
       %1)) == ((~Int.Add : (arrow int (arrow int int)))
      %1
      ((~Int.Add : (arrow int (arrow int int)))
       %0
       (r : int))))))) (bad, (∀ ((~Int.Lt : (arrow int (arrow int bool))) %0 (x : int))))
{
  {
    assert [good_assert] (∀ (~Bool.Not (%0 == (~Int.Add %0 #1))))
    r := (~Int.Add $__x0 #1)
    assert [good] (∀ (∃ ((~Int.Add
        (~Int.Add $__x0 #1)
        (~Int.Add %0 %1)) == (~Int.Add %1 (~Int.Add %0 (~Int.Add $__x0 #1))))))
    assert [bad] (∀ (~Int.Lt %0 $__x0))
  }
}
---
info:
Obligation: good_assert
Property: assert
Result: ✅ pass

Obligation: good
Property: assert
Result: ✅ pass

Obligation: bad
Property: assert
Result: ❌ fail
Model:
($__x0, 0)
-/
#guard_msgs in
#eval verify "cvc5" quantPgm (options := .default)

/--
info: [Strata.Core] Type checking succeeded.


VCs:
Label: trigger_assert
Property: assert
Assumptions:

(f_pos, (∀ (~Int.Gt (~f %0) #0)))
(g_neg, (∀ (∀ (~Bool.Implies
   (~Int.Gt %1 #0)
   (~Int.Lt
    (~g %1 %0)
    #0))))) (f_and_g, (∀ (∀ (~Int.Lt (~g %1 %0) (~f %1))))) (f_and_g2, (∀ (∀ (~Int.Lt (~g %1 %0) (~f %1)))))
Proof Obligation:
(~Int.Gt (~f $__x0) #0)

Label: multi_trigger_assert
Property: assert
Assumptions:

(f_pos, (∀ (~Int.Gt (~f %0) #0)))
(g_neg, (∀ (∀ (~Bool.Implies
   (~Int.Gt %1 #0)
   (~Int.Lt
    (~g %1 %0)
    #0))))) (f_and_g, (∀ (∀ (~Int.Lt (~g %1 %0) (~f %1))))) (f_and_g2, (∀ (∀ (~Int.Lt (~g %1 %0) (~f %1)))))
Proof Obligation:
(∀ (~Int.Lt (~g $__x0 %0) (~f $__x0)))

Label: f_and_g
Property: assert
Assumptions:

(f_pos, (∀ (~Int.Gt (~f %0) #0)))
(g_neg, (∀ (∀ (~Bool.Implies
   (~Int.Gt %1 #0)
   (~Int.Lt
    (~g %1 %0)
    #0))))) (f_and_g, (∀ (∀ (~Int.Lt (~g %1 %0) (~f %1))))) (f_and_g2, (∀ (∀ (~Int.Lt (~g %1 %0) (~f %1)))))
Proof Obligation:
(~Int.Lt (~g (~f $__x0) $__x0) #0)

---
info:
Obligation: trigger_assert
Property: assert
Result: ✅ pass

Obligation: multi_trigger_assert
Property: assert
Result: ✅ pass

Obligation: f_and_g
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval verify "cvc5" triggerPgm
