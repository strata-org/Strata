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
Obligation:
forall __q0 : int :: !(__q0 == __q0 + 1)

Label: good
Property: assert
Obligation:
forall __q0 : int :: exists __q1 : int :: $__x0 + 1 + (__q1 + __q0) == __q0 + (__q1 + ($__x0 + 1))

Label: bad
Property: assert
Obligation:
forall __q0 : int :: __q0 < $__x0



Result: Obligation: bad
Property: assert
Result: ❌ fail
Model:
($__x0, 0)


[DEBUG] Evaluated program:
procedure Test (x : int) returns (r : int)
spec {
  ensures [good]: forall __q0 : int :: exists __q1 : int :: r + (__q1 + __q0) == __q0 + (__q1 + r);
  ensures [bad]: forall __q0 : int :: __q0 < x;
  } {
  assert [good_assert]: forall __q0 : ($__unknown_type) :: !(__q0 == __q0 + 1);
  r := $__x0 + 1;
  assert [good]: forall __q0 : ($__unknown_type) :: exists __q1 : ($__unknown_type) :: $__x0 + 1 + (__q1 + __q0) == __q0 + (__q1 + ($__x0 + 1));
  assert [bad]: forall __q0 : ($__unknown_type) :: __q0 < $__x0;
  };

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
#eval verify quantPgm (options := .default)

/--
info: [Strata.Core] Type checking succeeded.


VCs:
Label: trigger_assert
Property: assert
Assumptions:
f_pos: forall __q0 : int ::  { f(__q0) }
  f(__q0) > 0
g_neg: forall __q0 : int :: forall __q1 : int ::  { g(__q0, __q1) }
  __q0 > 0 ==> g(__q0, __q1) < 0
f_and_g: forall __q0 : int :: forall __q1 : int ::  { g(__q0, __q1), f(__q0) }
  g(__q0, __q1) < f(__q0)
f_and_g2: forall __q0 : int :: forall __q1 : int ::  { g(__q0, __q1), f(__q0) }
  g(__q0, __q1) < f(__q0)
Obligation:
f($__x0) > 0

Label: multi_trigger_assert
Property: assert
Assumptions:
f_pos: forall __q0 : int ::  { f(__q0) }
  f(__q0) > 0
g_neg: forall __q0 : int :: forall __q1 : int ::  { g(__q0, __q1) }
  __q0 > 0 ==> g(__q0, __q1) < 0
f_and_g: forall __q0 : int :: forall __q1 : int ::  { g(__q0, __q1), f(__q0) }
  g(__q0, __q1) < f(__q0)
f_and_g2: forall __q0 : int :: forall __q1 : int ::  { g(__q0, __q1), f(__q0) }
  g(__q0, __q1) < f(__q0)
Obligation:
forall __q0 : int :: g($__x0, __q0) < f($__x0)

Label: f_and_g
Property: assert
Assumptions:
f_pos: forall __q0 : int ::  { f(__q0) }
  f(__q0) > 0
g_neg: forall __q0 : int :: forall __q1 : int ::  { g(__q0, __q1) }
  __q0 > 0 ==> g(__q0, __q1) < 0
f_and_g: forall __q0 : int :: forall __q1 : int ::  { g(__q0, __q1), f(__q0) }
  g(__q0, __q1) < f(__q0)
f_and_g2: forall __q0 : int :: forall __q1 : int ::  { g(__q0, __q1), f(__q0) }
  g(__q0, __q1) < f(__q0)
Obligation:
g(f($__x0), $__x0) < 0

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
#eval verify triggerPgm
