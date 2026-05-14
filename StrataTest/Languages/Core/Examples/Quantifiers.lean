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
forall l : int :: !(l == l + 1)

Label: good
Property: assert
Obligation:
forall y : int :: exists z : int :: $__x0 + 1 + (z + y) == y + (z + ($__x0 + 1))

Label: bad
Property: assert
Obligation:
forall q : int :: q < $__x0



Result: Obligation: bad
Property: assert
Result: ❌ fail
Model:
($__x0, 0)


[DEBUG] Evaluated program:
procedure Test (x : int) returns (r : int)
spec {
  ensures [good]: forall y : int :: exists z : int :: r + (z + y) == y + (z + r);
  ensures [bad]: forall q : int :: q < x;
  } {
  assert [good_assert]: forall l : ($__unknown_type) :: !(l == l + 1);
  r := $__x0 + 1;
  assert [good]: forall y : ($__unknown_type) :: exists z : ($__unknown_type) :: $__x0 + 1 + (z + y) == y + (z + ($__x0 + 1));
  assert [bad]: forall q : ($__unknown_type) :: q < $__x0;
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
f_pos: forall x : int ::  { f(x) }
  f(x) > 0
g_neg: forall x : int :: forall y : int ::  { g(x, y) }
  x > 0 ==> g(x, y) < 0
f_and_g: forall x : int :: forall y : int ::  { g(x, y), f(x) }
  g(x, y) < f(x)
f_and_g2: forall x : int :: forall y : int ::  { g(x, y), f(x) }
  g(x, y) < f(x)
Obligation:
f($__x0) > 0

Label: multi_trigger_assert
Property: assert
Assumptions:
f_pos: forall x : int ::  { f(x) }
  f(x) > 0
g_neg: forall x : int :: forall y : int ::  { g(x, y) }
  x > 0 ==> g(x, y) < 0
f_and_g: forall x : int :: forall y : int ::  { g(x, y), f(x) }
  g(x, y) < f(x)
f_and_g2: forall x : int :: forall y : int ::  { g(x, y), f(x) }
  g(x, y) < f(x)
Obligation:
forall y : int :: g($__x0, y) < f($__x0)

Label: f_and_g
Property: assert
Assumptions:
f_pos: forall x : int ::  { f(x) }
  f(x) > 0
g_neg: forall x : int :: forall y : int ::  { g(x, y) }
  x > 0 ==> g(x, y) < 0
f_and_g: forall x : int :: forall y : int ::  { g(x, y), f(x) }
  g(x, y) < f(x)
f_and_g2: forall x : int :: forall y : int ::  { g(x, y), f(x) }
  g(x, y) < f(x)
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
