/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

meta import Strata.Languages.Core.Core
import Strata.DDM.Integration.Lean.HashCommands

meta section
---------------------------------------------------------------------
namespace Strata

def quantPgm :=
#strata
program Core;
procedure Test(x : int, out r : int)
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

procedure TestTriggers(x : int, out r : int)
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
forall y : int :: exists z : int :: x@1 + 1 + (z + y) == y + (z + (x@1 + 1))

Label: bad
Property: assert
Obligation:
forall q : int :: q < x@1

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
(x@1, 0)
-/
#guard_msgs in
#eval Core.verify quantPgm (options := .default)

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
f(x@1) > 0

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
forall y : int :: g(x@1, y) < f(x@1)

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
g(f(x@1), x@1) < 0

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
#eval Core.verify triggerPgm

end Strata
end
