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

/-

info: [Strata.Core] Type checking succeeded.
-/
#guard_msgs in
#eval verify "cvc5" quantPgm (options := .default)

/-

info: [Strata.Core] Type checking succeeded.
-/
#guard_msgs in
#eval verify "cvc5" triggerPgm
