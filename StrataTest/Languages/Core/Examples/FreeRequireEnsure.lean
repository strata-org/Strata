/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Core.Verifier

---------------------------------------------------------------------
namespace Strata

def freeReqEnsPgm : Program :=
#strata
program Core;
procedure Proc(inout g : int)
spec {
  free requires [g_eq_15]: g == 15;
  // `g_lt_10` is not checked by this procedure.
  free ensures [g_lt_10]: g < 10;
}
{
  assert [g_gt_10_internal]: (g > 10);
  g := g + 1;
};

procedure ProcCaller (inout g : int, out x : int) {
  call Proc(g, out g);
  // Fails; `g_eq_15` requires of Proc ignored here.
  assert [g_eq_15_internal]: (g == 15);
};
#end

/--
info: [Strata.Core] Type checking succeeded.


VCs:
Label: g_gt_10_internal
Property: assert
Assumptions:
g_eq_15: $__g0 == 15
Obligation:
$__g0 > 10

Label: g_lt_10
Property: assert
Assumptions:
g_eq_15: $__g0 == 15
Obligation:
true

Label: g_eq_15_internal
Property: assert
Assumptions:
callElimAssume_g_lt_10_2: $__g5 < 10
Obligation:
$__g5 == 15

---
info:
Obligation: g_gt_10_internal
Property: assert
Result: ✅ pass

Obligation: g_lt_10
Property: assert
Result: ✅ pass

Obligation: g_eq_15_internal
Property: assert
Result: ❓ unknown
Model:
($__g5, 0) ($__g0, 0)
-/
#guard_msgs in
#eval verify freeReqEnsPgm

---------------------------------------------------------------------
