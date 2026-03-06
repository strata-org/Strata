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
var g : int;
procedure Proc() returns ()
spec {
  modifies g;
  free requires [g_eq_15]: g == 15;
  // `g_lt_10` is not checked by this procedure.
  free ensures [g_lt_10]: g < 10;
}
{
  assert [g_gt_10_internal]: (g > 10);
  g := g + 1;
};

procedure ProcCaller () returns (x : int) {
  call := Proc();
  // Fails; `g_eq_15` requires of Proc ignored here.
  assert [g_eq_15_internal]: (g == 15);
};
#end

/--
info: [Strata.Core] Type checking succeeded.


Obligation (Origin_Proc_Requires)g_eq_15 is free!


VCs:
Label: g_gt_10_internal
Property: assert
Assumptions:
g_eq_15: $__g1 == 15
Obligation:
$__g1 > 10

Label: g_lt_10
Property: assert
Assumptions:
g_eq_15: $__g1 == 15
Obligation:
true

Label: g_eq_15_internal
Property: assert
Assumptions:
(Origin_Proc_Ensures)g_lt_10: $__g3 < 10
Obligation:
$__g3 == 15



Result: Obligation: g_eq_15_internal
Property: assert
Result: ❌ fail
Model:
($__g3, 0)


[DEBUG] Evaluated program:
var g : int;
procedure Proc () returns ()
spec {
  modifies g;
  free requires [g_eq_15]: g == 15;
  free ensures [g_lt_10]: g < 10;
  } {
  assume [g_eq_15]: $__g1 == 15;
  assert [g_gt_10_internal]: $__g1 > 10;
  g := $__g1 + 1;
  assert [g_lt_10]: true;
  };
procedure ProcCaller () returns (x : int)
{
  call  := Proc();
  assert [g_eq_15_internal]: $__g3 == 15;
  };

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
Result: ❌ fail
Model:
($__g3, 0)
-/
#guard_msgs in
#eval verify freeReqEnsPgm

---------------------------------------------------------------------
