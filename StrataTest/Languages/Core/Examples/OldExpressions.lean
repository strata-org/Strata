/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Core.Verifier

---------------------------------------------------------------------
namespace Strata

def oldExprPgm : Program :=
#strata
program Core;
var g : bool;
var g2 : bool;

procedure T1() returns (y : bool, z : bool)
spec {
  modifies g2;
  ensures  [T1_g_unchanged]: (g == old(g));
  ensures  [T1_g2_eq_old_g]: (g2 == old(g));
  ensures  [T1_y_eq_old_g2]: (y == old(g2));
  ensures  [T1_z_eq_y]:      (z == old(y));
}
{
  y := old(g2);
  g2 := old(g);
  z := old(g);
  assert [T1_z_eq_g]: (z == g);
  z := old(g2);
  assert [T1_z_eq_old_g2]: (z == old(g2));
};

procedure T2 () returns ()
spec {
  modifies g;
  modifies g2;
}
{
  var a : bool, b : bool;
  g := true;
  g2 := false;
  call a, b := T1();
  assert [T2_g2_eq_g]:     (g2 == g);
  assert [T2_g_true]:      (g == true);
  assert [T2_a_eq_false]:  (old(a) == false);
  assert [T2_b_eq_false]:  (b == false);
};
#end

/--
info: [Strata.Core] Type checking succeeded.


VCs:
Label: T1_z_eq_g
Property: assert
Obligation:
true

Label: T1_z_eq_old_g2
Property: assert
Obligation:
true

Label: T1_g_unchanged
Property: assert
Obligation:
true

Label: T1_g2_eq_old_g
Property: assert
Obligation:
true

Label: T1_y_eq_old_g2
Property: assert
Obligation:
true

Label: T1_z_eq_y
Property: assert
Obligation:
true

Label: T2_g2_eq_g
Property: assert
Assumptions:
(Origin_T1_Ensures)T1_g_unchanged: true == true
(Origin_T1_Ensures)T1_g2_eq_old_g: $__g27 == true
(Origin_T1_Ensures)T1_y_eq_old_g2: $__a5 == false
(Origin_T1_Ensures)T1_z_eq_y: $__b6 == $__a5
Obligation:
$__g27 == true

Label: T2_g_true
Property: assert
Assumptions:
(Origin_T1_Ensures)T1_g_unchanged: true == true
(Origin_T1_Ensures)T1_g2_eq_old_g: $__g27 == true
(Origin_T1_Ensures)T1_y_eq_old_g2: $__a5 == false
(Origin_T1_Ensures)T1_z_eq_y: $__b6 == $__a5
Obligation:
true

Label: T2_a_eq_false
Property: assert
Assumptions:
(Origin_T1_Ensures)T1_g_unchanged: true == true
(Origin_T1_Ensures)T1_g2_eq_old_g: $__g27 == true
(Origin_T1_Ensures)T1_y_eq_old_g2: $__a5 == false
(Origin_T1_Ensures)T1_z_eq_y: $__b6 == $__a5
Obligation:
$__a5 == false

Label: T2_b_eq_false
Property: assert
Assumptions:
(Origin_T1_Ensures)T1_g_unchanged: true == true
(Origin_T1_Ensures)T1_g2_eq_old_g: $__g27 == true
(Origin_T1_Ensures)T1_y_eq_old_g2: $__a5 == false
(Origin_T1_Ensures)T1_z_eq_y: $__b6 == $__a5
Obligation:
$__b6 == false

---
info:
Obligation: T1_z_eq_g
Property: assert
Result: ✅ pass

Obligation: T1_z_eq_old_g2
Property: assert
Result: ✅ pass

Obligation: T1_g_unchanged
Property: assert
Result: ✅ pass

Obligation: T1_g2_eq_old_g
Property: assert
Result: ✅ pass

Obligation: T1_y_eq_old_g2
Property: assert
Result: ✅ pass

Obligation: T1_z_eq_y
Property: assert
Result: ✅ pass

Obligation: T2_g2_eq_g
Property: assert
Result: ✅ pass

Obligation: T2_g_true
Property: assert
Result: ✅ pass

Obligation: T2_a_eq_false
Property: assert
Result: ✅ pass

Obligation: T2_b_eq_false
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval verify oldExprPgm

---------------------------------------------------------------------
