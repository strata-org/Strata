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

procedure T1(inout g : bool, inout g2 : bool, out y : bool, out z : bool)
spec {
  ensures  [T1_g_unchanged]: (g == old g);
  ensures  [T1_g2_eq_old_g]: (g2 == old g);
  ensures  [T1_y_eq_old_g2]: (y == old g2);
  ensures  [T1_z_eq_y]:      (z == old g2);
}
{
  y := old g2;
  g2 := old g;
  z := old g2;
  assert [T1_z_eq_g2]: (z == old g2);
};

procedure T2 (inout g : bool, inout g2 : bool)
spec {
}
{
  var a : bool, b : bool;
  g := true;
  g2 := false;
  call T1(g, g2, out g, out g2, out a, out b);
  assert [T2_g2_eq_g]:     (g2 == g);
  assert [T2_g_true]:      (g == true);
  assert [T2_a_eq_false]:  (a == false);
  assert [T2_b_eq_false]:  (b == false);
};
#end

/--
info: [Strata.Core] Type checking succeeded.


VCs:
Label: T1_z_eq_g2
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
callElimAssume_T1_g_unchanged_8: $__g12 == true
callElimAssume_T1_g2_eq_old_g_9: $__g213 == true
callElimAssume_T1_y_eq_old_g2_10: $__a14 == false
callElimAssume_T1_z_eq_y_11: $__b15 == false
Obligation:
$__g213 == $__g12

Label: T2_g_true
Property: assert
Assumptions:
callElimAssume_T1_g_unchanged_8: $__g12 == true
callElimAssume_T1_g2_eq_old_g_9: $__g213 == true
callElimAssume_T1_y_eq_old_g2_10: $__a14 == false
callElimAssume_T1_z_eq_y_11: $__b15 == false
Obligation:
$__g12 == true

Label: T2_a_eq_false
Property: assert
Assumptions:
callElimAssume_T1_g_unchanged_8: $__g12 == true
callElimAssume_T1_g2_eq_old_g_9: $__g213 == true
callElimAssume_T1_y_eq_old_g2_10: $__a14 == false
callElimAssume_T1_z_eq_y_11: $__b15 == false
Obligation:
$__a14 == false

Label: T2_b_eq_false
Property: assert
Assumptions:
callElimAssume_T1_g_unchanged_8: $__g12 == true
callElimAssume_T1_g2_eq_old_g_9: $__g213 == true
callElimAssume_T1_y_eq_old_g2_10: $__a14 == false
callElimAssume_T1_z_eq_y_11: $__b15 == false
Obligation:
$__b15 == false

---
info:
Obligation: T1_z_eq_g2
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
