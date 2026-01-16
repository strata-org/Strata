/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Core.Verifier

---------------------------------------------------------------------
namespace Strata

def unreachableAssertPgm :=
#strata
program Core;
procedure R() returns ()
{
  var x : int, y : int;
  var z : bool;
  assume [z_false]: (z == false);
  if (z == false) {
    y := x;
    assert [x_eq_y_internal]: (x == y);
  } else {
    assert [unreachable]: (false);
  }
  assert [x_eq_y]: (x == y);
};
#end

/--
info: [Strata.Core] Type checking succeeded.


VCs:
Label: x_eq_y_internal
Property: assert
Assumptions:
(<label_ite_cond_true: (z == #false)>, (init_z_2 == #false))
(z_false, (init_z_2 == #false))

Proof Obligation:
#true

Label: unreachable
Property: assert
Assumptions:
(<label_ite_cond_false: !(z == #false)>, (if (init_z_2 == #false) then #false else #true))
(z_false, (init_z_2 == #false))

Proof Obligation:
#false

Label: x_eq_y
Property: assert
Assumptions:
(z_false, (init_z_2 == #false))
(<label_ite_cond_true: (z == #false)>, (if (init_z_2 == #false) then (init_z_2 == #false) else #true)) (<label_ite_cond_false: !(z == #false)>, (if (if (init_z_2 == #false) then #false else #true) then (if (init_z_2 == #false) then #false else #true) else #true))

Proof Obligation:
(init_x_0 == (if (init_z_2 == #false) then init_x_0 else init_y_1))

---
info:
Obligation: x_eq_y_internal
Property: assert
Result: ✅ pass

Obligation: unreachable
Property: assert
Result: ✅ pass

Obligation: x_eq_y
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval verify "cvc5" unreachableAssertPgm

---------------------------------------------------------------------
