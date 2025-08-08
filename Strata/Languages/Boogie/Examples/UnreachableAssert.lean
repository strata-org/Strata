/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Boogie.Verifier

---------------------------------------------------------------------
namespace Strata

def unreachableAssertEnv : Program :=
#strata
program Boogie;
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
info: [Strata.Boogie] Type checking succeeded.


VCs:
Label: x_eq_y_internal
Assumptions:
(<label_ite_cond_true: (z == #false)>, (init_z_2 == #false))
(z_false, (init_z_2 == #false))
Proof Obligation:
#true

Label: unreachable
Assumptions:
(<label_ite_cond_false: !(z == #false)>, (if (init_z_2 == #false) then #false else #true))
(z_false, (init_z_2 == #false))
Proof Obligation:
#false

Label: x_eq_y
Assumptions:
(z_false, (init_z_2 == #false))
(<label_ite_cond_true: (z == #false)>, (if (init_z_2 == #false) then (init_z_2 == #false) else #true)) (<label_ite_cond_false: !(z == #false)>, (if (if (init_z_2 == #false) then #false else #true) then (if (init_z_2 == #false) then #false else #true) else #true))
Proof Obligation:
(init_x_0 == (if (init_z_2 == #false) then init_x_0 else init_y_1))

Wrote problem to vcs/x_eq_y_internal.smt2.
Wrote problem to vcs/unreachable.smt2.
Wrote problem to vcs/x_eq_y.smt2.
---
info:
Obligation: x_eq_y_internal
Result: verified

Obligation: unreachable
Result: verified

Obligation: x_eq_y
Result: verified
-/
#guard_msgs in
#eval verify "cvc5" unreachableAssertEnv

---------------------------------------------------------------------
