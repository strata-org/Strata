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
<label_ite_cond_true: (z == #false)>: $__z2 == false
z_false: $__z2 == false
Obligation:
true

Label: unreachable
Property: assert
Assumptions:
<label_ite_cond_false: !(z == #false)>: if $__z2 == false then false else true
z_false: $__z2 == false
Obligation:
false

Label: x_eq_y
Property: assert
Assumptions:
z_false: $__z2 == false
<label_ite_cond_true: (z == #false)>: if $__z2 == false then ($__z2 == false) else true
<label_ite_cond_false: !(z == #false)>: if if $__z2 == false then false else true then if $__z2 == false then false else true else true
Obligation:
$__x0 == if $__z2 == false then $__x0 else $__y1

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
#eval verify unreachableAssertPgm

---------------------------------------------------------------------
