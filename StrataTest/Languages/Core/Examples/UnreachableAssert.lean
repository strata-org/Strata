/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

meta import Strata.Languages.Core
import StrataDDM.Integration.Lean.HashCommands

meta section
---------------------------------------------------------------------
namespace Strata

def unreachableAssertPgm :=
#strata
program Core;
procedure R()
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
<label_ite_cond_true: z == false>: z@1 == false
z_false: z@1 == false
Obligation:
true

Label: unreachable
Property: assert
Assumptions:
<label_ite_cond_false: !(z == false)>: if z@1 == false then false else true
z_false: z@1 == false
Obligation:
false

Label: x_eq_y
Property: assert
Assumptions:
z_false: z@1 == false
<label_ite_cond_true: z == false>: if z@1 == false then z@1 == false else true
<label_ite_cond_false: !(z == false)>: if if z@1 == false then false else true then if z@1 == false then false else true else true
Obligation:
x@1 == (if z@1 == false then x@1 else y@1)

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
#eval Core.verify unreachableAssertPgm

end Strata
end
---------------------------------------------------------------------
