/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Core.Verifier

---------------------------------------------------------------------
namespace Strata

def testerEx :=
#strata
program Core;


datatype Any () {
  from_bool (as_bool : bool)
};

procedure test () returns ()
{
  var b: bool;
  havoc b;
  assert [constr_tester_cancel]: Any..isfrom_bool(from_bool(b));
};

#end

/-- info: [Strata.Core] Type checking succeeded.


VCs:
Label: constr_tester_cancel
Property: assert
Assumptions:


Proof Obligation:
#true

---
info:
Obligation: constr_tester_cancel
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval verify testerEx


def destrEx :=
#strata
program Core;


datatype Any () {
  from_bool (as_bool : bool)
};

procedure test () returns ()
{
  var b: bool;
  havoc b;
  assume (b == true);
  assert [constr_destr_cancel]: Any..as_bool(from_bool(b));
};

#end

/-- info: [Strata.Core] Type checking succeeded.


VCs:
Label: assert_constr_destr_cancel_calls_Any..as_bool_0
Property: assert
Assumptions:
(assume_0, ($__b0 == #true))

Proof Obligation:
#true

Label: constr_destr_cancel
Property: assert
Assumptions:
(assume_0, ($__b0 == #true))

Proof Obligation:
$__b0

---
info:
Obligation: assert_constr_destr_cancel_calls_Any..as_bool_0
Property: assert
Result: ✅ pass

Obligation: constr_destr_cancel
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval verify destrEx

end Strata
