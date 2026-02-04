/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Core.Verifier

---------------------------------------------------------------------
namespace Strata

def smalltest :=
#strata
program Core;


datatype Any () {
  from_bool (as_bool : bool)
};

procedure test () returns ()
{
  var b: bool;
  havoc b;
  assert [constr_destr_cancel]: Any..isfrom_bool(from_bool(b));
};

#end

/-- info: [Strata.Core] Type checking succeeded.


VCs:
Label: constr_destr_cancel
Property: assert
Assumptions:


Proof Obligation:
#true

---
info:
Obligation: constr_destr_cancel
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval verify "cvc5" smalltest

end Strata
