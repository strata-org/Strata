/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Core.Verifier

---------------------------------------------------------------------
namespace Strata

def assertionNames :=
#strata
program Core;
procedure Test(x : int) returns ()
spec {
  requires x == 1;
}
{
  assert x == 1;
};
#end

-- Translation from DDM AST to Strata Core AST

/-- info: true -/
#guard_msgs in
-- No errors in translation.
#eval TransM.run Inhabited.default (translateProgram assertionNames) |>.snd |>.isEmpty

/--
info: procedure Test :  ((x : int)) → ()
  modifies: []
  preconditions: (Test_requires_0, ((x : int) == #1))
  postconditions: 
{
  {
    assert [assert_0] ((x : int) == #1)
  }
}
Errors: #[]
-/
#guard_msgs in
#eval TransM.run Inhabited.default (translateProgram assertionNames)

/--
info: [Strata.Core] Type checking succeeded.


VCs:
Label: assert_0
Property: assert
Assumptions:
(Test_requires_0, ($__x0 == #1))

Proof Obligation:
($__x0 == #1)

---
info:
Obligation: assert_0
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval verify assertionNames

---------------------------------------------------------------------
