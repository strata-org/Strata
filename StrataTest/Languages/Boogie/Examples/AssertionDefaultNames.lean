/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Boogie.Verifier

---------------------------------------------------------------------
namespace Strata

def assertionNames :=
#strata
program Boogie;
procedure Test(x : int) returns ()
spec {
  requires x == 1;
}
{
  assert x == 1;
};
#end

-- Translation from DDM AST to Boogie/Strata AST

/-- info: true -/
#guard_msgs in
-- No errors in translation.
#eval TransM.run Inhabited.default (translateProgram assertionNames) |>.snd |>.isEmpty

/--
info: (procedure Test :  ((x : int)) → ())
modifies: []
preconditions: (Test_requires_0, ((x : int) == #1))
postconditions: ⏎
body: assert [assert_0] ((x : int) == #1)

Errors: #[]
-/
#guard_msgs in
#eval TransM.run Inhabited.default (translateProgram assertionNames)

/--
info: [Strata.Boogie] Type checking succeeded.


VCs:
Label: assert_0
Assumptions:
(Test_requires_0, ($__x0 == #1))

Proof Obligation:
($__x0 == #1)

Wrote problem to vcs/assert_0.smt2.
---
info:
Obligation: assert_0
Result: verified
-/
#guard_msgs in
#eval verify "z3" assertionNames

---------------------------------------------------------------------
