/-
  Copyright Strata Contributors

  Licensed under the Apache License, Version 2.0 (the "License");
  you may not use this file except in compliance with the License.
  You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

  Unless required by applicable law or agreed to in writing, software
  distributed under the License is distributed on an "AS IS" BASIS,
  WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
  See the License for the specific language governing permissions and
  limitations under the License.
-/

import Strata.Languages.Boogie.Verifier

---------------------------------------------------------------------
namespace Strata

def assertionNames : Environment :=
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
#eval TransM.run (translateProgram (assertionNames.commands)) |>.snd |>.isEmpty

/--
info: (procedure Test :  ((x : int)) → ())
modifies: []
preconditions: (Test_requires_0, (x == (#1 : int)))
postconditions: ⏎
body: assert [assert: (x == (#1 : int))] (x == (#1 : int))

Errors: #[]
-/
#guard_msgs in
#eval TransM.run (translateProgram (assertionNames.commands))

/--
info: [Strata.Boogie] Type checking succeeded.


VCs:
Label: assert: (x == (#1 : int))
Assumptions:
(Test_requires_0, ($__x0 == #1))
Proof Obligation:
($__x0 == #1)

Wrote problem to vcs/assert:_(x_eq_(#1_:_int)).smt2.
---
info:
Obligation: assert: (x == (#1 : int))
Result: verified
-/
#guard_msgs in
#eval verify "z3" assertionNames

---------------------------------------------------------------------
