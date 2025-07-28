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

def havocEnv : Environment :=
#strata
program Boogie;
procedure S() returns ()
{
  var x : int;
  x := 1;
  havoc x;
  assert [x_eq_1]: (x == 1); // error
};
#end

/-- info: true -/
#guard_msgs in
-- No errors in translation.
#eval TransM.run (translateProgram (havocEnv.commands)) |>.snd |>.isEmpty

/--
info: (procedure S :  () → ())
modifies: []
preconditions: ⏎
postconditions: ⏎
body: init (x : int) := init_x_0
x := (#1 : int)
havoc x
assert [x_eq_1] (x == (#1 : int))

Errors: #[]
-/
#guard_msgs in
#eval TransM.run (translateProgram (havocEnv.commands))

/--
info: [Strata.Boogie] Type checking succeeded.


VCs:
Label: x_eq_1
Assumptions:
Proof Obligation:
($__x0 == #1)

Wrote problem to vcs/x_eq_1.smt2.


Obligation x_eq_1: could not be proved!

Result: failed
CEx: ($__x0, 0)
---
info:
Obligation: x_eq_1
Result: failed
CEx: ($__x0, 0)
-/
#guard_msgs in
#eval verify "cvc5" havocEnv

---------------------------------------------------------------------
