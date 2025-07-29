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

def mapEnv : Environment :=
#strata
program Boogie;

const a : Map int bool;

procedure P() returns ()
{
  assume [a_zero_true_assumption]: (a[0] == true);
  assert [a_zero_true]: a[0];
  assert [a_one_true]: a[1];
};
#end

/-- info: true -/
#guard_msgs in
-- No errors in translation.
#eval TransM.run (translateProgram (mapEnv.commands)) |>.snd |>.isEmpty

/--
info: func a :  () → (Map int bool);
(procedure P :  () → ())
modifies: []
preconditions: ⏎
postconditions: ⏎
body: assume [a_zero_true_assumption] (((~select ~a) (#0 : int)) == (#true : bool))
assert [a_zero_true] ((~select ~a) (#0 : int))
assert [a_one_true] ((~select ~a) (#1 : int))

Errors: #[]
-/
#guard_msgs in
#eval TransM.run (translateProgram (mapEnv.commands))

/--
info: [Strata.Boogie] Type checking succeeded.


VCs:
Label: a_zero_true
Assumptions:
(a_zero_true_assumption, (((~select ~a) #0) == #true))
Proof Obligation:
((~select ~a) #0)

Label: a_one_true
Assumptions:
(a_zero_true_assumption, (((~select ~a) #0) == #true))
Proof Obligation:
((~select ~a) #1)

Wrote problem to vcs/a_zero_true.smt2.
Wrote problem to vcs/a_one_true.smt2.


Obligation a_one_true: could not be proved!

Result: failed
CEx: ⏎
---
info:
Obligation: a_zero_true
Result: verified

Obligation: a_one_true
Result: failed
CEx:
-/
#guard_msgs in
#eval verify "cvc5" mapEnv

---------------------------------------------------------------------
