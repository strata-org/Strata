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

var a : Map int int;
var b : Map bool int;

procedure P() returns ()
spec {
  modifies a;
  modifies b;
  requires a[0] == 0;
}
{
  assert a[0] == 0;
  a := a[1 := 1];
  assert a[1] == 1;
  a := a[0 := 1];
  assert a[1] == 1;

  b := b[true := -1];
  assert b[true] == -1;
  assert [mix]: a[1] == -(b[true]);
};
#end


/-- info: true -/
#guard_msgs in
-- No errors in translation.
#eval TransM.run (translateProgram (mapEnv.commands)) |>.snd |>.isEmpty

/--
info: var (a : (Map int int)) := init_a_0
var (b : (Map bool int)) := init_b_1
(procedure P :  () → ())
modifies: [a, b]
preconditions: (P_requires_2, (((~select a) (#0 : int)) == (#0 : int)))
postconditions: ⏎
body: assert [assert: (((~select a) (#0 : int)) == (#0 : int))] (((~select a) (#0 : int)) == (#0 : int))
a := (((~update a) (#1 : int)) (#1 : int))
assert [assert: (((~select a) (#1 : int)) == (#1 : int))] (((~select a) (#1 : int)) == (#1 : int))
a := (((~update a) (#0 : int)) (#1 : int))
assert [assert: (((~select a) (#1 : int)) == (#1 : int))] (((~select a) (#1 : int)) == (#1 : int))
b := (((~update b) (#true : bool)) (~Int.Neg (#1 : int)))
assert [assert: (((~select b) (#true : bool)) == (~Int.Neg (#1 : int)))] (((~select b) (#true : bool)) == (~Int.Neg (#1 : int)))
assert [mix] (((~select a) (#1 : int)) == (~Int.Neg ((~select b) (#true : bool))))

Errors: #[]
-/
#guard_msgs in
#eval TransM.run (translateProgram (mapEnv.commands))

/--
info: [Strata.Boogie] Type checking succeeded.


VCs:
Label: assert: (((~select a) (#0 : int)) == (#0 : int))
Assumptions:
(P_requires_2, (((~select $__a0) #0) == #0))
Proof Obligation:
(((~select $__a0) #0) == #0)

Label: assert: (((~select a) (#1 : int)) == (#1 : int))
Assumptions:
(P_requires_2, (((~select $__a0) #0) == #0))
Proof Obligation:
(((~select (((~update $__a0) #1) #1)) #1) == #1)

Label: assert: (((~select a) (#1 : int)) == (#1 : int))
Assumptions:
(P_requires_2, (((~select $__a0) #0) == #0))
Proof Obligation:
(((~select (((~update (((~update $__a0) #1) #1)) #0) #1)) #1) == #1)

Label: assert: (((~select b) (#true : bool)) == (~Int.Neg (#1 : int)))
Assumptions:
(P_requires_2, (((~select $__a0) #0) == #0))
Proof Obligation:
(((~select (((~update $__b1) #true) #-1)) #true) == #-1)

Label: mix
Assumptions:
(P_requires_2, (((~select $__a0) #0) == #0))
Proof Obligation:
(((~select (((~update (((~update $__a0) #1) #1)) #0) #1)) #1) == (~Int.Neg ((~select (((~update $__b1) #true) #-1)) #true)))

Wrote problem to vcs/assert: (((~select a) (#0 : int)) == (#0 : int)).smt2.
Wrote problem to vcs/assert: (((~select a) (#1 : int)) == (#1 : int)).smt2.
Wrote problem to vcs/assert: (((~select a) (#1 : int)) == (#1 : int)).smt2.
Wrote problem to vcs/assert: (((~select b) (#true : bool)) == (~Int.Neg (#1 : int))).smt2.
Wrote problem to vcs/mix.smt2.
---
info:
Obligation: assert: (((~select a) (#0 : int)) == (#0 : int))
Result: verified

Obligation: assert: (((~select a) (#1 : int)) == (#1 : int))
Result: verified

Obligation: assert: (((~select a) (#1 : int)) == (#1 : int))
Result: verified

Obligation: assert: (((~select b) (#true : bool)) == (~Int.Neg (#1 : int)))
Result: verified

Obligation: mix
Result: verified
-/
#guard_msgs in
#eval verify "cvc5" mapEnv

---------------------------------------------------------------------
