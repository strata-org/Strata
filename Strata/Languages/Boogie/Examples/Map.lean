/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Boogie.Verifier

open Strata

---------------------------------------------------------------------
private def mapPgm :=
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
#eval TransM.run (translateProgram mapPgm) |>.snd |>.isEmpty

/--
info: func a :  () → (Map int bool);
(procedure P :  () → ())
modifies: []
preconditions: ⏎
postconditions: ⏎
body: assume [a_zero_true_assumption] ((((~select : (arrow (Map int bool) (arrow int bool))) (~a : (Map int bool))) (#0 : int)) == (#true : bool))
assert [a_zero_true] (((~select : (arrow (Map int bool) (arrow int bool))) (~a : (Map int bool))) (#0 : int))
assert [a_one_true] (((~select : (arrow (Map int bool) (arrow int bool))) (~a : (Map int bool))) (#1 : int))

Errors: #[]
-/
#guard_msgs in
#eval TransM.run (translateProgram mapPgm)

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

Evaluated program:
func a :  () → (Map int bool);
(procedure P :  () → ())
modifies: []
preconditions: ⏎
postconditions: ⏎
body: assume [a_zero_true_assumption] (((~select ~a) #0) == #true)
assert [a_zero_true] ((~select ~a) #0)
assert [a_one_true] ((~select ~a) #1)

---
info:
Obligation: a_zero_true
Result: verified

Obligation: a_one_true
Result: failed
CEx:
-/
#guard_msgs in
#eval verify "cvc5" mapPgm

---------------------------------------------------------------------
