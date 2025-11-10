/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Boogie.Verifier

---------------------------------------------------------------------
namespace Strata

def havocPgm : Program :=
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
#eval TransM.run (translateProgram havocPgm) |>.snd |>.isEmpty

/--
info: (procedure S :  () → ())
modifies: []
preconditions: ⏎
postconditions: ⏎
body: init (x : int) := init_x_0
x := #1
havoc x
assert [x_eq_1] ((x : int) == #1)

Errors: #[]
-/
#guard_msgs in
#eval TransM.run (translateProgram havocPgm)

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

Evaluated program:
(procedure S :  () → ())
modifies: []
preconditions: ⏎
postconditions: ⏎
body: init (x : int) := init_x_0
x := #1
#[<var x: ($__x0 : int)>] havoc x
assert [x_eq_1] ($__x0 == #1)

---
info:
Obligation: x_eq_1
Result: failed
CEx: ($__x0, 0)
-/
#guard_msgs in
#eval verify "cvc5" havocPgm

---------------------------------------------------------------------
