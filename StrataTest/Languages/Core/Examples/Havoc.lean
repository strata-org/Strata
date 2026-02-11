/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Core.Verifier

---------------------------------------------------------------------
namespace Strata

def havocPgm : Program :=
#strata
program Core;
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
#eval TransM.run Inhabited.default (translateProgram havocPgm) |>.snd |>.isEmpty

/--
info: procedure S :  () → ()
  modifies: []
  preconditions: ⏎
  postconditions: ⏎
{
  init (x : int) := init_x_0
  x := #1
  havoc x
  assert [x_eq_1] ((x : int) == #1)
}
Errors: #[]
-/
#guard_msgs in
#eval TransM.run Inhabited.default (translateProgram havocPgm)

/--
info: [Strata.Core] Type checking succeeded.


VCs:
Label: x_eq_1
Property: assert
Assumptions:


Proof Obligation:
($__x0 == #1)



Result: Obligation: x_eq_1
Property: assert
Result: ❌ fail
Model:
($__x0, 0)


Evaluated program:
procedure S :  () → ()
  modifies: []
  preconditions: ⏎
  postconditions: ⏎
{
  init (x : int) := init_x_0
  x := #1
  havoc x
  assert [x_eq_1] ($__x0 == #1)
}
---
info:
Obligation: x_eq_1
Property: assert
Result: ❌ fail
Model:
($__x0, 0)
-/
#guard_msgs in
#eval verify "cvc5" havocPgm

---------------------------------------------------------------------
