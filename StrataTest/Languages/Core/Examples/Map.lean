/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Core.Verifier

open Strata

---------------------------------------------------------------------
private def mapPgm :=
#strata
program Core;

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
#eval TransM.run Inhabited.default (translateProgram mapPgm) |>.snd |>.isEmpty

/--
info: function a () : Map int bool;
procedure P () returns ()
{
  assume [a_zero_true_assumption]: a[0] == true;
  assert [a_zero_true]: a[0];
  assert [a_one_true]: a[1];
  };
-/
#guard_msgs in
#eval TransM.run Inhabited.default (translateProgram mapPgm) |>.fst

/--
info: [Strata.Core] Type checking succeeded.


VCs:
Label: a_zero_true
Property: assert
Assumptions:
(a_zero_true_assumption, ((~select ~a #0) == #true))

Proof Obligation:
(~select ~a #0)

Label: a_one_true
Property: assert
Assumptions:
(a_zero_true_assumption, ((~select ~a #0) == #true))

Proof Obligation:
(~select ~a #1)



Result: Obligation: a_one_true
Property: assert
Result: ❌ fail


[DEBUG] Evaluated program:
function a () : Map int bool;
procedure P () returns ()
{
  assume [a_zero_true_assumption]: a[0] == true;
  assert [a_zero_true]: a[0];
  assert [a_one_true]: a[1];
  };

---
info:
Obligation: a_zero_true
Property: assert
Result: ✅ pass

Obligation: a_one_true
Property: assert
Result: ❌ fail
-/
#guard_msgs in
#eval verify mapPgm

---------------------------------------------------------------------
