/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/


import Strata.Languages.Core.Verifier

---------------------------------------------------------------------
open Strata

private def failing :=
#strata
program Core;

type MapII := Map int int;

procedure P(inout a : MapII)
spec {
  requires a[0] == 0;
}
{
  assert a[0] == 1;
};
#end


/--
info: true
-/
#guard_msgs in
-- No errors in translation.
#eval TransM.run Inhabited.default (translateProgram failing) |>.snd |>.isEmpty

/--
info: program Core;

type MapII := Map int int;
procedure P (inout a : MapII)
spec {
  requires [P_requires_0]: a[0] == 0;
  } {
  assert [assert_0]: a[0] == 1;
};
-/
#guard_msgs in
#eval TransM.run Inhabited.default (translateProgram failing) |>.fst

/--
info:
Obligation: assert_0
Property: assert
Result: ❌ fail
-/
#guard_msgs in
#eval verify failing (options := .quiet)

---------------------------------------------------------------------

private def failingThrice :=
#strata
program Core;

procedure P(x : int)
spec {
  requires x != 0;
}
{
  assert x == 1;
  assert x == 2;
  assert x != 7;
};
#end

/--
info:
Obligation: assert_0
Property: assert
Result: ❌ fail

Obligation: assert_1
Property: assert
Result: ❌ fail

Obligation: assert_2
Property: assert
Result: ❌ fail
-/
#guard_msgs in
#eval verify failingThrice (options := .quiet)
