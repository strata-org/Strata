/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/


import Strata.Languages.Boogie.Verifier

---------------------------------------------------------------------
open Strata

private def failing :=
#strata
program Boogie;

type MapII := Map int int;

var a : MapII;

procedure P() returns ()
spec {
  modifies a;
  requires a[0] == 0;
}
{
  assert a[0] == 1;
};
#end


/-- info: true -/
#guard_msgs in
-- No errors in translation.
#eval TransM.run Inhabited.default (translateProgram failing) |>.snd |>.isEmpty

/--
info: type MapII := (Map int int)
var (a : MapII) := init_a_0
(procedure P :  () → ())
modifies: [a]
preconditions: (P_requires_1, ((((~select : (arrow (Map int int) (arrow int int))) (a : MapII)) #0) == #0))
postconditions: ⏎
body: assert [assert_0] ((((~select : (arrow (Map int int) (arrow int int))) (a : MapII)) #0) == #1)

Errors: #[]
-/
#guard_msgs in
#eval TransM.run Inhabited.default (translateProgram failing)

/--
info: [Strata.Boogie] Type checking succeeded.


VCs:
Label: assert_0
Assumptions:
(P_requires_1, (((~select $__a0) #0) == #0))

Proof Obligation:
(((~select $__a0) #0) == #1)

Wrote problem to vcs/assert_0.smt2.


Obligation assert_0: could not be proved!

Result: failed
CEx: ⏎

Evaluated program:
type MapII := (Map int int)
var (a : (Map int int)) := init_a_0
(procedure P :  () → ())
modifies: [a]
preconditions: (P_requires_1, ((((~select : (arrow (Map int int) (arrow int int))) (a : (Map int int))) #0) == #0))
postconditions: ⏎
body: assume [P_requires_1] (((~select $__a0) #0) == #0)
assert [assert_0] (((~select $__a0) #0) == #1)

---
info:
Obligation: assert_0
Result: failed
CEx:
-/
#guard_msgs in
#eval verify "cvc5" failing

---------------------------------------------------------------------

private def failingThrice :=
#strata
program Boogie;

procedure P(x : int) returns ()
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

Obligation assert_0: could not be proved!

Result: failed
CEx: ($__x0, (- 1))


Obligation assert_1: could not be proved!

Result: failed
CEx: ($__x0, (- 1))


Obligation assert_2: could not be proved!

Result: failed
CEx: ($__x0, 7)
---
info:
Obligation: assert_0
Result: failed
CEx: ($__x0, (- 1))

Obligation: assert_1
Result: failed
CEx: ($__x0, (- 1))

Obligation: assert_2
Result: failed
CEx: ($__x0, 7)
-/
#guard_msgs in
#eval verify "cvc5" failingThrice Inhabited.default Options.quiet
