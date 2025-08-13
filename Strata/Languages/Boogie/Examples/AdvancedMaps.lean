/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/


import Strata.Languages.Boogie.Verifier

---------------------------------------------------------------------
open Strata

private def mapPgm :=
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
  assert [a0eq0]: a[0] == 0;
  a := a[1 := 1];
  assert [a1eq1]: a[1] == 1;
  a := a[0 := 1];
  assert [a0eq1]: a[0] == 1;

  b := b[true := -1];
  assert [bTrueEqTrue]: b[true] == -1;
  assert [mix]: a[1] == -(b[true]);
};
#end


/-- info: true -/
#guard_msgs in
-- No errors in translation.
#eval TransM.run (translateProgram (mapPgm.commands)) |>.snd |>.isEmpty

/--
info: var (a : (Map int int)) := init_a_0
var (b : (Map bool int)) := init_b_1
(procedure P :  () → ())
modifies: [a, b]
preconditions: (P_requires_2, ((((~select : (arrow (Map int int) (arrow int int))) a) (#0 : int)) == (#0 : int)))
postconditions: ⏎
body: assert [a0eq0] ((((~select : (arrow (Map int int) (arrow int int))) a) (#0 : int)) == (#0 : int))
a := ((((~update : (arrow (Map int int) (arrow int (arrow int (Map int int))))) a) (#1 : int)) (#1 : int))
assert [a1eq1] ((((~select : (arrow (Map int int) (arrow int int))) a) (#1 : int)) == (#1 : int))
a := ((((~update : (arrow (Map int int) (arrow int (arrow int (Map int int))))) a) (#0 : int)) (#1 : int))
assert [a0eq1] ((((~select : (arrow (Map int int) (arrow int int))) a) (#0 : int)) == (#1 : int))
b := ((((~update : (arrow (Map bool int) (arrow bool (arrow int (Map bool int))))) b) (#true : bool)) (~Int.Neg (#1 : int)))
assert [bTrueEqTrue] ((((~select : (arrow (Map bool int) (arrow bool int))) b) (#true : bool)) == (~Int.Neg (#1 : int)))
assert [mix] ((((~select : (arrow (Map int int) (arrow int int))) a) (#1 : int)) == (~Int.Neg (((~select : (arrow (Map bool int) (arrow bool int))) b) (#true : bool))))

Errors: #[]
-/
#guard_msgs in
#eval TransM.run (translateProgram (mapPgm.commands))

/--
info: [Strata.Boogie] Type checking succeeded.


VCs:
Label: a0eq0
Assumptions:
(P_requires_2, (((~select $__a0) #0) == #0))
Proof Obligation:
(((~select $__a0) #0) == #0)

Label: a1eq1
Assumptions:
(P_requires_2, (((~select $__a0) #0) == #0))
Proof Obligation:
(((~select (((~update $__a0) #1) #1)) #1) == #1)

Label: a0eq1
Assumptions:
(P_requires_2, (((~select $__a0) #0) == #0))
Proof Obligation:
(((~select (((~update (((~update $__a0) #1) #1)) #0) #1)) #0) == #1)

Label: bTrueEqTrue
Assumptions:
(P_requires_2, (((~select $__a0) #0) == #0))
Proof Obligation:
(((~select (((~update $__b1) #true) #-1)) #true) == #-1)

Label: mix
Assumptions:
(P_requires_2, (((~select $__a0) #0) == #0))
Proof Obligation:
(((~select (((~update (((~update $__a0) #1) #1)) #0) #1)) #1) == (~Int.Neg ((~select (((~update $__b1) #true) #-1)) #true)))

Wrote problem to vcs/a0eq0.smt2.
Wrote problem to vcs/a1eq1.smt2.
Wrote problem to vcs/a0eq1.smt2.
Wrote problem to vcs/bTrueEqTrue.smt2.
Wrote problem to vcs/mix.smt2.
---
info:
Obligation: a0eq0
Result: verified

Obligation: a1eq1
Result: verified

Obligation: a0eq1
Result: verified

Obligation: bTrueEqTrue
Result: verified

Obligation: mix
Result: verified
-/
#guard_msgs in
#eval verify "cvc5" mapPgm

---------------------------------------------------------------------
