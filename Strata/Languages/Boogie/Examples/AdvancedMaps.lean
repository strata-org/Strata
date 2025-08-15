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

type MapII := Map int int;
type MapIMapII := Map int MapII;

var a : MapII;
var b : Map bool int;
var c : Map int MapII;

procedure P() returns ()
spec {
  modifies a;
  modifies b;
  modifies c;
  requires a[0] == 0;
  requires c[0] == a;
}
{
  assert [c_0_eq_a]: c[0] == a;
  c := c[1 := a];
  assert [c_1_eq_a]: c[1] == a;

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
#eval TransM.run (translateProgram mapPgm) |>.snd |>.isEmpty

/--
info: type MapII := (Map int int)
type MapIMapII := (Map int MapII)
var (a : MapII) := init_a_0
var (b : (Map bool int)) := init_b_1
var (c : (Map int MapII)) := init_c_2
(procedure P :  () → ())
modifies: [a, b, c]
preconditions: (P_requires_3, ((((~select : (arrow (Map int int) (arrow int int))) a) (#0 : int)) == (#0 : int))) (P_requires_4, ((((~select : (arrow (Map int MapII) (arrow int MapII))) c) (#0 : int)) == a))
postconditions: ⏎
body: assert [c_0_eq_a] ((((~select : (arrow (Map int MapII) (arrow int MapII))) c) (#0 : int)) == a)
c := ((((~update : (arrow (Map int MapII) (arrow int (arrow MapII (Map int MapII))))) c) (#1 : int)) a)
assert [c_1_eq_a] ((((~select : (arrow (Map int MapII) (arrow int MapII))) c) (#1 : int)) == a)
assert [a0eq0] ((((~select : (arrow (Map int int) (arrow int int))) a) (#0 : int)) == (#0 : int))
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
#eval TransM.run (translateProgram mapPgm)

/--
info: [Strata.Boogie] Type checking succeeded.


VCs:
Label: c_0_eq_a
Assumptions:
(P_requires_3, (((~select $__a0) #0) == #0))
(P_requires_4, (((~select $__c2) #0) == $__a0))
Proof Obligation:
(((~select $__c2) #0) == $__a0)

Label: c_1_eq_a
Assumptions:
(P_requires_3, (((~select $__a0) #0) == #0))
(P_requires_4, (((~select $__c2) #0) == $__a0))
Proof Obligation:
(((~select (((~update $__c2) #1) $__a0)) #1) == $__a0)

Label: a0eq0
Assumptions:
(P_requires_3, (((~select $__a0) #0) == #0))
(P_requires_4, (((~select $__c2) #0) == $__a0))
Proof Obligation:
(((~select $__a0) #0) == #0)

Label: a1eq1
Assumptions:
(P_requires_3, (((~select $__a0) #0) == #0))
(P_requires_4, (((~select $__c2) #0) == $__a0))
Proof Obligation:
(((~select (((~update $__a0) #1) #1)) #1) == #1)

Label: a0eq1
Assumptions:
(P_requires_3, (((~select $__a0) #0) == #0))
(P_requires_4, (((~select $__c2) #0) == $__a0))
Proof Obligation:
(((~select (((~update (((~update $__a0) #1) #1)) #0) #1)) #0) == #1)

Label: bTrueEqTrue
Assumptions:
(P_requires_3, (((~select $__a0) #0) == #0))
(P_requires_4, (((~select $__c2) #0) == $__a0))
Proof Obligation:
(((~select (((~update $__b1) #true) #-1)) #true) == #-1)

Label: mix
Assumptions:
(P_requires_3, (((~select $__a0) #0) == #0))
(P_requires_4, (((~select $__c2) #0) == $__a0))
Proof Obligation:
(((~select (((~update (((~update $__a0) #1) #1)) #0) #1)) #1) == (~Int.Neg ((~select (((~update $__b1) #true) #-1)) #true)))

Wrote problem to vcs/c_0_eq_a.smt2.
Wrote problem to vcs/c_1_eq_a.smt2.
Wrote problem to vcs/a0eq0.smt2.
Wrote problem to vcs/a1eq1.smt2.
Wrote problem to vcs/a0eq1.smt2.
Wrote problem to vcs/bTrueEqTrue.smt2.
Wrote problem to vcs/mix.smt2.
---
info:
Obligation: c_0_eq_a
Result: verified

Obligation: c_1_eq_a
Result: verified

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
