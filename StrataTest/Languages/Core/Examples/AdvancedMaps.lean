/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/


import Strata.Languages.Core.Verifier

---------------------------------------------------------------------
open Strata

private def mapPgm :=
#strata
program Core;

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
  assert [a0neq2]: a[0] != 2;

  b := b[true := -1];
  assert [bTrueEqTrue]: b[true] == -1;
  assert [mix]: a[1] == -(b[true]);
};
#end


/-- info: true -/
#guard_msgs in
-- No errors in translation.
#eval TransM.run Inhabited.default (translateProgram mapPgm) |>.snd |>.isEmpty

/-

info: type MapII := (Map int int)
type MapIMapII := (Map int MapII)
var (a : MapII) := init_a_0
var (b : (Map bool int)) := init_b_1
var (c : (Map int MapII)) := init_c_2
procedure P :  () → ()
  modifies: [a, b, c]
  preconditions: (P_requires_3, (((~select : (arrow (Map int int) (arrow int int)))
    (a : MapII)
    #0) == #0)) (P_requires_4, (((~select : (arrow (Map int MapII) (arrow int MapII)))
    (c : (Map int MapII))
    #0) == (a : MapII)))
  postconditions: 
{
  assert [c_0_eq_a] (((~select : (arrow (Map int MapII) (arrow int MapII))) (c : (Map int MapII)) #0) == (a : MapII))
  c := ((~update : (arrow (Map int MapII) (arrow int (arrow MapII (Map int MapII)))))
   (c : (Map int MapII))
   #1
   (a : MapII))
  assert [c_1_eq_a] (((~select : (arrow (Map int MapII) (arrow int MapII))) (c : (Map int MapII)) #1) == (a : MapII))
  assert [a0eq0] (((~select : (arrow (Map int int) (arrow int int))) (a : MapII) #0) == #0)
  a := ((~update : (arrow (Map int int) (arrow int (arrow int (Map int int))))) (a : MapII) #1 #1)
  assert [a1eq1] (((~select : (arrow (Map int int) (arrow int int))) (a : MapII) #1) == #1)
  a := ((~update : (arrow (Map int int) (arrow int (arrow int (Map int int))))) (a : MapII) #0 #1)
  assert [a0eq1] (((~select : (arrow (Map int int) (arrow int int))) (a : MapII) #0) == #1)
  assert [a0neq2] ((~Bool.Not : (arrow bool bool))
   (((~select : (arrow (Map int int) (arrow int int))) (a : MapII) #0) == #2))
  b := ((~update : (arrow (Map bool int) (arrow bool (arrow int (Map bool int)))))
   (b : (Map bool int))
   #true
   ((~Int.Neg : (arrow int int)) #1))
  assert [bTrueEqTrue] (((~select : (arrow (Map bool int) (arrow bool int)))
    (b : (Map bool int))
    #true) == ((~Int.Neg : (arrow int int)) #1))
  assert [mix] (((~select : (arrow (Map int int) (arrow int int)))
    (a : MapII)
    #1) == ((~Int.Neg : (arrow int int))
    ((~select : (arrow (Map bool int) (arrow bool int))) (b : (Map bool int)) #true)))
}
Errors: #[]
-/
#guard_msgs in
#eval TransM.run Inhabited.default (translateProgram mapPgm)

/-

info: [Strata.Core] Type checking succeeded.
-/
#guard_msgs in
#eval verify "cvc5" mapPgm

---------------------------------------------------------------------
