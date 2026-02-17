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

/--
info: type MapII := Map int int;
type MapIMapII := Map int MapII;
var a : MapII;
var b : (Map bool int);
var c : (Map int MapII);
procedure P () returns ()
spec {
  modifies a;
  modifies b;
  modifies c;
  requires [P_requires_3]: a[0] == 0;
  requires [P_requires_4]: c[0] == a;
  } {
  assert [c_0_eq_a]: c[0] == a;
  c := c[1:=a];
  assert [c_1_eq_a]: c[1] == a;
  assert [a0eq0]: a[0] == 0;
  a := a[1:=1];
  assert [a1eq1]: a[1] == 1;
  a := a[0:=1];
  assert [a0eq1]: a[0] == 1;
  assert [a0neq2]: !(a[0] == 2);
  b := b[true:=-(1)];
  assert [bTrueEqTrue]: b[true] == -(1);
  assert [mix]: a[1] == -(b[true]);
  };
-/
#guard_msgs in
#eval TransM.run Inhabited.default (translateProgram mapPgm) |>.fst

/--
info: [Strata.Core] Type checking succeeded.


VCs:
Label: c_0_eq_a
Property: assert
Assumptions:
(P_requires_3, ((~select $__a0 #0) == #0))
(P_requires_4, ((~select $__c2 #0) == $__a0))

Proof Obligation:
((~select $__c2 #0) == $__a0)

Label: c_1_eq_a
Property: assert
Assumptions:
(P_requires_3, ((~select $__a0 #0) == #0))
(P_requires_4, ((~select $__c2 #0) == $__a0))

Proof Obligation:
((~select (~update $__c2 #1 $__a0) #1) == $__a0)

Label: a0eq0
Property: assert
Assumptions:
(P_requires_3, ((~select $__a0 #0) == #0))
(P_requires_4, ((~select $__c2 #0) == $__a0))

Proof Obligation:
((~select $__a0 #0) == #0)

Label: a1eq1
Property: assert
Assumptions:
(P_requires_3, ((~select $__a0 #0) == #0))
(P_requires_4, ((~select $__c2 #0) == $__a0))

Proof Obligation:
((~select (~update $__a0 #1 #1) #1) == #1)

Label: a0eq1
Property: assert
Assumptions:
(P_requires_3, ((~select $__a0 #0) == #0))
(P_requires_4, ((~select $__c2 #0) == $__a0))

Proof Obligation:
((~select (~update (~update $__a0 #1 #1) #0 #1) #0) == #1)

Label: a0neq2
Property: assert
Assumptions:
(P_requires_3, ((~select $__a0 #0) == #0))
(P_requires_4, ((~select $__c2 #0) == $__a0))

Proof Obligation:
(~Bool.Not ((~select (~update (~update $__a0 #1 #1) #0 #1) #0) == #2))

Label: bTrueEqTrue
Property: assert
Assumptions:
(P_requires_3, ((~select $__a0 #0) == #0))
(P_requires_4, ((~select $__c2 #0) == $__a0))

Proof Obligation:
((~select (~update $__b1 #true #-1) #true) == #-1)

Label: mix
Property: assert
Assumptions:
(P_requires_3, ((~select $__a0 #0) == #0))
(P_requires_4, ((~select $__c2 #0) == $__a0))

Proof Obligation:
((~select (~update (~update $__a0 #1 #1) #0 #1) #1) == (~Int.Neg (~select (~update $__b1 #true #-1) #true)))

---
info:
Obligation: c_0_eq_a
Property: assert
Result: ✅ pass

Obligation: c_1_eq_a
Property: assert
Result: ✅ pass

Obligation: a0eq0
Property: assert
Result: ✅ pass

Obligation: a1eq1
Property: assert
Result: ✅ pass

Obligation: a0eq1
Property: assert
Result: ✅ pass

Obligation: a0neq2
Property: assert
Result: ✅ pass

Obligation: bTrueEqTrue
Property: assert
Result: ✅ pass

Obligation: mix
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval verify mapPgm

---------------------------------------------------------------------
