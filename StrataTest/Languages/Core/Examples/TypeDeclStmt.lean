/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Core.Verifier

namespace Strata

/-- Basic uninterpreted type declaration with equality reasoning -/
def typeDeclStmt1 : Program :=
#strata
program Core;

procedure P () returns () {
  type T;
  var a : T;
  var b : T;
  var c : T;
  assume [ab]: (a == b);
  assume [bc]: (b == c);
  assert [trans]: (a == c);
};
#end

/-- info: #[] -/
#guard_msgs in
#eval TransM.run Inhabited.default (translateProgram typeDeclStmt1) |>.snd

/--
info: [Strata.Core] Type checking succeeded.


VCs:
Label: trans
Property: assert
Assumptions:
ab: $__a0 == $__b1
bc: $__b1 == $__c2
Obligation:
$__a0 == $__c2

---
info:
Obligation: trans
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval verify typeDeclStmt1

/-- Type scoping - same type name in different procedures -/
def typeDeclStmt2 : Program :=
#strata
program Core;

procedure P1 () returns () {
  type T;
  var x : T;
};

procedure P2 () returns () {
  type T;
  var y : T;
};
#end

/-- info: #[] -/
#guard_msgs in
#eval TransM.run Inhabited.default (translateProgram typeDeclStmt2) |>.snd

/-- Multiple distinct uninterpreted types in same procedure -/
def typeDeclStmt3 : Program :=
#strata
program Core;

procedure P () returns () {
  type T;
  type U;
  var x : T;
  var y : U;
  var z : T;
  assume [x_eq_z]: (x == z);
  assert [reflexive]: (x == x);
};
#end

/-- info: #[] -/
#guard_msgs in
#eval TransM.run Inhabited.default (translateProgram typeDeclStmt3) |>.snd

/--
info: [Strata.Core] Type checking succeeded.


VCs:
Label: reflexive
Property: assert
Assumptions:
x_eq_z: $__x0 == $__z2
Obligation:
true

---
info:
Obligation: reflexive
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval verify typeDeclStmt3

/-- Parameterized type declaration -/
def typeDeclStmt4 : Program :=
#strata
program Core;

procedure P () returns () {
  type T (a : Type, b : Type);
  var x : T int bool;
  var y : T int bool;
  assume [diff]: (x != y);
  assert [neq]: (x != y);
};
#end

/-- info: #[] -/
#guard_msgs in
#eval TransM.run Inhabited.default (translateProgram typeDeclStmt4) |>.snd

/--
info: [Strata.Core] Type checking succeeded.


VCs:
Label: neq
Property: assert
Assumptions:
diff: !($__x0 == $__y1)
Obligation:
!($__x0 == $__y1)

---
info:
Obligation: neq
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval verify typeDeclStmt4

/--
error: Expression has type T int bool when T bool int expected.
-/
#guard_msgs in
def typeDeclStmtError1 :=
#strata
program Core;

procedure P () returns () {
  type T (a : Type, b : Type);
  var p1 : T int bool;
  var p2 : T bool int;
  assert [wrong]: (p1 == p2);
};
#end

end Strata
