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

/-- Type scoping - type declared in one procedure not visible in another -/
def typeDeclStmt2 : Program :=
#strata
program Core;

procedure P1 () returns () {
  type T;
  var x : T;
};

procedure P2 () returns () {
  var y : int;
  assert [trivial]: (y == y);
};
#end

/-- info: #[] -/
#guard_msgs in
#eval TransM.run Inhabited.default (translateProgram typeDeclStmt2) |>.snd

/--
info: [Strata.Core] Type checking succeeded.


VCs:
Label: trivial
Property: assert
Obligation:
true

---
info:
Obligation: trivial
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval verify typeDeclStmt2

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

end Strata
