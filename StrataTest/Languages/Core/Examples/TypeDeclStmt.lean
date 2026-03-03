/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Core.Verifier

namespace Strata

/-- Basic uninterpreted type declaration in a statement -/
def typeDeclStmt1 : Program :=
#strata
program Core;

procedure P () returns () {
  type T;
  var x : T;
  var y : T;
  assume [xy_eq]: (x == y);
  assert [reflexive]: (x == x);
};
#end

/-- info: #[] -/
#guard_msgs in
#eval TransM.run Inhabited.default (translateProgram typeDeclStmt1) |>.snd

/--
info: [Strata.Core] Type checking succeeded.


VCs:
Label: reflexive
Property: assert
Assumptions:
xy_eq: x == y
Obligation:
x == x

---
info:
Obligation: reflexive
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval verify typeDeclStmt1

--------------------------------------------------------------------

/-- Polymorphic uninterpreted type with constructor and accessors -/
def typeDeclStmt2 : Program :=
#strata
program Core;

procedure P () returns () {
  type Pair (a : Type, b : Type);
  
  function mkPair<a, b>(x : a, y : b) : Pair a b;
  function fst<a, b>(p : Pair a b) : a;
  function snd<a, b>(p : Pair a b) : b;
  
  axiom [fst_mkPair]: (forall<a, b> x : a, y : b :: fst(mkPair(x, y)) == x);
  axiom [snd_mkPair]: (forall<a, b> x : a, y : b :: snd(mkPair(x, y)) == y);
  
  var p1 : Pair int bool := mkPair(42, true);
  var p2 : Pair bool int := mkPair(false, 42);
  
  assert [fst_snd_eq]: (fst(p1) == snd(p2));
};
#end

/-- info: #[] -/
#guard_msgs in
#eval TransM.run Inhabited.default (translateProgram typeDeclStmt2) |>.snd

/--
info: [Strata.Core] Type checking succeeded.


VCs:
Label: fst_snd_eq
Property: assert
Obligation:
42 == 42

---
info:
Obligation: fst_snd_eq
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval verify typeDeclStmt2

--------------------------------------------------------------------

/-- Type declaration should be scoped to the procedure -/
def typeDeclStmt3 : Program :=
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
#eval TransM.run Inhabited.default (translateProgram typeDeclStmt3) |>.snd

--------------------------------------------------------------------

/-- Function declarations should be able to use statement-level types -/
def typeDeclStmt4 : Program :=
#strata
program Core;

procedure P () returns () {
  type T;
  var x : T;
  function id(v : T) : T { v }
  var y : T := id(x);
  assert [id_correct]: (y == x);
};
#end

/-- info: #[] -/
#guard_msgs in
#eval TransM.run Inhabited.default (translateProgram typeDeclStmt4) |>.snd

/--
info: [Strata.Core] Type checking succeeded.


VCs:
Label: id_correct
Property: assert
Obligation:
x == x

---
info:
Obligation: id_correct
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval verify typeDeclStmt4

--------------------------------------------------------------------

/-- Type mismatch should be caught -/
/--
error: Expression has type Pair bool int when Pair int bool expected.
-/
#guard_msgs in
def typeDeclStmtError1 :=
#strata
program Core;

procedure P () returns () {
  type Pair (a : Type, b : Type);
  var p1 : Pair int bool;
  var p2 : Pair bool int;
  assert [wrong]: (p1 == p2);
};
#end

end Strata
