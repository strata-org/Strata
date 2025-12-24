/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Boogie.Verifier

---------------------------------------------------------------------
namespace Strata

/-!
# Recursive Datatype Example: List

This example demonstrates recursive datatypes with the List type,
showing how to work with constructors, testers, and destructors
for recursive structures.
-/

def listConsPgm : Program :=
#strata
program Boogie;

datatype List (α : Type) {
  Nil(),
  Cons(head: α, tail: List α)
};

procedure testCons(x: int, xs: List int) returns (r: List int)
spec {
  ensures [r_is_cons]: (List$isCons(r));
  ensures [head_correct]: (List$ConsProj0(r) == x);
  ensures [tail_correct]: (List$ConsProj1(r) == xs);
}
{
  r := Cons(x, xs);
  assert [r_is_cons]: List$isCons(r);
  assert [head_correct]: (List$ConsProj0(r) == x);
  assert [tail_correct]: (List$ConsProj1(r) == xs);
};
#end

/-
/-- info: true -/
#guard_msgs in
#eval TransM.run Inhabited.default (translateProgram listConsPgm) |>.snd |>.isEmpty
-/

/-
/--
info: [Strata.Boogie] Type checking succeeded.


VCs:
Label: r_is_cons
Assumptions:


Proof Obligation:
(~List$isCons ((~Cons $__x0) $__xs0))

Label: head_correct
Assumptions:


Proof Obligation:
((~List$ConsProj0 ((~Cons $__x0) $__xs0)) == $__x0)

Label: tail_correct
Assumptions:


Proof Obligation:
((~List$ConsProj1 ((~Cons $__x0) $__xs0)) == $__xs0)

Label: testCons_ensures_0
Assumptions:


Proof Obligation:
(~List$isCons ((~Cons $__x0) $__xs0))

Label: testCons_ensures_1
Assumptions:


Proof Obligation:
((~List$ConsProj0 ((~Cons $__x0) $__xs0)) == $__x0)

Label: testCons_ensures_2
Assumptions:


Proof Obligation:
((~List$ConsProj1 ((~Cons $__x0) $__xs0)) == $__xs0)

---
info:
Obligation: r_is_cons
Result: verified

Obligation: head_correct
Result: verified

Obligation: tail_correct
Result: verified

Obligation: testCons_ensures_0
Result: verified

Obligation: testCons_ensures_1
Result: verified

Obligation: testCons_ensures_2
Result: verified
-/
#guard_msgs in
#eval verify "cvc5" listConsPgm
-/

---------------------------------------------------------------------

def listNilPgm : Program :=
#strata
program Boogie;

datatype List (α : Type) {
  Nil(),
  Cons(head: α, tail: List α)
};

procedure testNil() returns (r: List int)
spec {
  ensures [r_is_nil]: (List$isNil(r));
  ensures [r_not_cons]: (!List$isCons(r));
}
{
  r := Nil();
  assert [r_is_nil]: List$isNil(r);
  assert [r_not_cons]: !List$isCons(r);
};
#end

/-
/-- info: true -/
#guard_msgs in
#eval TransM.run Inhabited.default (translateProgram listNilPgm) |>.snd |>.isEmpty
-/

/-
/--
info: [Strata.Boogie] Type checking succeeded.


VCs:
Label: r_is_nil
Assumptions:


Proof Obligation:
(~List$isNil ~Nil)

Label: r_not_cons
Assumptions:


Proof Obligation:
(~Bool.Not (~List$isCons ~Nil))

Label: testNil_ensures_0
Assumptions:


Proof Obligation:
(~List$isNil ~Nil)

Label: testNil_ensures_1
Assumptions:


Proof Obligation:
(~Bool.Not (~List$isCons ~Nil))

---
info:
Obligation: r_is_nil
Result: verified

Obligation: r_not_cons
Result: verified

Obligation: testNil_ensures_0
Result: verified

Obligation: testNil_ensures_1
Result: verified
-/
#guard_msgs in
#eval verify "cvc5" listNilPgm
-/

---------------------------------------------------------------------

def listHeadPgm : Program :=
#strata
program Boogie;

datatype List (α : Type) {
  Nil(),
  Cons(head: α, tail: List α)
};

procedure getHead(xs: List int) returns (result: int)
spec {
  requires [xs_is_cons]: (List$isCons(xs));
  ensures [result_is_head]: (result == List$ConsProj0(xs));
}
{
  assert [xs_is_cons]: List$isCons(xs);
  result := List$ConsProj0(xs);
};
#end

/-
/-- info: true -/
#guard_msgs in
#eval TransM.run Inhabited.default (translateProgram listHeadPgm) |>.snd |>.isEmpty
-/

/-
/--
info: [Strata.Boogie] Type checking succeeded.


VCs:
Label: xs_is_cons
Assumptions:
(getHead_requires_0, (~List$isCons $__xs0))

Proof Obligation:
(~List$isCons $__xs0)

Label: getHead_ensures_0
Assumptions:
(getHead_requires_0, (~List$isCons $__xs0))

Proof Obligation:
($__result0 == (~List$ConsProj0 $__xs0))

---
info:
Obligation: xs_is_cons
Result: verified

Obligation: getHead_ensures_0
Result: verified
-/
#guard_msgs in
#eval verify "cvc5" listHeadPgm
-/

---------------------------------------------------------------------

def listSingletonPgm : Program :=
#strata
program Boogie;

datatype List (α : Type) {
  Nil(),
  Cons(head: α, tail: List α)
};

procedure singleton(x: int) returns (r: List int)
spec {
  ensures [r_is_cons]: (List$isCons(r));
  ensures [head_is_x]: (List$ConsProj0(r) == x);
  ensures [tail_is_nil]: (List$isNil(List$ConsProj1(r)));
}
{
  r := Cons(x, Nil());
  assert [r_is_cons]: List$isCons(r);
  assert [head_is_x]: (List$ConsProj0(r) == x);
  assert [tail_is_nil]: List$isNil(List$ConsProj1(r));
};
#end

/-
/-- info: true -/
#guard_msgs in
#eval TransM.run Inhabited.default (translateProgram listSingletonPgm) |>.snd |>.isEmpty
-/

/-
/--
info: [Strata.Boogie] Type checking succeeded.


VCs:
Label: r_is_cons
Assumptions:


Proof Obligation:
(~List$isCons ((~Cons $__x0) ~Nil))

Label: head_is_x
Assumptions:


Proof Obligation:
((~List$ConsProj0 ((~Cons $__x0) ~Nil)) == $__x0)

Label: tail_is_nil
Assumptions:


Proof Obligation:
(~List$isNil (~List$ConsProj1 ((~Cons $__x0) ~Nil)))

Label: singleton_ensures_0
Assumptions:


Proof Obligation:
(~List$isCons ((~Cons $__x0) ~Nil))

Label: singleton_ensures_1
Assumptions:


Proof Obligation:
((~List$ConsProj0 ((~Cons $__x0) ~Nil)) == $__x0)

Label: singleton_ensures_2
Assumptions:


Proof Obligation:
(~List$isNil (~List$ConsProj1 ((~Cons $__x0) ~Nil)))

---
info:
Obligation: r_is_cons
Result: verified

Obligation: head_is_x
Result: verified

Obligation: tail_is_nil
Result: verified

Obligation: singleton_ensures_0
Result: verified

Obligation: singleton_ensures_1
Result: verified

Obligation: singleton_ensures_2
Result: verified
-/
#guard_msgs in
#eval verify "cvc5" listSingletonPgm
-/

---------------------------------------------------------------------

end Strata
