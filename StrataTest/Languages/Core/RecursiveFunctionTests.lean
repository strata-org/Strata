/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Core.Verifier

/-!
# Recursive Function Integration Tests

Tests recursive functions over algebraic datatypes using the `recursive function`
concrete syntax with `decreases` clauses. Verifies parsing, translation,
axiom-based SMT encoding, and end-to-end verification.
-/

namespace Strata.RecursiveFunctionTest

---------------------------------------------------------------------
-- Test 1: listLen — basic recursive function, ground assertions
---------------------------------------------------------------------

def listLenPgm : Program :=
#strata
program Core;

datatype IntList { Nil(), Cons(hd: int, tl: IntList) };

recursive function listLen (xs : IntList) : int
  decreases xs
{
  if IntList..isNil(xs) then 0 else 1 + listLen(IntList..tl(xs))
}

procedure TestListLen() returns ()
spec {
  ensures true;
}
{
  assert [nilLen]: listLen(Nil()) == 0;
  assert [oneLen]: listLen(Cons(1, Nil())) == 1;
  assert [twoLen]: listLen(Cons(1, Cons(2, Nil()))) == 2;
};
#end

/-- info: true -/
#guard_msgs in
#eval TransM.run Inhabited.default (translateProgram listLenPgm) |>.snd |>.isEmpty



/--
info: [Strata.Core] Type checking succeeded.


VCs:
Label: nilLen
Property: assert
Obligation:
true

Label: oneLen
Property: assert
Obligation:
true

Label: twoLen
Property: assert
Obligation:
true

Label: TestListLen_ensures_0
Property: assert
Obligation:
true

---
info: Obligation: nilLen
Property: assert
Result: ✅ pass

Obligation: oneLen
Property: assert
Result: ✅ pass

Obligation: twoLen
Property: assert
Result: ✅ pass

Obligation: TestListLen_ensures_0
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval verify listLenPgm (options := .default)

---------------------------------------------------------------------
-- Test 2: listLen with symbolic arguments and axiom reasoning
---------------------------------------------------------------------

def listLenAxiomPgm : Program :=
#strata
program Core;

datatype IntList { Nil(), Cons(hd: int, tl: IntList) };

recursive function listLen (xs : IntList) : int
  decreases xs
{
  if IntList..isNil(xs) then 0 else 1 + listLen(IntList..tl(xs))
}

procedure TestNilCase(xs : IntList) returns ()
spec {
  requires IntList..isNil(xs);
  ensures true;
}
{
  assert [nilCase]: listLen(xs) == 0;
};

procedure TestConsCase(xs : IntList) returns ()
spec {
  requires IntList..isCons(xs);
  ensures true;
}
{
  assert [consLen]: listLen(xs) == 1 + listLen(IntList..tl(xs));
};
#end

/-- info: true -/
#guard_msgs in
#eval TransM.run Inhabited.default (translateProgram listLenAxiomPgm) |>.snd |>.isEmpty

/--
info: [Strata.Core] Type checking succeeded.


VCs:
Label: nilCase
Property: assert
Assumptions:
TestNilCase_requires_0: IntList..isNil($__xs0)
Obligation:
listLen($__xs0) == 0

Label: TestNilCase_ensures_1
Property: assert
Assumptions:
TestNilCase_requires_0: IntList..isNil($__xs0)
Obligation:
true

Label: consLen
Property: assert
Assumptions:
TestConsCase_requires_0: IntList..isCons($__xs1)
Obligation:
listLen($__xs1) == 1 + listLen(IntList..tl($__xs1))

Label: TestConsCase_ensures_1
Property: assert
Assumptions:
TestConsCase_requires_0: IntList..isCons($__xs1)
Obligation:
true

---
info: Obligation: nilCase
Property: assert
Result: ✅ pass

Obligation: TestNilCase_ensures_1
Property: assert
Result: ✅ pass

Obligation: consLen
Property: assert
Result: ✅ pass

Obligation: TestConsCase_ensures_1
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval verify listLenAxiomPgm (options := .default)

---------------------------------------------------------------------
-- Test 3: recursive function with decreases on non-first parameter
---------------------------------------------------------------------

def lookupPgm : Program :=
#strata
program Core;

datatype IntList { Nil(), Cons(hd: int, tl: IntList) };

recursive function contains (key : int, xs : IntList) : bool
  decreases xs
{
  ! (IntList..isNil(xs)) &&
  (IntList..hd(xs) == key  || contains(key, IntList..tl(xs)))
  //if IntList..isNil(xs) then false
  //else if IntList..hd(xs) == key then true
  //else contains(key, IntList..tl(xs))
}

procedure TestContains() returns ()
spec {
  ensures true;
}
{
  assert [emptyList]: !contains(1, Nil());
  assert [found]: contains(2, Cons(1, Cons(2, Nil())));
  assert [notFound]: !contains(3, Cons(1, Cons(2, Nil())));
};
#end

/-- info: true -/
#guard_msgs in
#eval TransM.run Inhabited.default (translateProgram lookupPgm) |>.snd |>.isEmpty

/--
info:
Obligation: emptyList
Property: assert
Result: ✅ pass

Obligation: found
Property: assert
Result: ✅ pass

Obligation: notFound
Property: assert
Result: ✅ pass

Obligation: TestContains_ensures_0
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval verify lookupPgm (options := .quiet)

---------------------------------------------------------------------
-- Test 4: imperative loop equivalent to recursive function
---------------------------------------------------------------------

-- TODO: without termination checking, this isn't really a proof

def impEquivPgm : Program :=
#strata
program Core;

datatype IntList { Nil(), Cons(hd: int, tl: IntList) };

recursive function listLen (xs : IntList) : int
  decreases xs
{
  if IntList..isNil(xs) then 0 else 1 + listLen(IntList..tl(xs))
}

procedure listLenImp(xs : IntList) returns (r : int)
spec {
  ensures [equiv]: r == listLen(xs);
}
{
  var cur : IntList;
  var acc : int;
  cur := xs;
  acc := 0;
  while (!IntList..isNil(cur))
    invariant acc + listLen(cur) == listLen(xs)
    invariant acc >= 0
  {
    acc := acc + 1;
    cur := IntList..tl(cur);
  }
  r := acc;
};
#end

/-- info: true -/
#guard_msgs in
#eval TransM.run Inhabited.default (translateProgram impEquivPgm) |>.snd |>.isEmpty

/--
info: [Strata.Core] Type checking succeeded.


VCs:
Label: entry_invariant_0_0
Property: assert
Assumptions:
<label_ite_cond_true: (~Bool.Not (~IntList..isNil cur))>: !(IntList..isNil($__xs0))
Obligation:
0 + listLen($__xs0) == listLen($__xs0)

Label: entry_invariant_0_1
Property: assert
Assumptions:
<label_ite_cond_true: (~Bool.Not (~IntList..isNil cur))>: !(IntList..isNil($__xs0))
Obligation:
true

Label: arbitrary_iter_maintain_invariant_0_0
Property: assert
Assumptions:
<label_ite_cond_true: (~Bool.Not (~IntList..isNil cur))>: !(IntList..isNil($__xs0))
assume_guard_0: !(IntList..isNil($__cur5))
assume_invariant_0_0: $__acc4 + listLen($__cur5) == listLen($__xs0)
assume_invariant_0_1: $__acc4 >= 0
Obligation:
$__acc4 + 1 + listLen(IntList..tl($__cur5)) == listLen($__xs0)

Label: arbitrary_iter_maintain_invariant_0_1
Property: assert
Assumptions:
<label_ite_cond_true: (~Bool.Not (~IntList..isNil cur))>: !(IntList..isNil($__xs0))
assume_guard_0: !(IntList..isNil($__cur5))
assume_invariant_0_0: $__acc4 + listLen($__cur5) == listLen($__xs0)
assume_invariant_0_1: $__acc4 >= 0
Obligation:
$__acc4 + 1 >= 0

Label: equiv
Property: assert
Assumptions:
<label_ite_cond_true: (~Bool.Not (~IntList..isNil cur))>: if !(IntList..isNil($__xs0)) then !(IntList..isNil($__xs0)) else true
assume_guard_0: if !(IntList..isNil($__xs0)) then !(IntList..isNil($__cur5)) else true
assume_invariant_0_0: if !(IntList..isNil($__xs0)) then $__acc4 + listLen($__cur5) == listLen($__xs0) else true
assume_invariant_0_1: if !(IntList..isNil($__xs0)) then $__acc4 >= 0 else true
not_guard_0: if !(IntList..isNil($__xs0)) then !(!(IntList..isNil($__cur7))) else true
invariant_0_0: if !(IntList..isNil($__xs0)) then $__acc6 + listLen($__cur7) == listLen($__xs0) else true
invariant_0_1: if !(IntList..isNil($__xs0)) then $__acc6 >= 0 else true
<label_ite_cond_false: !(~Bool.Not (~IntList..isNil cur))>: if if !(IntList..isNil($__xs0)) then false else true then if !(IntList..isNil($__xs0)) then false else true else true
Obligation:
if !(IntList..isNil($__xs0)) then $__acc6 else 0 == listLen($__xs0)

---
info: Obligation: entry_invariant_0_0
Property: assert
Result: ✅ pass

Obligation: entry_invariant_0_1
Property: assert
Result: ✅ pass

Obligation: arbitrary_iter_maintain_invariant_0_0
Property: assert
Result: ✅ pass

Obligation: arbitrary_iter_maintain_invariant_0_1
Property: assert
Result: ✅ pass

Obligation: equiv
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval verify impEquivPgm (options := .default)

end Strata.RecursiveFunctionTest
