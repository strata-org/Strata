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

rec function listLen (@[cases] xs : IntList) : int
{
  if IntList..isNil(xs) then 0 else 1 + listLen(IntList..tl(xs))
};

procedure TestListLen()
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
Label: listLen_terminates_0
Property: assert
Assumptions:
IntList..dtRank_0: forall __q0 : IntList ::  { IntList..dtRank(__q0) }
  IntList..dtRank(__q0) >= 0
IntList..dtRank_1: forall __q0 : int :: forall __q1 : IntList ::  { IntList..dtRank(Cons(__q0, __q1)) }
  IntList..dtRank(__q1) < IntList..dtRank(Cons(__q0, __q1))
Obligation:
!(IntList..isNil(xs)) ==> IntList..dtRank(IntList..tl(xs)) < IntList..dtRank(xs)

Label: listLen_body_calls_IntList..tl_0
Property: assert
Obligation:
!(IntList..isNil(xs@1)) ==> IntList..isCons(xs@1)

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
info:
Obligation: listLen_terminates_0
Property: assert
Result: ✅ pass

Obligation: listLen_body_calls_IntList..tl_0
Property: assert
Result: ✅ pass

Obligation: nilLen
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

rec function listLen (@[cases] xs : IntList) : int
{
  if IntList..isNil(xs) then 0 else 1 + listLen(IntList..tl(xs))
};

procedure TestNilCase(xs : IntList)
spec {
  requires IntList..isNil(xs);
  ensures true;
}
{
  assert [nilCase]: listLen(xs) == 0;
};

procedure TestConsCase(xs : IntList)
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
Label: listLen_terminates_0
Property: assert
Assumptions:
IntList..dtRank_0: forall __q0 : IntList ::  { IntList..dtRank(__q0) }
  IntList..dtRank(__q0) >= 0
IntList..dtRank_1: forall __q0 : int :: forall __q1 : IntList ::  { IntList..dtRank(Cons(__q0, __q1)) }
  IntList..dtRank(__q1) < IntList..dtRank(Cons(__q0, __q1))
Obligation:
!(IntList..isNil(xs)) ==> IntList..dtRank(IntList..tl(xs)) < IntList..dtRank(xs)

Label: listLen_body_calls_IntList..tl_0
Property: assert
Obligation:
!(IntList..isNil(xs@1)) ==> IntList..isCons(xs@1)

Label: nilCase
Property: assert
Assumptions:
TestNilCase_requires_0: IntList..isNil(xs@2)
Obligation:
listLen(xs@2) == 0

Label: TestNilCase_ensures_1
Property: assert
Assumptions:
TestNilCase_requires_0: IntList..isNil(xs@2)
Obligation:
true

Label: assert_consLen_calls_IntList..tl_0
Property: assert
Assumptions:
TestConsCase_requires_0: IntList..isCons(xs@3)
Obligation:
IntList..isCons(xs@3)

Label: consLen
Property: assert
Assumptions:
TestConsCase_requires_0: IntList..isCons(xs@3)
Obligation:
listLen(xs@3) == 1 + listLen(IntList..tl(xs@3))

Label: TestConsCase_ensures_1
Property: assert
Assumptions:
TestConsCase_requires_0: IntList..isCons(xs@3)
Obligation:
true

---
info:
Obligation: listLen_terminates_0
Property: assert
Result: ✅ pass

Obligation: listLen_body_calls_IntList..tl_0
Property: assert
Result: ✅ pass

Obligation: nilCase
Property: assert
Result: ✅ pass

Obligation: TestNilCase_ensures_1
Property: assert
Result: ✅ pass

Obligation: assert_consLen_calls_IntList..tl_0
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

rec function contains (key : int, @[cases] xs : IntList) : bool
{
  if IntList..isNil(xs) then false
  else if IntList..hd(xs) == key then true
  else contains(key, IntList..tl(xs))
};

procedure TestContains()
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
Obligation: contains_terminates_0
Property: assert
Result: ✅ pass

Obligation: contains_body_calls_IntList..hd_0
Property: assert
Result: ✅ pass

Obligation: contains_body_calls_IntList..tl_1
Property: assert
Result: ✅ pass

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

-- Note: without termination checking, this isn't really a proof

def impEquivPgm : Program :=
#strata
program Core;

datatype IntList { Nil(), Cons(hd: int, tl: IntList) };

rec function listLen (@[cases] xs : IntList) : int
{
  if IntList..isNil(xs) then 0 else 1 + listLen(IntList..tl(xs))
};

procedure listLenImp(xs : IntList, out r : int)
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
Label: listLen_terminates_0
Property: assert
Assumptions:
IntList..dtRank_0: forall __q0 : IntList ::  { IntList..dtRank(__q0) }
  IntList..dtRank(__q0) >= 0
IntList..dtRank_1: forall __q0 : int :: forall __q1 : IntList ::  { IntList..dtRank(Cons(__q0, __q1)) }
  IntList..dtRank(__q1) < IntList..dtRank(Cons(__q0, __q1))
Obligation:
!(IntList..isNil(xs)) ==> IntList..dtRank(IntList..tl(xs)) < IntList..dtRank(xs)

Label: listLen_body_calls_IntList..tl_0
Property: assert
Obligation:
!(IntList..isNil(xs@1)) ==> IntList..isCons(xs@1)

Label: entry_invariant_0_0
Property: assert
Obligation:
0 + listLen(xs@2) == listLen(xs@2)

Label: entry_invariant_0_1
Property: assert
Obligation:
true

Label: set_cur_calls_IntList..tl_0
Property: assert
Assumptions:
<label_ite_cond_true: !(IntList..isNil(cur))>: !(IntList..isNil(xs@2))
assume_guard_0: !(IntList..isNil(cur@1))
assume_invariant_0_0: acc@1 + listLen(cur@1) == listLen(xs@2)
assume_invariant_0_1: acc@1 >= 0
assume_entry_invariant_0_0: 0 + listLen(xs@2) == listLen(xs@2)
Obligation:
IntList..isCons(cur@1)

Label: arbitrary_iter_maintain_invariant_0_0
Property: assert
Assumptions:
<label_ite_cond_true: !(IntList..isNil(cur))>: !(IntList..isNil(xs@2))
assume_guard_0: !(IntList..isNil(cur@1))
assume_invariant_0_0: acc@1 + listLen(cur@1) == listLen(xs@2)
assume_invariant_0_1: acc@1 >= 0
assume_entry_invariant_0_0: 0 + listLen(xs@2) == listLen(xs@2)
Obligation:
acc@1 + 1 + listLen(IntList..tl(cur@1)) == listLen(xs@2)

Label: arbitrary_iter_maintain_invariant_0_1
Property: assert
Assumptions:
<label_ite_cond_true: !(IntList..isNil(cur))>: !(IntList..isNil(xs@2))
assume_guard_0: !(IntList..isNil(cur@1))
assume_invariant_0_0: acc@1 + listLen(cur@1) == listLen(xs@2)
assume_invariant_0_1: acc@1 >= 0
assume_entry_invariant_0_0: 0 + listLen(xs@2) == listLen(xs@2)
Obligation:
acc@1 + 1 >= 0

Label: equiv
Property: assert
Assumptions:
assume_entry_invariant_0_0: 0 + listLen(xs@2) == listLen(xs@2)
<label_ite_cond_true: !(IntList..isNil(cur))>: if !(IntList..isNil(xs@2)) then !(IntList..isNil(xs@2)) else true
assume_guard_0: if !(IntList..isNil(xs@2)) then !(IntList..isNil(cur@1)) else true
assume_invariant_0_0: if !(IntList..isNil(xs@2)) then acc@1 + listLen(cur@1) == listLen(xs@2) else true
assume_invariant_0_1: if !(IntList..isNil(xs@2)) then acc@1 >= 0 else true
not_guard_0: if !(IntList..isNil(xs@2)) then !(!(IntList..isNil(cur@2))) else true
invariant_0_0: if !(IntList..isNil(xs@2)) then acc@2 + listLen(cur@2) == listLen(xs@2) else true
invariant_0_1: if !(IntList..isNil(xs@2)) then acc@2 >= 0 else true
<label_ite_cond_false: !(!(IntList..isNil(cur)))>: if if !(IntList..isNil(xs@2)) then false else true then if !(IntList..isNil(xs@2)) then false else true else true
Obligation:
if !(IntList..isNil(xs@2)) then acc@2 else 0 == listLen(xs@2)

---
info:
Obligation: listLen_terminates_0
Property: assert
Result: ✅ pass

Obligation: listLen_body_calls_IntList..tl_0
Property: assert
Result: ✅ pass

Obligation: entry_invariant_0_0
Property: assert
Result: ✅ pass

Obligation: entry_invariant_0_1
Property: assert
Result: ✅ pass

Obligation: set_cur_calls_IntList..tl_0
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

---------------------------------------------------------------------
-- Test 5: recursive function with precondition
---------------------------------------------------------------------

def recPrecondPgm : Program :=
#strata
program Core;

datatype IntList { Nil(), Cons(hd: int, tl: IntList) };

rec function listLen (@[cases] xs : IntList) : int
{
  if IntList..isNil(xs) then 0 else 1 + listLen(IntList..tl(xs))
};

rec function nth (@[cases] xs : IntList, n : int) : int
  requires IntList..isCons(xs);
  requires n >= 0;
  requires n < listLen(xs);
{
  if IntList..isNil(xs) then 0
  else if n == 0 then IntList..hd(xs)
  else nth(IntList..tl(xs), n - 1)
};

procedure TestNth()
spec {
  ensures true;
}
{
  assert [first]:  nth(Cons(10, Cons(20, Nil())), 0) == 10;
  assert [second]: nth(Cons(10, Cons(20, Nil())), 1) == 20;
};
#end

/-- info: true -/
#guard_msgs in
#eval TransM.run Inhabited.default (translateProgram recPrecondPgm) |>.snd |>.isEmpty

/--
info:
Obligation: listLen_terminates_0
Property: assert
Result: ✅ pass

Obligation: listLen_body_calls_IntList..tl_0
Property: assert
Result: ✅ pass

Obligation: nth_terminates_0
Property: assert
Result: ✅ pass

Obligation: nth_body_calls_IntList..hd_0
Property: assert
Result: ✅ pass

Obligation: nth_body_calls_IntList..tl_1
Property: assert
Result: ✅ pass

Obligation: nth_body_calls_nth_2
Property: assert
Result: ✅ pass

Obligation: nth_body_calls_nth_3
Property: assert
Result: ✅ pass

Obligation: nth_body_calls_nth_4
Property: assert
Result: ✅ pass

Obligation: assert_first_calls_nth_0
Property: assert
Result: ✅ pass

Obligation: assert_first_calls_nth_1
Property: assert
Result: ✅ pass

Obligation: assert_first_calls_nth_2
Property: assert
Result: ✅ pass

Obligation: first
Property: assert
Result: ✅ pass

Obligation: assert_second_calls_nth_0
Property: assert
Result: ✅ pass

Obligation: assert_second_calls_nth_1
Property: assert
Result: ✅ pass

Obligation: assert_second_calls_nth_2
Property: assert
Result: ✅ pass

Obligation: second
Property: assert
Result: ✅ pass

Obligation: TestNth_ensures_0
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval verify recPrecondPgm (options := .quiet)

end Strata.RecursiveFunctionTest
