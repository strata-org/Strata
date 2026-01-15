/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Boogie.Verifier

/-!
# Datatype List Integration Test

Tests recursive List datatypes using the DDM datatype declaration syntax.
Verifies:
- Parsing of List datatype declarations with Nil() and Cons(head: int, tail: List) constructors
- Tester functions (List..isNil, List..isCons)
- Destructor functions (head, tail) for field access
- Type-checking and verification with recursive type

-/

namespace Strata.DatatypeListTest

---------------------------------------------------------------------
-- Test 1: Basic List Datatype Declaration and Tester Functions
---------------------------------------------------------------------

def listTesterPgm : Program :=
#strata
program Boogie;

// Define List datatype with Nil() and Cons(head: int, tail: List) constructors
// Note: This is a recursive datatype - tail has type List
datatype List () { Nil(), Cons(head: int, tail: List) };

procedure TestListTesters() returns ()
spec {
  ensures true;
}
{
  var xs : List;
  var ys : List;

  // Create a Nil (empty list)
  xs := Nil();

  // Test that xs is Nil
  assert [isNil]: List..isNil(xs);

  // Test that xs is not Cons
  assert [notCons]: !List..isCons(xs);

  // Create a Cons (non-empty list with one element)
  ys := Cons(42, Nil());

  // Test that ys is Cons
  assert [isCons]: List..isCons(ys);

  // Test that ys is not Nil
  assert [notNil]: !List..isNil(ys);
};
#end

/-- info: true -/
#guard_msgs in
#eval TransM.run Inhabited.default (translateProgram listTesterPgm) |>.snd |>.isEmpty

/--
info:
Obligation: isNil
Property: assert
Result: ✅ pass

Obligation: notCons
Property: assert
Result: ✅ pass

Obligation: isCons
Property: assert
Result: ✅ pass

Obligation: notNil
Property: assert
Result: ✅ pass

Obligation: TestListTesters_ensures_0
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval verify "cvc5" listTesterPgm Inhabited.default Options.quiet

---------------------------------------------------------------------
-- Test 2: List with Havoc (requires SMT reasoning)
---------------------------------------------------------------------

def listHavocPgm : Program :=
#strata
program Boogie;

datatype List () { Nil(), Cons(head: int, tail: List) };

procedure TestListHavoc() returns ()
spec {
  ensures true;
}
{
  var xs : List;

  // Initialize and then havoc
  xs := Nil();
  havoc xs;

  // Assume xs is Cons
  assume List..isCons(xs);

  // Assert xs is not Nil (should follow from assumption)
  assert [notNil]: !List..isNil(xs);
};
#end

/-- info: true -/
#guard_msgs in
#eval TransM.run Inhabited.default (translateProgram listHavocPgm) |>.snd |>.isEmpty

/--
info:
Obligation: notNil
Property: assert
Result: ✅ pass

Obligation: TestListHavoc_ensures_0
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval verify "cvc5" listHavocPgm Inhabited.default Options.quiet

---------------------------------------------------------------------
-- Test 3: List Exhaustiveness (exactly one tester is true)
---------------------------------------------------------------------

def listExhaustivePgm : Program :=
#strata
program Boogie;

datatype List () { Nil(), Cons(head: int, tail: List) };

procedure TestListExhaustive() returns ()
spec {
  ensures true;
}
{
  var xs : List;

  // Havoc to get arbitrary List
  xs := Nil();
  havoc xs;

  // At least one tester must be true (exhaustiveness)
  assert [exhaustive]: List..isNil(xs) || List..isCons(xs);
};
#end

/-- info: true -/
#guard_msgs in
#eval TransM.run Inhabited.default (translateProgram listExhaustivePgm) |>.snd |>.isEmpty

/--
info:
Obligation: exhaustive
Property: assert
Result: ✅ pass

Obligation: TestListExhaustive_ensures_0
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval verify "cvc5" listExhaustivePgm Inhabited.default Options.quiet

---------------------------------------------------------------------
-- Test 4: List Mutual Exclusion (testers are mutually exclusive)
---------------------------------------------------------------------

def listMutualExclusionPgm : Program :=
#strata
program Boogie;

datatype List () { Nil(), Cons(head: int, tail: List) };

procedure TestListMutualExclusion() returns ()
spec {
  ensures true;
}
{
  var xs : List;

  // Havoc to get arbitrary List
  xs := Nil();
  havoc xs;

  // Assume xs is Nil
  assume List..isNil(xs);

  // Assert xs is not Cons (mutual exclusion)
  assert [mutualExclusion]: !List..isCons(xs);
};
#end

/-- info: true -/
#guard_msgs in
#eval TransM.run Inhabited.default (translateProgram listMutualExclusionPgm) |>.snd |>.isEmpty

/--
info:
Obligation: mutualExclusion
Property: assert
Result: ✅ pass

Obligation: TestListMutualExclusion_ensures_0
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval verify "cvc5" listMutualExclusionPgm Inhabited.default Options.quiet

---------------------------------------------------------------------
-- Test 5: List Constructor Equality
---------------------------------------------------------------------

def listEqualityPgm : Program :=
#strata
program Boogie;

datatype List () { Nil(), Cons(head: int, tail: List) };

procedure TestListEquality() returns ()
spec {
  ensures true;
}
{
  var xs : List;
  var ys : List;

  // Create two Nil values
  xs := Nil();
  ys := Nil();

  // Assert they are equal
  assert [nilEquality]: xs == ys;

  // Create two Cons values with same arguments
  xs := Cons(42, Nil());
  ys := Cons(42, Nil());

  // Assert they are equal
  assert [consEquality]: xs == ys;
};
#end

/-- info: true -/
#guard_msgs in
#eval TransM.run Inhabited.default (translateProgram listEqualityPgm) |>.snd |>.isEmpty

/--
info:
Obligation: nilEquality
Property: assert
Result: ✅ pass

Obligation: consEquality
Property: assert
Result: ✅ pass

Obligation: TestListEquality_ensures_0
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval verify "cvc5" listEqualityPgm Inhabited.default Options.quiet

---------------------------------------------------------------------
-- Test 6: List Constructor Inequality
---------------------------------------------------------------------

def listInequalityPgm : Program :=
#strata
program Boogie;

datatype List () { Nil(), Cons(head: int, tail: List) };

procedure TestListInequality() returns ()
spec {
  ensures true;
}
{
  var xs : List;
  var ys : List;

  // Create Nil and Cons values
  xs := Nil();
  ys := Cons(42, Nil());

  // Assert they are not equal
  assert [nilVsCons]: xs != ys;
};
#end

/-- info: true -/
#guard_msgs in
#eval TransM.run Inhabited.default (translateProgram listInequalityPgm) |>.snd |>.isEmpty

/--
info:
Obligation: nilVsCons
Property: assert
Result: ✅ pass

Obligation: TestListInequality_ensures_0
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval verify "cvc5" listInequalityPgm Inhabited.default Options.quiet

---------------------------------------------------------------------
-- Test 7: List Destructor Functions (head and tail)
---------------------------------------------------------------------

def listDestructorPgm : Program :=
#strata
program Boogie;

datatype List () { Nil(), Cons(head: int, tail: List) };

procedure TestListDestructor() returns ()
spec {
  ensures true;
}
{
  var xs : List;
  var h : int;
  var t : List;

  // Create a Cons value with known content
  xs := Cons(42, Nil());

  // Extract the head using the destructor function
  h := head(xs);

  // Assert the extracted head is correct
  assert [headIs42]: h == 42;

  // Extract the tail using the destructor function
  t := tail(xs);

  // Assert the tail is Nil
  assert [tailIsNil]: List..isNil(t);

  // Test with a longer list
  xs := Cons(10, Cons(20, Nil()));
  h := head(xs);
  assert [headIs10]: h == 10;

  t := tail(xs);
  assert [tailIsCons]: List..isCons(t);
};
#end

/-- info: true -/
#guard_msgs in
#eval TransM.run Inhabited.default (translateProgram listDestructorPgm) |>.snd |>.isEmpty

/--
info:
Obligation: headIs42
Property: assert
Result: ✅ pass

Obligation: tailIsNil
Property: assert
Result: ✅ pass

Obligation: headIs10
Property: assert
Result: ✅ pass

Obligation: tailIsCons
Property: assert
Result: ✅ pass

Obligation: TestListDestructor_ensures_0
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval verify "cvc5" listDestructorPgm Inhabited.default Options.quiet

---------------------------------------------------------------------
-- Test 8: Nested List Operations (head of tail)
---------------------------------------------------------------------

def listNestedPgm : Program :=
#strata
program Boogie;

datatype List () { Nil(), Cons(head: int, tail: List) };

procedure TestListNested() returns ()
spec {
  ensures true;
}
{
  var xs : List;
  var second : int;

  // Create a list with two elements: [1, 2]
  xs := Cons(1, Cons(2, Nil()));

  // Get the second element (head of tail)
  second := head(tail(xs));

  // Assert the second element is 2
  assert [secondIs2]: second == 2;
};
#end

/-- info: true -/
#guard_msgs in
#eval TransM.run Inhabited.default (translateProgram listNestedPgm) |>.snd |>.isEmpty

/--
info:
Obligation: secondIs2
Property: assert
Result: ✅ pass

Obligation: TestListNested_ensures_0
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval verify "cvc5" listNestedPgm Inhabited.default Options.quiet

---------------------------------------------------------------------
-- Test 9: List Destructor with Havoc (requires SMT reasoning)
---------------------------------------------------------------------

def listDestructorHavocPgm : Program :=
#strata
program Boogie;

datatype List () { Nil(), Cons(head: int, tail: List) };

procedure TestListDestructorHavoc() returns ()
spec {
  ensures true;
}
{
  var xs : List;
  var h : int;

  // Initialize and then havoc
  xs := Nil();
  havoc xs;

  // Assume xs is a specific Cons
  assume xs == Cons(100, Nil());

  // Extract head
  h := head(xs);

  // Assert head is 100
  assert [headIs100]: h == 100;
};
#end

/-- info: true -/
#guard_msgs in
#eval TransM.run Inhabited.default (translateProgram listDestructorHavocPgm) |>.snd |>.isEmpty

/--
info:
Obligation: headIs100
Property: assert
Result: ✅ pass

Obligation: TestListDestructorHavoc_ensures_0
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval verify "cvc5" listDestructorHavocPgm Inhabited.default Options.quiet

---------------------------------------------------------------------
-- Test 10: List with Different Values (inequality of different heads)
---------------------------------------------------------------------

def listDifferentValuesPgm : Program :=
#strata
program Boogie;

datatype List () { Nil(), Cons(head: int, tail: List) };

procedure TestListDifferentValues() returns ()
spec {
  ensures true;
}
{
  var xs : List;
  var ys : List;

  // Create two Cons values with different heads
  xs := Cons(1, Nil());
  ys := Cons(2, Nil());

  // Assert they are not equal
  assert [different_values]: xs != ys;
};
#end

/-- info: true -/
#guard_msgs in
#eval TransM.run Inhabited.default (translateProgram listDifferentValuesPgm) |>.snd |>.isEmpty

/--
info:
Obligation: different_values
Property: assert
Result: ✅ pass

Obligation: TestListDifferentValues_ensures_0
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval verify "cvc5" listDifferentValuesPgm Inhabited.default Options.quiet

end Strata.DatatypeListTest
