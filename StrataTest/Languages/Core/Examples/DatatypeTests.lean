/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Core.Verifier

/-!
# Datatype Verification Tests

- Nested polymorphic datatypes (List of Option) with deep destructor access
- Hidden type recursion (datatype referenced only transitively via another datatype's constructor)
-/

namespace Strata.DatatypeTests

---------------------------------------------------------------------
-- Test 1: Nested Polymorphic Datatypes (List of Option)
---------------------------------------------------------------------

def nestedPolyDestructorPgm : Program :=
#strata
program Core;

datatype Option (a : Type) { None(), Some(OptionVal: a) };
datatype List (a : Type) { Nil(), Cons(hd: a, tl: List a) };

procedure TestNestedPolyDestructor() returns ()
spec {
  ensures true;
}
{
  var listOfOpt : List (Option int);
  var headOpt : Option int;
  var value : int;

  listOfOpt := Cons(Some(42), Nil());

  assert [isCons]: List..isCons(listOfOpt);

  headOpt := List..hd(listOfOpt);
  value := Option..OptionVal(headOpt);

  assert [valueIs42]: value == 42;
};
#end

/-- info: true -/
#guard_msgs in
#eval TransM.run Inhabited.default (translateProgram nestedPolyDestructorPgm) |>.snd |>.isEmpty

/--
info:
Obligation: isCons
Property: assert
Result: ✅ pass

Obligation: valueIs42
Property: assert
Result: ✅ pass

Obligation: TestNestedPolyDestructor_ensures_0
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval verify nestedPolyDestructorPgm (options := .quiet)

---------------------------------------------------------------------
-- Test 2: Hidden Type Recursion
--
-- Container references Hidden in its constructor, but the program
-- never directly uses Hidden. Tests that SMT.Context.addType correctly
-- handles transitive datatype dependencies.
---------------------------------------------------------------------

def hiddenTypeRecursionPgm : Program :=
#strata
program Core;

datatype Hidden (a : Type) { HiddenValue(hiddenField: a) };
datatype Container (a : Type) { Empty(), WithHidden(hiddenPart: Hidden a, visiblePart: a) };

procedure TestHiddenTypeRecursion() returns ()
spec {
  ensures true;
}
{
  var container : Container int;
  var vp : int;

  container := Empty();
  havoc container;

  assume !Container..isEmpty(container);

  vp := Container..visiblePart(container);
  assume vp == 42;

  assert [isWithHidden]: Container..isWithHidden(container);
};
#end

/-- info: true -/
#guard_msgs in
#eval TransM.run Inhabited.default (translateProgram hiddenTypeRecursionPgm) |>.snd |>.isEmpty

/--
info:
Obligation: isWithHidden
Property: assert
Result: ✅ pass

Obligation: TestHiddenTypeRecursion_ensures_0
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval verify hiddenTypeRecursionPgm (options := .quiet)

end Strata.DatatypeTests
