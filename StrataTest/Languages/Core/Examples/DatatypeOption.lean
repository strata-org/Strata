/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Core.Verifier

/-!
# Datatype Option Integration Test

Tests Option-style datatypes (constructors with fields) using the DDM
datatype declaration syntax. Verifies:
- Parsing of Option datatype declarations with None() and Some(val: int)
- Tester functions (Option..isNone, Option..isSome)
- Destructor function (val) for field access
- Type-checking and verification
-/

namespace Strata.DatatypeOptionTest

---------------------------------------------------------------------
-- Test 1: Basic Option Datatype Declaration and Tester Functions
---------------------------------------------------------------------

def optionTesterPgm : Program :=
#strata
program Core;

// Define Option datatype with None() and Some(val: int) constructors
datatype Option () { None(), Some(val: int) };

procedure TestOptionTesters() returns ()
spec {
  ensures true;
}
{
  var x : Option;
  var y : Option;

  // Create a None value
  x := None();

  // Test that x is None
  assert [isNone]: Option..isNone(x);

  // Test that x is not Some
  assert [notSome]: !Option..isSome(x);

  // Create a Some value
  y := Some(42);

  // Test that y is Some
  assert [isSome]: Option..isSome(y);

  // Test that y is not None
  assert [notNone]: !Option..isNone(y);
};
#end

/-- info: true -/
#guard_msgs in
#eval TransM.run Inhabited.default (translateProgram optionTesterPgm) |>.snd |>.isEmpty

/--
info:
Obligation: isNone
Property: assert
Result: ✅ pass

Obligation: notSome
Property: assert
Result: ✅ pass

Obligation: isSome
Property: assert
Result: ✅ pass

Obligation: notNone
Property: assert
Result: ✅ pass

Obligation: TestOptionTesters_ensures_0
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval verify "cvc5" optionTesterPgm (options := .quiet)

---------------------------------------------------------------------
-- Test 2: Option with Havoc (requires SMT reasoning)
---------------------------------------------------------------------

def optionHavocPgm : Program :=
#strata
program Core;

datatype Option () { None(), Some(val: int) };

procedure TestOptionHavoc() returns ()
spec {
  ensures true;
}
{
  var x : Option;

  // Initialize and then havoc
  x := None();
  havoc x;

  // Assume x is Some
  assume Option..isSome(x);

  // Assert x is not None (should follow from assumption)
  assert [notNone]: !Option..isNone(x);
};
#end

/-- info: true -/
#guard_msgs in
#eval TransM.run Inhabited.default (translateProgram optionHavocPgm) |>.snd |>.isEmpty

/--
info:
Obligation: notNone
Property: assert
Result: ✅ pass

Obligation: TestOptionHavoc_ensures_0
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval verify "cvc5" optionHavocPgm (options := .quiet)

---------------------------------------------------------------------
-- Test 3: Option Exhaustiveness (exactly one tester is true)
---------------------------------------------------------------------

def optionExhaustivePgm : Program :=
#strata
program Core;

datatype Option () { None(), Some(val: int) };

procedure TestOptionExhaustive() returns ()
spec {
  ensures true;
}
{
  var x : Option;

  // Havoc to get arbitrary Option
  x := None();
  havoc x;

  // At least one tester must be true (exhaustiveness)
  assert [exhaustive]: Option..isNone(x) || Option..isSome(x);
};
#end

/-- info: true -/
#guard_msgs in
#eval TransM.run Inhabited.default (translateProgram optionExhaustivePgm) |>.snd |>.isEmpty

/--
info:
Obligation: exhaustive
Property: assert
Result: ✅ pass

Obligation: TestOptionExhaustive_ensures_0
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval verify "cvc5" optionExhaustivePgm (options := .quiet)

---------------------------------------------------------------------
-- Test 4: Option Mutual Exclusion (testers are mutually exclusive)
---------------------------------------------------------------------

def optionMutualExclusionPgm : Program :=
#strata
program Core;

datatype Option () { None(), Some(val: int) };

procedure TestOptionMutualExclusion() returns ()
spec {
  ensures true;
}
{
  var x : Option;

  // Havoc to get arbitrary Option
  x := None();
  havoc x;

  // Assume x is None
  assume Option..isNone(x);

  // Assert x is not Some (mutual exclusion)
  assert [mutualExclusion]: !Option..isSome(x);
};
#end

/-- info: true -/
#guard_msgs in
#eval TransM.run Inhabited.default (translateProgram optionMutualExclusionPgm) |>.snd |>.isEmpty

/--
info:
Obligation: mutualExclusion
Property: assert
Result: ✅ pass

Obligation: TestOptionMutualExclusion_ensures_0
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval verify "cvc5" optionMutualExclusionPgm (options := .quiet)

---------------------------------------------------------------------
-- Test 5: Option Constructor Equality
---------------------------------------------------------------------

def optionEqualityPgm : Program :=
#strata
program Core;

datatype Option () { None(), Some(val: int) };

procedure TestOptionEquality() returns ()
spec {
  ensures true;
}
{
  var x : Option;
  var y : Option;

  // Create two None values
  x := None();
  y := None();

  // Assert they are equal
  assert [noneEquality]: x == y;

  // Create two Some values with same argument
  x := Some(42);
  y := Some(42);

  // Assert they are equal
  assert [someEquality]: x == y;
};
#end

/-- info: true -/
#guard_msgs in
#eval TransM.run Inhabited.default (translateProgram optionEqualityPgm) |>.snd |>.isEmpty

/--
info:
Obligation: noneEquality
Property: assert
Result: ✅ pass

Obligation: someEquality
Property: assert
Result: ✅ pass

Obligation: TestOptionEquality_ensures_0
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval verify "cvc5" optionEqualityPgm (options := .quiet)

---------------------------------------------------------------------
-- Test 6: Option Constructor Inequality
---------------------------------------------------------------------

def optionInequalityPgm : Program :=
#strata
program Core;

datatype Option () { None(), Some(val: int) };

procedure TestOptionInequality() returns ()
spec {
  ensures true;
}
{
  var x : Option;
  var y : Option;

  // Create None and Some values
  x := None();
  y := Some(42);

  // Assert they are not equal
  assert [noneVsSome]: x != y;
};
#end

/-- info: true -/
#guard_msgs in
#eval TransM.run Inhabited.default (translateProgram optionInequalityPgm) |>.snd |>.isEmpty

/--
info:
Obligation: noneVsSome
Property: assert
Result: ✅ pass

Obligation: TestOptionInequality_ensures_0
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval verify "cvc5" optionInequalityPgm (options := .quiet)

---------------------------------------------------------------------
-- Test 7: Option Destructor Function (field accessor)
---------------------------------------------------------------------

def optionDestructorPgm : Program :=
#strata
program Core;

datatype Option () { None(), Some(val: int) };

procedure TestOptionDestructor() returns ()
spec {
  ensures true;
}
{
  var x : Option;
  var v : int;

  // Create a Some value with known content
  x := Some(42);

  // Extract the value using the destructor function
  v := Option..val(x);

  // Assert the extracted value is correct
  assert [valIs42]: v == 42;

  // Test with a different value
  x := Some(100);
  v := Option..val(x);
  assert [valIs100]: v == 100;
};
#end

/-- info: true -/
#guard_msgs in
#eval TransM.run Inhabited.default (translateProgram optionDestructorPgm) |>.snd |>.isEmpty

/--
info:
Obligation: valIs42
Property: assert
Result: ✅ pass

Obligation: valIs100
Property: assert
Result: ✅ pass

Obligation: TestOptionDestructor_ensures_0
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval verify "cvc5" optionDestructorPgm (options := .quiet)

end Strata.DatatypeOptionTest
