/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Boogie.Verifier

/-!
# Datatype Enum Integration Test

Tests enum-style datatypes (constructors with no fields) using the DDM
datatype declaration syntax. Verifies:
- Parsing of enum datatype declarations
- Tester functions (Color..isRed, Color..isGreen, Color..isBlue)
- Type-checking and verification
-/

namespace Strata.DatatypeEnumTest

---------------------------------------------------------------------
-- Test 1: Basic Enum Datatype Declaration and Tester Functions
---------------------------------------------------------------------

def enumPgm : Program :=
#strata
program Boogie;

// Define an enum-style datatype with no fields
datatype Color () { Red(), Green(), Blue() };

procedure TestEnumTesters() returns ()
spec {
  ensures true;
}
{
  var c : Color;

  // Create a Red color
  c := Red();

  // Test that c is Red
  assert [isRed]: Color..isRed(c);

  // Test that c is not Green or Blue
  assert [notGreen]: !Color..isGreen(c);
  assert [notBlue]: !Color..isBlue(c);
};
#end

/-- info: true -/
#guard_msgs in
#eval TransM.run Inhabited.default (translateProgram enumPgm) |>.snd |>.isEmpty

/--
info:
Obligation: isRed
Property: assert
Result: ✅ pass

Obligation: notGreen
Property: assert
Result: ✅ pass

Obligation: notBlue
Property: assert
Result: ✅ pass

Obligation: TestEnumTesters_ensures_0
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval verify "cvc5" enumPgm Inhabited.default Options.quiet

---------------------------------------------------------------------
-- Test 2: Enum with Havoc (requires SMT reasoning)
---------------------------------------------------------------------

def enumHavocPgm : Program :=
#strata
program Boogie;

datatype Color () { Red(), Green(), Blue() };

procedure TestEnumHavoc() returns ()
spec {
  ensures true;
}
{
  var c : Color;

  // Initialize and then havoc
  c := Red();
  havoc c;

  // Assume c is Green
  assume Color..isGreen(c);

  // Assert c is not Red (should follow from assumption)
  assert [notRed]: !Color..isRed(c);

  // Assert c is not Blue (should follow from assumption)
  assert [notBlue]: !Color..isBlue(c);
};
#end

/-- info: true -/
#guard_msgs in
#eval TransM.run Inhabited.default (translateProgram enumHavocPgm) |>.snd |>.isEmpty

/--
info:
Obligation: notRed
Property: assert
Result: ✅ pass

Obligation: notBlue
Property: assert
Result: ✅ pass

Obligation: TestEnumHavoc_ensures_0
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval verify "cvc5" enumHavocPgm Inhabited.default Options.quiet

---------------------------------------------------------------------
-- Test 3: Enum Exhaustiveness (exactly one tester is true)
---------------------------------------------------------------------

def enumExhaustivePgm : Program :=
#strata
program Boogie;

datatype Color () { Red(), Green(), Blue() };

procedure TestEnumExhaustive() returns ()
spec {
  ensures true;
}
{
  var c : Color;

  // Havoc to get arbitrary color
  c := Red();
  havoc c;

  // At least one tester must be true (exhaustiveness)
  assert [exhaustive]: Color..isRed(c) || Color..isGreen(c) || Color..isBlue(c);
};
#end

/-- info: true -/
#guard_msgs in
#eval TransM.run Inhabited.default (translateProgram enumExhaustivePgm) |>.snd |>.isEmpty

/--
info:
Obligation: exhaustive
Property: assert
Result: ✅ pass

Obligation: TestEnumExhaustive_ensures_0
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval verify "cvc5" enumExhaustivePgm Inhabited.default Options.quiet

end Strata.DatatypeEnumTest
