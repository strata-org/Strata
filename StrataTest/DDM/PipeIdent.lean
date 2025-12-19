/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.DDM.Integration.Lean

open Strata

-- Test dialect for pipe-delimited identifiers (SMT-LIB/Boogie syntax)
#dialect
dialect PipeIdent;

category Expression;

op var (name : Ident) : Expression => name;
op assign (lhs : Ident, rhs : Expression) : Command => lhs " := " rhs ";";
op add (a : Expression, b : Expression) : Expression => @[prec(10), leftassoc] a " + " b;
op or (a : Expression, b : Expression) : Expression => @[prec(5), leftassoc] a " || " b;
op bitwiseOr (a : Expression, b : Expression) : Expression => @[prec(6), leftassoc] a " | " b;
op intLit (n : Num) : Expression => n;

#end

namespace PipeIdent

#strata_gen PipeIdent

end PipeIdent

-- Test 1: Simple pipe-delimited identifier with hyphens
def testHyphenated := #strata
program PipeIdent;
|special-name| := 42;
#end

/--
info: "program PipeIdent;\n(|special-name|) := 42;"
-/
#guard_msgs in
#eval toString testHyphenated.format

-- Test 2: Pipe-delimited identifier with spaces
def testSpaces := #strata
program PipeIdent;
|name with spaces| := 10;
#end

/--
info: "program PipeIdent;\n(|name with spaces|) := 10;"
-/
#guard_msgs in
#eval toString testSpaces.format

-- Test 3: Pipe-delimited identifier with special characters
def testSpecialChars := #strata
program PipeIdent;
|name@with#special$chars| := 5;
#end

/--
info: "program PipeIdent;\n(|name@with#special$chars|) := 5;"
-/
#guard_msgs in
#eval toString testSpecialChars.format

-- Test 4: Pipe-delimited identifier starting with number
def testNumeric := #strata
program PipeIdent;
|123numeric| := 99;
#end

/--
info: "program PipeIdent;\n(|123numeric|) := 99;"
-/
#guard_msgs in
#eval toString testNumeric.format

-- Test 5: Regular identifier (should still work)
def testRegular := #strata
program PipeIdent;
regularName := 7;
#end

/--
info: "program PipeIdent;\n(regularName) := 7;"
-/
#guard_msgs in
#eval toString testRegular.format

-- Test 6: Pipe-delimited identifier in expression with || operator
-- This tests that || operator is not confused with pipe-delimited identifiers
def testOrOperator := #strata
program PipeIdent;
result := |special-name| || regularName;
#end

/--
info: "program PipeIdent;\n(result) := |special-name| || regularName;"
-/
#guard_msgs in
#eval toString testOrOperator.format

-- Test 7: Pipe-delimited identifiers in addition expression
def testAddition := #strata
program PipeIdent;
sum := |special-name| + |name with spaces|;
#end

/--
info: "program PipeIdent;\n(sum) := |special-name| + |name with spaces|;"
-/
#guard_msgs in
#eval toString testAddition.format

-- Test 8: Complex expression mixing pipe-delimited and regular identifiers
def testMixed := #strata
program PipeIdent;
|result-value| := |x-coord| + yCoord || |123start|;
#end

/--
info: "program PipeIdent;\n(|result-value|) := |x-coord| + yCoord || |123start|;"
-/
#guard_msgs in
#eval toString testMixed.format

-- Test 9: Pipe-delimited identifier with Unicode characters
def testUnicode := #strata
program PipeIdent;
|name-with-émojis-🎉| := 42;
#end

/--
info: "program PipeIdent;\n(|name-with-émojis-🎉|) := 42;"
-/
#guard_msgs in
#eval toString testUnicode.format

-- Test 10: Comprehensive test with all features
def testComprehensive := #strata
program PipeIdent;
|x-coordinate| := 10;
|first name| := 100;
|value@index| := 5;
|123start| := 42;
regularVar := 7;
|special-result| := regularVar + |x-coordinate|;
boolResult := |special-result| || regularVar;
|++| := 1;
operatorSum := |++| + regularVar;
#end

/--
info: "program PipeIdent;\n(|x-coordinate|) := 10;(|first name|) := 100;(|value@index|) := 5;(|123start|) := 42;(regularVar) := 7;(|special-result|) := regularVar + |x-coordinate|;(boolResult) := |special-result| || regularVar;(|++|) := 1;(operatorSum) := |++| + regularVar;"
-/
#guard_msgs in
#eval toString testComprehensive.format

-- Test that we can construct expressions programmatically
def manualConstruction : PipeIdent.Expression Unit :=
  .add ()
    (.var () ⟨(), "special-name"⟩)
    (.var () ⟨(), "another-name"⟩)

-- Test that the AST structure is correct
example : PipeIdent.Expression Unit := .var () ⟨(), "x-coordinate"⟩
example : PipeIdent.Expression Unit := .var () ⟨(), "name with spaces"⟩
example : PipeIdent.Expression Unit := .var () ⟨(), "123numeric"⟩

-- Test 11: Escape sequences (SMT-LIB 2.6 spec)
def testEscapes := #strata
program PipeIdent;
|name\|with\|pipes| := 1;
|path\\to\\file| := 2;
result := |name\|with\|pipes| + |path\\to\\file|;
#end

/--
info: "program PipeIdent;\n(|name\\|with\\|pipes|) := 1;(|path\\\\to\\\\file|) := 2;(result) := |name\\|with\\|pipes| + |path\\\\to\\\\file|;"
-/
#guard_msgs in
#eval toString testEscapes.format


-- Test 12: Single | operator works (bitwise OR)
def testBitwiseOr := #strata
program PipeIdent;
result := a | b;
#end

/--
info: "program PipeIdent;\n(result) := a | b;"
-/
#guard_msgs in
#eval toString testBitwiseOr.format

-- Test 13: Both | operator and |identifier| coexist
def testBothOperators := #strata
program PipeIdent;
|x-value| := 10;
|y-value| := 20;
result := |x-value| | |y-value|;
#end

/--
info: "program PipeIdent;\n(|x-value|) := 10;(|y-value|) := 20;(result) := |x-value| | |y-value|;"
-/
#guard_msgs in
#eval toString testBothOperators.format

-- Test 14: Whitespace after | makes it an operator
def testOperatorWhitespace := #strata
program PipeIdent;
x := a | b;
y := c| d;
#end

/--
info: "program PipeIdent;\n(x) := a | b;(y) := c | d;"
-/
#guard_msgs in
#eval toString testOperatorWhitespace.format
