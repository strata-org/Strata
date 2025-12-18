/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.DDM.Integration.Lean

open Strata

/-!
# Bitwise OR Dialect Test

Tests that pipe-delimited identifiers work correctly even when | is defined
as a single-character operator token in the dialect.
-/

#load_dialect "../../Examples/dialects/BitwiseOr.dialect.st"

namespace BitwiseOr

#strata_gen BitwiseOr

-- Test 1: Single | operator works
def testBitwiseOr := #strata
program BitwiseOr;
result := a | b;
#end

/--
info: "program BitwiseOr;\n(result) := a | b;"
-/
#guard_msgs in
#eval toString testBitwiseOr.format

-- Test 2: Pipe-delimited identifiers still work
def testPipeIdent := #strata
program BitwiseOr;
|special-name| := 42;
#end

/--
info: "program BitwiseOr;\n(|special-name|) := 42;"
-/
#guard_msgs in
#eval toString testPipeIdent.format

-- Test 3: Both can coexist
def testBoth := #strata
program BitwiseOr;
|x-value| := 10;
|y-value| := 20;
result := |x-value| | |y-value|;
#end

/--
info: "program BitwiseOr;\n(|x-value|) := 10;(|y-value|) := 20;(result) := |x-value| | |y-value|;"
-/
#guard_msgs in
#eval toString testBoth.format

-- Test 4: Whitespace after | makes it an operator
def testWhitespace := #strata
program BitwiseOr;
x := a | b;
y := c| d;
#end

/--
info: "program BitwiseOr;\n(x) := a | b;(y) := c | d;"
-/
#guard_msgs in
#eval toString testWhitespace.format

end BitwiseOr
