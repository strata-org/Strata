/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.DDM.Integration.Lean

-- Test dialect with Num
#dialect
dialect TestUnwrap;

// Test Num usage
op index (i : Num) : Command => "index " i ";";
// Test another Num operation
op regular (i : Num) : Command => "regular " i ";";

#end

-- Test that Num works
def testUnwrapProgram := #strata program TestUnwrap; index 42; #end

/--
info: "program TestUnwrap;\nindex 42;"
-/
#guard_msgs in
#eval toString testUnwrapProgram.format

-- Test regular version
def testRegularProgram := #strata program TestUnwrap; regular 99; #end

/--
info: "program TestUnwrap;\nregular 99;"
-/
#guard_msgs in
#eval toString testRegularProgram.format
