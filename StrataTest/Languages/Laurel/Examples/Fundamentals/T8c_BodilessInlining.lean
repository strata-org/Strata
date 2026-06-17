/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import StrataTest.Util.TestLaurel

open StrataTest.Util
open Strata

/-! # Bodiless Procedure Inlining Test

Verifies that inlining a bodiless Laurel procedure does not introduce
`assume false`. Previously, bodiless procedures had `assume false` as their
body, so inlining would make everything after the call trivially provable.
Now the body assumes the postconditions instead, so `assert false` after
the inlined call is correctly rejected. -/

#guard_msgs (drop info) in
#eval testLaurel (options := { translateOptions := { inlineFunctionsWhenPossible := true } }) <|
#strata
program Laurel;
procedure bodilessProcedure() returns (r: int)
  opaque
  ensures r > 0
;

procedure caller()
  opaque
{
  var x: int := bodilessProcedure();
  assert x > 0;
  assert false
//^^^^^^^^^^^^ error: assertion could not be proved
};
#end
