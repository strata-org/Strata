/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import StrataTest.Util.TestLaurel

open StrataTest.Util
open Strata

/-- info: 8:9-16  error: constrained return types on functions are not yet supported
5:9-17  error: constrained return types on functions are not yet supported -/
#guard_msgs in
#eval testLaurelExpect <|
#strata_expect
program Laurel;
constrained nat = x: int where x >= 0 witness 0

// Function with valid constrained return — constraint not checked (not yet supported)
function goodFunc(): nat { 3 };

// Function with invalid constrained return — constraint not checked (not yet supported)
function badFunc(): nat { -1 };

// Caller of constrained function — body is inlined, caller sees actual value
procedure callerGood()
  opaque
{
  var x: int := goodFunc();
  assert x >= 0
};
#end
