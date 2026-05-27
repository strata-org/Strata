/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import StrataTest.Util.TestLaurel

open StrataTest.Util
open Strata

#eval testLaurelExpect <|
#strata_expect
program Laurel;
constrained nat = x: int where x >= 0 witness 0

// Function with valid constrained return — constraint not checked (not yet supported)
function goodFunc(): nat { 3 };
//       ^^^^^^^^ error: constrained return types on functions are not yet supported

// Function with invalid constrained return — constraint not checked (not yet supported)
function badFunc(): nat { -1 };
//       ^^^^^^^ error: constrained return types on functions are not yet supported

// Caller of constrained function — body is inlined, caller sees actual value
procedure callerGood()
  opaque
{
  var x: int := goodFunc();
  assert x >= 0
};
#end
