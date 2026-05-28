/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import StrataTest.Util.TestLaurel

open StrataTest.Util
open Strata

/-! ## Functions with postconditions are not yet supported -/

#eval testLaurel <|
#strata
program Laurel;

function opaqueFunction(x: int) returns (r: int)
//       ^^^^^^^^^^^^^^ error: functions with postconditions are not yet supported
  requires x > 0
  opaque
  ensures r > 0
// The above limitation is because functions in Core do not support postconditions
{
  x
};

procedure callerOfOpaqueFunction()
  opaque
{
  var x: int := opaqueFunction(3);
  assert x > 0;
// The following assertion should fail but does not
  assert x == 3
};
#end
