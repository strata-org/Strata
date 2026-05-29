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
// The above limitation is because Core does not yet support functions with postconditions
  requires x > 0
  opaque
  ensures r > 0
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
