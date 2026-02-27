/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import StrataTest.Util.TestDiagnostics
import StrataTest.Languages.Laurel.TestExamples

open StrataTest.Util
open Strata

namespace Strata.Laurel

def program := r"

function opaqueFunction(x: int) returns (r: int)
//       ^^^^^^^^^^^^^^ error: functions with postconditions are not yet supported
// The above limitation is because Core does not yet support functions with postconditions
  requires x > 0
  ensures r > 0
// The above limitation is because functions in Core do not support postconditions
{
  x
}

procedure callerOfOpaqueFunction() {
  var x: int := opaqueFunction(3);
  assert x > 0;
// The following assertion should fail but does not
// Because Core does not support opaque functions
  assert x == 3;
}
"

#guard_msgs (drop info, error) in
#eval testInputWithOffset "Postconditions" program 14 processLaurelFile
