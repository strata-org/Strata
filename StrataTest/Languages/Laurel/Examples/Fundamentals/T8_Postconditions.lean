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
procedure opaqueBody(x: int) returns (r: int)
// the presence of the ensures make the body opaque. we can consider more explicit syntax.
  ensures r > 0
{
  if (x > 0) { r := x; }
  else { r := 1; }
}

procedure callerOfOpaqueProcedure() {
  var x: int := opaqueBody(3);
  assert x > 0;
  assert x == 3;
//^^^^^^^^^^^^^^ error: assertion does not hold
}

procedure invalidPostcondition(x: int)
    ensures false
//          ^^^^^ error: assertion does not hold
{
}

function opaqueFunction(x: int) returns (r: int)
  requires x > 0
  ensures r > 0
{
  x
}

procedure callerOfOpaqueFunction() {
  var x: int := opaqueFunction(3);
  assert x > 0;
// The following assert should fail but it does not,
// because Core does not support opaque functions
//  assert x == 3;
}
"

#guard_msgs (drop info, error) in
#eval testInputWithOffset "Postconditions" program 14 processLaurelFile
