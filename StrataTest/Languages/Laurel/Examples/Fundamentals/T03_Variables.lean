/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import StrataTest.Util.TestDiagnostics
import StrataTest.Languages.Laurel.TestExamples

open StrataTest.Util
open Strata

namespace Strata.Laurel

def program: String := r"
procedure NestedImpureStatements() {
  var y: int := 0;
  var x: int := y;
  var z: int := y := y + 1;;
    assert x == y;
//  ^^^^^^^^^^^^^^ error: assertion does not hold
  assert z == y;
}

// Regression test: assignment lifting after a conditional should work
procedure AssignmentAfterConditional(x: int) {
  var y: int := 0;
  if (x > 0) { y := 1; }
  var z: int := y := y + 1;;
  assert z == y;
}
"

#guard_msgs (error, drop all) in
#eval! testInputWithOffset "Variables" program 14 processLaurelFile


end Laurel
