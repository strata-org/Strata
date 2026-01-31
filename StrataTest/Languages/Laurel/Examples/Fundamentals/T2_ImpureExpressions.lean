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

procedure multipleAssignments() {
  var x: int;
  var y: int := ((x := 1;) + x) + (x := 2;);
  assert y == 4;
}
"

#guard_msgs (error, drop all) in
#eval! testInputWithOffset "NestedImpureStatements" program 14 processLaurelFile


end Laurel
