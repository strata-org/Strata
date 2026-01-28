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
procedure conditionalAssignmentInExpression(x: int) {
  var y: int := 0;
  var z: int := if (x > 0) { y := y + 1; } else { 0 };
//                           ^^^^^^^^^^^ error: Could not lift assigment in expression that is evaluated conditionally
  if (x > 0) {
    assert y == 1;
  } else {
    assert z == 0;
    assert y == 0;
  }
}
"

#guard_msgs(drop info, error) in
#eval! testInputWithOffset "T2_ImpureExpressionsNotSupported" program 14 processLaurelFile


end Laurel
