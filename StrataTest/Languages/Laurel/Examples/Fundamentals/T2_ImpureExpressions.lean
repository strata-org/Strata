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
  var y := 0;
  var z := if (x > 0) { y := y + 1; } else { 0 };
  if (x > 0) {
    assert y == 1;
  } else {
    assert z == 0;
    assert y == 0;
//  ^^^^^^^^^^^^^^ error: assertion does not hold
  }
}
"

#eval! testInputWithOffset "NestedImpureStatements" program 14 processLaurelFile


end Laurel
