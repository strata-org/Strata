/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import StrataTest.Util.TestDiagnostics
import StrataTest.Languages.Laurel.TestExamples

open StrataTest.Util
open Strata

namespace Laurel

def program: String := r"
procedure nestedImpureStatements(x: int) {
  var y := 0;
  if (y := y + 1; == { y := y + 1; x }) {
    assert x == 1;
    assert y == x + 1;
  } else {
    assert x != 1;
  }
  assert y == 2;
    assert false;
//  ^^^^^^^^^^^^^ error: assertion does not hold
}
"

#eval! testInputWithOffset "NestedImpureStatements" program 14 processLaurelFile


end Laurel
