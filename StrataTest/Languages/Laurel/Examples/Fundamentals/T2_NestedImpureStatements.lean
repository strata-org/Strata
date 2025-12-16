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
procedure nestedImpureStatements(x: int): int {
  var y := 0;
  var z := x;
  if (z := z + 1; == y := y + 1;) {

    assert y == x + 1;
    1
  } else {
    assert y == x + 1;
//  ^^^^^^^^^^^^^^^^^^ error: assertion does not hold
    2
  }
}
"

#eval! testInputWithOffset "NestedImpureStatements" program 15 processLaurelFile

/-
Translation towards SMT:

function nestedImpureStatements(): int {
  var x := 0;
  var y := 0;
  x := x + 1;
  var t1 := x;
  y := x;
  var t2 := x;
  if (t1 == t2) {
    1
  } else {
    2
  }
}

-/

end Laurel
