/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import StrataTest.Util.TestDiagnostics
import StrataTest.Languages.Laurel.TestExamples

open StrataTest.Util

namespace Strata
namespace Laurel

def program := r"
composite Top {
  var xValue: int
}

composite Left extends Top {}
composite Right extends Top {}
composite Bottom extends Left, Right {}

procedure diamondField(b: Bottom) {
  b#xValue := 1;
//  ^^^^^^ error: fields that are inherited multiple times can not be accessed.
}
"

#guard_msgs (drop info) in
#eval testInputWithOffset "InheritanceError" program 14 processLaurelFile
