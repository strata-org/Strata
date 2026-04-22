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
procedure multipleReturns() returns (x: int, y: int, z: int)
  ensures x == 1 && y == 2 && z == 3;

procedure caller() {
  var y: int;
  var x: int, y, var z: int := multipleReturns();
  assert x == 1;
  assert y == 2;
  assert z == 3
};
"

#guard_msgs (drop info, error) in
#eval testInputWithOffset "MultipleReturns" program 14 processLaurelFile

end Strata.Laurel
