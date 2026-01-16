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
procedure syntacticallyABoogieFunction(x: int): int {
  x + 1
}

procedure noFunctionBecauseContract() returns (r: int)
  ensures r > 0
{
  10
}

procedure noFunctionBecauseStatements(): int {
  var x: int := 3;
  x + 1
}

procedure caller() {
  assert syntacticallyABoogieFunction(1) == 2;
  var x: int := noFunctionBecauseContract();
  assert x > 0;
  var y: int := noFunctionBecauseStatements();
  assert y == 4;
}
"

-- #guard_msgs(drop info, error) in
#eval! testInputWithOffset "T5_ProcedureCallsBoogie" program 14 processLaurelFile
