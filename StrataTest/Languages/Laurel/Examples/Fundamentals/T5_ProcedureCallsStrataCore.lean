/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

/-
The purpose of this test is to ensure we're using functions and procedures as well as
Strata Core supports them. When Strata Core makes procedures more powerful, so we
won't need functions any more, then this test can be merged into other tests.
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
  return 10;
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
//. ^^^^^^^^^^^^^^ error: assertion does not hold
}
"

#guard_msgs(drop info, error) in
#eval! testInputWithOffset "T5_ProcedureCallsStrataCore" program 20 processLaurelFile
