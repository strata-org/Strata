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
function assertAndAssumeInFunctions(a: int) returns (r: int)
{
  assert 2 == 3;
//^^^^^^^^^^^^^^ error: asserts are not YET supported in functions or contracts
  assume true;
//^^^^^^^^^^^^ error: assumes are not YET supported in functions or contracts
  a
}
"

#guard_msgs (error, drop all) in
#eval! testInputWithOffset "ControlFlowError" program 14 processLaurelFile
