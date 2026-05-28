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

procedure deadCodeAfterIfElse(x: int) returns (r: int) {
  if x > 0 then { return 1 } else { return 2 };
//^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ error: in a transparent body, if-then-else is only supported as the last statement in a block
  return 3
};
"

#guard_msgs (error, drop all) in
#eval! testInputWithOffset "ControlFlowError" program 14 processLaurelFile
