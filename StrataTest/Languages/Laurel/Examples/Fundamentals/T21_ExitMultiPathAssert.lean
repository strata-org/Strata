/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import StrataTest.Util.TestDiagnostics
import StrataTest.Languages.Laurel.TestExamples

open StrataTest.Util

namespace Strata.Laurel

def exitMultiPathProgram := r"
procedure foo(x: int) {
  {
    if x == 0 then {
      exit myBlock
    }
  } myBlock;
  assert false
//^^^^^^^^^^^^ error: assertion does not hold
};
"

#guard_msgs (error, drop all) in
#eval! testInputWithOffset "ExitMultiPathAssert" exitMultiPathProgram 14 processLaurelFile

end Strata.Laurel
