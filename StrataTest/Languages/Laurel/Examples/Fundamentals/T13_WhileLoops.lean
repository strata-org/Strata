/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import StrataTest.Util.TestDiagnostics
import StrataTest.Languages.Laurel.TestExamples

open StrataTest.Util

namespace Strata
namespace Laurel

def whileLoopsProgram := r"
procedure countDown() {
    var i: int := 3;
    while(i > 0)
      invariant i >= 0
    {
        i := i - 1;
    }
    assert i == 0;
}

procedure countUp() {
    var n: int := 5;
    var i: int := 0;
    while(i < n)
      invariant i >= 0
      invariant i <= n
    {
        i := i + 1;
    }
    assert i == n;
}
"

#guard_msgs(drop info, error) in
#eval testInputWithOffset "WhileLoops" whileLoopsProgram 14 processLaurelFile

end Laurel
