/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import StrataTest.Util.TestDiagnostics
import StrataTest.Languages.Laurel.TestExamples

open StrataTest.Util

namespace Strata
namespace Laurel

def forLoopProgram := r"
procedure sumToThree()
  opaque
{
  var sum: int := 0;
  for (var i: int := 0; i < 3; i := i + 1)
    invariant sum >= 0
    invariant sum <= 3
    invariant i >= 0
    invariant i <= 3
    invariant sum == i
  {
    sum := sum + 1
  };
  assert sum == 3
};
"

#guard_msgs(drop info, error) in
#eval testInputWithOffset "ForLoop" forLoopProgram 15 processLaurelFile

end Laurel
end Strata
