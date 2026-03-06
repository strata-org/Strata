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
procedure earlyReturnCorrect(x: int) returns (r: int)
  ensures r >= 0
{
  if (x < 0) {
    return -x;
  }
  return x;
}

procedure earlyReturnBuggy(x: int) returns (r: int)
  ensures r >= 0
//        ^^^^^^ error: assertion does not hold
// duplicate due to VCG path duplication (#419):
//        ^^^^^^ error: assertion does not hold
{
  if (x < 0) {
    return x;
  }
  return x;
}
"

#guard_msgs (drop info, error) in
#eval testInputWithOffset "EarlyReturn" program 14 processLaurelFile

end Strata.Laurel
