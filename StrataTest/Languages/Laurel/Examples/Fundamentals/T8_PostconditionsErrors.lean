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

// Function with ensures that the body does NOT satisfy
function badPostcond(x: int) returns (r: int)
//       ^^^^^^^^^^^ error: assertion does not hold
  ensures r > x
{
  x
};
"

#guard_msgs (drop info, error) in
#eval testInputWithOffset "Postconditions" program 14 processLaurelFile
