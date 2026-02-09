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
procedure hasRequires(x: int) returns (r: int)
  requires x > 2
//         ^^^^^ error: assertion does not hold
// Core does not seem to report precondition errors correctly.
// This should occur at the call site and with a different message
{
  assert x > 0;
    assert x > 3;
//  ^^^^^^^^^^^^^ error: assertion does not hold
  x + 1
}

procedure caller() {
  var x: int := hasRequires(1);
  var y: int := hasRequires(3);
}
"

#guard_msgs (drop info, error) in
#eval testInputWithOffset "Preconditions" program 14 processLaurelFile
