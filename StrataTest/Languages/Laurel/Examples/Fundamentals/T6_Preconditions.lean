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

/-
Translation towards SMT:

function hasRequires_requires(x: int): boolean {
  x > 2
}

function hasRequires(x: int): int {
  x + 1
}

proof hasRequires_requires {
  assert 1 == 1;
}

proof hasRequires_body {
  var x: int;
  assume hasRequires_requires();
  assert x > 0; // pass
  assert x > 3; // fail
}

proof caller_body {
  var hasRequires_arg1 := 1;
  assert hasRequires_ensures(hasRequires_arg1); // fail
  var x := hasRequires(hasRequires_arg1);

  var hasRequires_arg1_2 := 3;
  assert hasRequires_ensures(hasRequires_arg1_2); // pass
  var y: int := hasRequires(hasRequires_arg1_2);
}
-/
