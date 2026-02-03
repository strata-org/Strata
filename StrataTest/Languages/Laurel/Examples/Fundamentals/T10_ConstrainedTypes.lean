/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import StrataTest.Util.TestDiagnostics
import StrataTest.Languages.Laurel.TestExamples

open StrataTest.Util

namespace Strata
namespace Laurel

def program := r"
constrained nat = x: int where x >= 0 witness 0

procedure double(n: nat) returns (r: nat)
  ensures r == n + n
{
    return n + n;
}

procedure testQuantifier()
  ensures forall(n: nat) => n + 1 > 0
{}
"

#guard_msgs(drop info, error) in
#eval testInputWithOffset "ConstrainedTypes" program 14 processLaurelFile
