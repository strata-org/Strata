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
procedure divide(x: int, y: int) returns (result: int)
  requires y != 0 propertySummary "divisor must be non-zero"
//         ^^^^^^ error: divisor must be non-zero does not hold
{
  assert y != 0 propertySummary "divisor is zero";
//^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ error: divisor is zero does not hold
  return x;
};

procedure checkPositive(n: int) returns (ok: bool)
  requires n >= 0 propertySummary "input must be non-negative"
//         ^^^^^^ error: input must be non-negative does not hold
{
  assert n >= 0 propertySummary "n is negative";
//^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ error: n is negative does not hold
  return true;
};
"

#guard_msgs (drop info, error) in
#eval testInputWithOffset "PropertySummary" program 14 processLaurelFile

end Strata.Laurel
