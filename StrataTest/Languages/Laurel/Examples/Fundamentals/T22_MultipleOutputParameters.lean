/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import StrataTest.Util.TestDiagnostics
import StrataTest.Languages.Laurel.TestExamples

open StrataTest.Util
open Strata

namespace Strata.Laurel

def multiOutputProgram := r"
procedure twoOutputs(x: int) returns (a: int, b: int)
  ensures a == x + 1
  ensures b == x + 2
{
  a := x + 1;
  b := x + 2
};

procedure callTwoOutputs()
{
  var p: int, q: int := twoOutputs(10);
  assert p == 11;
  assert q == 12
};

procedure callTwoOutputsFailing()
{
  var p: int, q: int := twoOutputs(10);
  assert p == 99
//^^^^^^^^^^^^^^ error: assertion could not be proved
};
"

#guard_msgs (drop info, error) in
#eval testInputWithOffset "MultiOutput" multiOutputProgram 14 processLaurelFile

end Strata.Laurel
