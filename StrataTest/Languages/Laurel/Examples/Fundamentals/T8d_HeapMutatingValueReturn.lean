/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import StrataTest.Util.TestDiagnostics
import StrataTest.Languages.Laurel.TestExamples

open StrataTest.Util
open Strata

namespace Strata.Laurel

def heapMutatingValueReturnProgram := r"
composite Container {
  var value: int
}

procedure setAndReturn(c: Container, x: int) returns (r: int)
  opaque
  ensures r == x
  modifies c
{
  c#value := x;
  return x
};

procedure setAndReturnBuggy(c: Container, x: int) returns (r: int)
  opaque
  ensures r == x + 1
//        ^^^^^^^^^^ error: assertion does not hold
  modifies c
{
  c#value := x;
  return x
};
"

#guard_msgs (drop info, error) in
#eval testInputWithOffset "HeapMutatingValueReturn" heapMutatingValueReturnProgram 15 processLaurelFile

end Strata.Laurel
