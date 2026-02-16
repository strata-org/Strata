/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import StrataTest.Util.TestDiagnostics
import StrataTest.Languages.Laurel.TestExamples

open StrataTest.Util

namespace Strata
namespace Laurel

/-!
This test demonstrates an issue with the Box datatype encoding.

When accessing a field like `c#intValue`, the Laurel translator generates:
  Box..intVal(heap[c][Container..intValue])

The `Box..intVal` destructor has a precondition requiring `Box..isBoxInt(x)`.
However, there's no assumption that `heap[c][Container..intValue]` is a BoxInt,
even though the field is declared as type `int`.

This causes PrecondElim to generate unprovable assertions.
-/

def program := r"
composite C {
  var x: int
}

procedure getX(c: C) returns (r: int) {
  r := c#x;
}
"

#guard_msgs(drop info, error) in
#eval testInputWithOffset "BoxPreconditionIssue" program 10 processLaurelFile

end Laurel
end Strata
