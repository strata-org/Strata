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

// Function with valid constrained return — constraint not checked (not yet supported)
function goodFunc(): nat { 3 };
//       ^^^^^^^^ error: constrained return types on functions are not yet supported

// Function with invalid constrained return — constraint not checked (not yet supported)
function badFunc(): nat { -1 };
//       ^^^^^^^ error: constrained return types on functions are not yet supported

// Caller of constrained function — body is inlined, caller sees actual value
procedure callerGood()
  opaque
{
  var x: int := goodFunc();
  assert x >= 0
};
"

#guard_msgs(drop info, error) in
#eval testInputWithOffset "ConstrainedTypes" program 14 processLaurelFile

end Laurel
end Strata
