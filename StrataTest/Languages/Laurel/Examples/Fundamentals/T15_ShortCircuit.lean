/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import StrataTest.Util.TestDiagnostics
import StrataTest.Languages.Laurel.TestExamples

open StrataTest.Util

namespace Strata
namespace Laurel

def shortCircuitProgram := r"
function mustNotCall(x: int): int
  requires false
{ x };

// AndThen: false && mustNotCall(0) > 0 — dead branch not evaluated
procedure testAndThenShortCircuit() {
  var b: bool := false && mustNotCall(0) > 0;
  assert !b
};

// OrElse: true || mustNotCall(0) > 0 — dead branch not evaluated
procedure testOrElseShortCircuit() {
  var b: bool := true || mustNotCall(0) > 0;
  assert b
};

// Division by zero in dead branch — not evaluated
procedure testAndThenDivByZero() {
  assert !(false && 1 / 0 > 0)
};

procedure testOrElseDivByZero() {
  assert true || 1 / 0 > 0
};
"

#guard_msgs(drop info, error) in
#eval testInputWithOffset "ShortCircuit" shortCircuitProgram 15 processLaurelFile

end Laurel
end Strata
