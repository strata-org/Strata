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
function mustNotCallFunc(x: int): int
  requires false
{ x };

procedure mustNotCallProc(): int
  requires false
{
  return 0
};

// Pure path: function with requires false

procedure testAndThenFunc() {
  var b: bool := false && mustNotCallFunc(0) > 0;
  assert !b
};

procedure testOrElseFunc() {
  var b: bool := true || mustNotCallFunc(0) > 0;
  assert b
};

procedure testImpliesFunc() {
  var b: bool := false ==> mustNotCallFunc(0) > 0;
  assert b
};

// Pure path: division by zero

procedure testAndThenDivByZero() {
  assert !(false && 1 / 0 > 0)
};

procedure testOrElseDivByZero() {
  assert true || 1 / 0 > 0
};

procedure testImpliesDivByZero() {
  assert false ==> 1 / 0 > 0
};

// Imperative path: procedure with requires false

procedure testAndThenProc() {
  var b: bool := false && mustNotCallProc() > 0;
  assert !b
};

procedure testOrElseProc() {
  var b: bool := true || mustNotCallProc() > 0;
  assert b
};

procedure testImpliesProc() {
  var b: bool := false ==> mustNotCallProc() > 0;
  assert b
};
"

#guard_msgs(drop info) in
#eval testInputWithOffset "ShortCircuit" shortCircuitProgram 15 processLaurelFile

end Laurel
end Strata
