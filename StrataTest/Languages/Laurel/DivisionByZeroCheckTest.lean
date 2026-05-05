/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import StrataTest.Util.TestDiagnostics
import StrataTest.Languages.Laurel.TestExamples

open StrataTest.Util

namespace Strata.Laurel

/-! ## End-to-end test: safe division (no errors) and unsafe division (error)

Division and modulo in Laurel translate to Core's safe operators, which have
built-in preconditions (divisor ≠ 0). The PrecondElim transform automatically
generates verification conditions for these preconditions.
-/

def e2eProgram := r"
procedure safeDivision()
  opaque
{
  var x: int := 10;
  var y: int := 2;
  var z: int := x / y;
  assert z == 5
};

// Error ranges are too wide because Core does not use expression locations
procedure unsafeDivision(x: int)
  opaque
{
  var z: int := 10 / x
//^^^^^^^^^^^^^^^^^^^^ error: assertion does not hold
// Error ranges are too wide because Core does not use expression locations
};

function pureDiv(x: int, y: int): int
  requires y != 0
{
  x / y
};

procedure callPureDivSafe()
  opaque
{
  var z: int := pureDiv(10, 2);
  assert z == 5
};

procedure callPureDivUnsafe(x: int)
  opaque
{
  var z: int := pureDiv(10, x)
//^^^^^^^^^^^^^^^^^^^^^^^^^^^^ error: assertion does not hold
// Error ranges are too wide because Core does not use expression locations
};
"

#guard_msgs(drop info, error) in
#eval testInputWithOffset "DivByZeroE2E" e2eProgram 22 processLaurelFile

end Laurel
