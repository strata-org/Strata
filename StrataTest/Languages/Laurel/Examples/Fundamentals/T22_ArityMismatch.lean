/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import StrataTest.Util.TestDiagnostics
import StrataTest.Languages.Laurel.TestExamples

open StrataTest.Util

namespace Strata
namespace Laurel

def arityMismatchProgram := r"
function f(x: int): int { x };

procedure caller()
  opaque
{
  var y: int := f(1, 2)
};
"

/--
error: ArityMismatch(79-100) ❌ Type checking error.
Impossible to unify int with (arrow int $__ty35).
-/
#guard_msgs(drop info, error) in
#eval testInputWithOffset "ArityMismatch" arityMismatchProgram 14 processLaurelFile

def outputArityMismatchProgram := r"
procedure twoReturns() returns (a: int, b: int)
  opaque
  ensures a == 1 && b == 2;

procedure mismatch()
  opaque
{
  var x: int;
  assign x := twoReturns()
//^^^^^^^^^^^^^^^^^^^^^^^^ error: Assignment target count mismatch
};
"

#guard_msgs(drop info, error) in
#eval testInputWithOffset "OutputArityMismatch" outputArityMismatchProgram 30 processLaurelFile
