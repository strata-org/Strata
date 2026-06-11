/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

meta import all StrataTest.Util.TestDiagnostics
meta import all StrataTest.Languages.Laurel.TestExamples

meta section

open StrataTest.Util

namespace Strata
namespace Laurel

def arityMismatchProgram := r"
function f(x: int): int { x };

procedure caller()
  opaque
{
  var y: int := f(1, 2)
//              ^^^^^^^ error: call to 'f' expects 1 argument(s) but 2 were provided
};
"

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
//            ^^^^^^^^^^^^ error: expected 'int', got '(int, int)'
};
"

#guard_msgs(drop info, error) in
#eval testInputWithOffset "OutputArityMismatch" outputArityMismatchProgram 30 processLaurelFile
