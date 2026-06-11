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

-- Over-arity is now caught in the resolution pass (type checking added to
-- Laurel resolution): calling `f` (1 parameter) with 2 arguments is rejected
-- with the resolution-pass arity diagnostic. Because resolution errors short-
-- circuit the pipeline before Core translation, the call no longer reaches the
-- Core unifier, so the old `ArityMismatch ❌ Type checking error / Impossible to
-- unify …` message is replaced by the resolution diagnostic below.
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
