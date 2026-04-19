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
  ensures true
{
  return 0
};

// Pure path: function with requires false

procedure testAndThenFunc()
  ensures true
{
  var b: bool := false && mustNotCallFunc(0) > 0;
//^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ error: assertion does not hold
// TODO caused by a bug in Core: https://github.com/strata-org/Strata/issues/697
  assert !b
};

procedure testOrElseFunc()
  ensures true
{
  var b: bool := true || mustNotCallFunc(0) > 0;
//^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ error: assertion does not hold
// TODO caused by a bug in Core: https://github.com/strata-org/Strata/issues/697
  assert b
};

procedure testImpliesFunc()
  ensures true
{
  var b: bool := false ==> mustNotCallFunc(0) > 0;
  assert b
};

// Pure path: division by zero

procedure testAndThenDivByZero()
  ensures true
{
  assert !(false && 1 / 0 > 0)
//^^^^^^^^^^^^^^^^^^^^^^^^^^^^ error: assertion does not hold
// TODO caused by a bug in Core.
};

procedure testOrElseDivByZero()
  ensures true
{
  assert true || 1 / 0 > 0
//^^^^^^^^^^^^^^^^^^^^^^^^ error: assertion does not hold
// TODO caused by a bug in Core: https://github.com/strata-org/Strata/issues/697
};

procedure testImpliesDivByZero()
  ensures true
{
  assert false ==> 1 / 0 > 0
};

// Imperative path: procedure with requires false

procedure testAndThenProc()
  ensures true
{
  var b: bool := false && mustNotCallProc() > 0;
  assert !b
};

procedure testOrElseProc()
  ensures true
{
  var b: bool := true || mustNotCallProc() > 0;
  assert b
};

procedure testImpliesProc()
  ensures true
{
  var b: bool := false ==> mustNotCallProc() > 0;
  assert b
};
"

#guard_msgs(drop info, error) in
#eval testInputWithOffset "ShortCircuit" shortCircuitProgram 15 processLaurelFile

end Laurel
end Strata
