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

def transparentBodyProgram := r"
procedure transparentBodyMultipleOuts() returns (q: int, r: int)
{
  assert true;
  q := 3;
//^^^^^^ error: destructive assignments are not supported in transparent bodies or contracts
  r := 2
};

procedure transparentBodyNoOuts()
{
  assert true
};

procedure transparentProcedureCaller() opaque {
  assign var x: int, var y: int := transparentBodyMultipleOuts();
  assert x == 3;
  assert y == 2;

  transparentBodyNoOuts()
};
"

#guard_msgs(drop info, error) in
#eval testInputWithOffset "TransparentBody" transparentBodyProgram 14 processLaurelFile

end Laurel
