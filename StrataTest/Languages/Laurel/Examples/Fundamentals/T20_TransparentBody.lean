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
procedure transparentBody(): int
{
  assert true;
  3
};

procedure tranparentCaller(): int {
  transparentBody()
};

procedure transparentCallerCaller() opaque {
  var x: int := tranparentCaller();
  assert x == 3
};
"

#guard_msgs(drop info, error) in
#eval testInputWithOffset "TransparentBody" transparentBodyProgram 14 processLaurelFile

end Laurel
