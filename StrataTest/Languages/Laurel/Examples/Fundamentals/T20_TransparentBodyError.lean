/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import StrataTest.Util.TestDiagnostics
import StrataTest.Languages.Laurel.TestExamples

open StrataTest.Util

namespace Strata
namespace Laurel

def transparentBodyProgram := r"
procedure transparentBodyMultipleOuts() returns (q: int, r: int)
{
  assert true;
  q := 3;
  r := 2
};

// No support for transparent void procedures yet
procedure transparentBody()
{
  assert true
};

procedure transparentProcedureCaller() opaque {
  assign var x: int, var y: int := transparentBodyMultipleOuts();
  assert x == 3;
  assert y == 2;

  transparentBody()
};
"

#guard_msgs(drop info, error) in
#eval testInputWithOffset "TransparentBody" transparentBodyProgram 14 processLaurelFile

end Laurel
