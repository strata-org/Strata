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
//^^^^^^ error: ending a transparent body with a Assign statement is not supported
};

procedure transparentBodyNoOuts()
{
  assert true;
  3
//^ error: ending a transparent body with a LiteralInt statement is not supported
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
