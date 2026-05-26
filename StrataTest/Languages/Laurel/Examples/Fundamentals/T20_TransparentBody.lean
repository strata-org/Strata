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
procedure transparentBody(): int
{
  assert true;
  3
};

procedure transparentProcedureCaller() opaque {
  var x: int := transparentBody();
  assert x == 3
};

// No support for transparent void procedures yet
// procedure transparentBody()
// {
//   assert true
// };
"

#guard_msgs(drop info, error) in
#eval testInputWithOffset "TransparentBody" transparentBodyProgram 14 processLaurelFile

end Laurel
