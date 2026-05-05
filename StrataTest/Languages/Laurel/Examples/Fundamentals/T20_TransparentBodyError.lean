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
procedure transparentBody()
//        ^^^^^^^^^^^^^^^ error: transparent procedures are not yet supported. Add 'opaque' to make the procedure opaque
{
  assert true
};
"

#guard_msgs(drop info, error) in
#eval testInputWithOffset "TransparentBody" transparentBodyProgram 14 processLaurelFile

end Laurel
