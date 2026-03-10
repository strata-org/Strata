/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import StrataTest.Util.TestDiagnostics
import StrataTest.Languages.Laurel.TestExamples

open StrataTest.Util

namespace Strata
namespace Laurel

def quantifiersProgram := r"
procedure testForall() {
    assert forall(x: int) => x + 0 == x;
}

procedure testExists() {
    assert exists(x: int) => x == 42;
}

procedure testQuantifierInContract(n: int)
  requires n > 0
  ensures forall(i: int) => i >= 0 ==> i < n ==> i < n + 1
{
}
"

#guard_msgs(drop info, error) in
#eval testInputWithOffset "Quantifiers" quantifiersProgram 14 processLaurelFile

end Laurel
