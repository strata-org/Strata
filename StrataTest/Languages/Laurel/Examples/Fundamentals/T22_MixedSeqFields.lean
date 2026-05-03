/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import StrataTest.Util.TestDiagnostics
import StrataTest.Languages.Laurel.TestExamples

open StrataTest.Util

namespace Strata
namespace Laurel

-- Regression: two `Seq<T>` fields with different `T` on the same composite
-- must produce distinct Box constructor names in HeapParameterization.
-- Before the fix, both shared the name "BoxSeq" and Core type-checking
-- failed on the element-type mismatch. After the fix the name encodes the
-- element type (`BoxSeq_int`, `BoxSeq_bool`, ...).
def mixedSeqFieldsProgram := r"
composite Both {
  var a: Seq<int>
  var b: Seq<bool>
}

procedure touch(x: Both) {
  x#a := [1];
  x#b := [true]
};
"

#guard_msgs(drop info, error) in
#eval testInputWithOffset "MixedSeqFields" mixedSeqFieldsProgram 14 processLaurelFile

end Laurel
end Strata
