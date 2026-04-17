/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import StrataTest.Util.TestDiagnostics
import StrataTest.Languages.Laurel.TestExamples

open StrataTest.Util

namespace Strata
namespace Laurel

def inferTypeErrorProgram := r"
procedure foo() {
  <?>
//^^^ error: could not infer type
};
"

#guard_msgs(drop info, error) in
#eval testInputWithOffset "InferTypeError" inferTypeErrorProgram 14 processLaurelFile
