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

def inferTypeErrorProgram := r"
procedure foo()
  opaque
{
  <?>
//^^^ error: could not infer type
};
"

#guard_msgs(drop info, error) in
#eval testInputWithOffset "InferTypeError" inferTypeErrorProgram 14 processLaurelFile
