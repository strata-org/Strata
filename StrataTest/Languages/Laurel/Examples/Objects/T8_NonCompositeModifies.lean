/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

/-
Regression test for issue #490: a modifies clause referencing a non-composite
type (e.g. a parameter of type int) previously caused an infinite loop
in laurelAnalyze. The fix filters out non-composite modifies entries and emits
a diagnostic error.
-/

import StrataTest.Util.TestDiagnostics
import StrataTest.Languages.Laurel.TestExamples

open StrataTest.Util

namespace Strata
namespace Laurel

def program := r"
composite Container {
  var value: int
}

procedure incWithPrimitiveModifies(x: int) returns (r: int)
  opaque
  modifies x
//         ^ error: modifies clause entry has non-composite type 'int' and will be ignored
{
  r := x + 1
};

procedure modifyContainerAndPrimitive(c: Container, x: int)
  opaque
  modifies c
  modifies x
//         ^ error: modifies clause entry has non-composite type 'int' and will be ignored
{
  c#value := 1
};
"

#guard_msgs (drop info, error) in
#eval testInputWithOffset "NonCompositeModifies" program 22 processLaurelFile
