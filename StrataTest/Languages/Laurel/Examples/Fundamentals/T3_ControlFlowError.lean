/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

meta import all StrataTest.Util.TestDiagnostics
meta import all StrataTest.Languages.Laurel.TestExamples

meta section

open StrataTest.Util
open Strata

namespace Strata.Laurel

def program := r"
procedure localVariableWithoutInitializer(): int {
  var x: int;
//^^^^^^^^^^ error: local variables must have initializers in transparent bodies or contracts
  return 3
};
"

#guard_msgs (error, drop all) in
#eval! testInputWithOffset "ControlFlowError" program 17 processLaurelFile
