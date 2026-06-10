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
procedure letExpressionsInTransparent() returns (r: int) {
  var x: int := 0;
  var y: int := x + 1;
  var z: int := y + 1;
  return z
};

procedure callLetExpressionsInTransparent() opaque {
  var x: int := letExpressionsInTransparent();
  assert x == 2
};
"

#guard_msgs (error, drop all) in
#eval! testInputWithOffset "ControlFlowError" program 14 processLaurelFile
