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
function assertAndAssumeInFunctions(a: int) returns (r: int)
{
  assert 2 == 3;
//^^^^^^^^^^^^^ error: asserts are not YET supported in functions or contracts
  assume true;
//^^^^^^^^^^^ error: assumes are not YET supported in functions or contracts
  a
};

function letsInFunction() returns (r: int) {
  var x: int := 0;
  var y: int := x + 1;
  var z: int := y + 1;
  z
};

procedure callLetsInFunction() opaque {
  var x: int := letsInFunction();
  assert x == 2
};

function localVariableWithoutInitializer(): int {
  var x: int;
//^^^^^^^^^^ error: local variables in functions must have initializers
  3
};
"

#guard_msgs (error, drop all) in
#eval! testInputWithOffset "ControlFlowError" program 14 processLaurelFile
