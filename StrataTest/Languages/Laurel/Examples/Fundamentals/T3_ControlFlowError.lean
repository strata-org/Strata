/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import StrataTest.Util.TestDiagnostics
import StrataTest.Languages.Laurel.TestExamples

open StrataTest.Util
open Strata

namespace Strata.Laurel

def program := r"
function assertAndAssumeInFunctions(a: int) returns (r: int)
{
  assert 2 == 3;
  assume true;
  a
};

// Lettish bindings in functions not yet supported
// because Core expressions do not support let bindings
function letsInFunction() returns (r: int) {
  var x: int := 0;
//^^^^^^^^^^^^^^^ error: local variables in functions are not YET supported
  var y: int := x + 1;
//^^^^^^^^^^^^^^^^^^^ error: local variables in functions are not YET supported
  var z: int := y + 1;
//^^^^^^^^^^^^^^^^^^^ error: local variables in functions are not YET supported
  z
};

function localVariableWithoutInitializer(): int {
  var x: int;
//^^^^^^^^^^ error: local variables in functions must have initializers
  3
};

function deadCodeAfterIfElse(x: int) returns (r: int) {
  if x > 0 then { return 1 } else { return 2 };
//                ^^^^^^^^ error: Return statement with value should have been eliminated by EliminateValueReturns pass
//                                  ^^^^^^^^ error: Return statement with value should have been eliminated by EliminateValueReturns pass
//^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ error: if-then-else only supported as the last statement in a block
  return 3
};
"

#guard_msgs (error, drop all) in
#eval! testInputWithOffset "ControlFlowError" program 14 processLaurelFile
