/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import StrataTest.Util.TestLaurel

open StrataTest.Util
open Strata

#eval testLaurelExpect <|
#strata_expect
program Laurel;
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

function localVariableWithoutInitializer(): int {
  var x: int;
//^^^^^^^^^^ error: local variables in functions must have initializers
  3
};

function deadCodeAfterIfElse(x: int) returns (r: int) {
  if x > 0 then { return 1 } else { return 2 };
//^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ error: if-then-else only supported as the last statement in a block
  return 3
};
#end
