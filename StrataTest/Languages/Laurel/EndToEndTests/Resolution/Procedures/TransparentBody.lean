/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import StrataTest.Util.TestLaurel

open StrataTest.Util
open Strata

#eval testLaurel <|
#strata
program Laurel;
procedure assertAndAssumeInFunctions(a: int) returns (r: int)
{
  assert 2 == 3;
  assume true;
  return a
};

procedure letsInFunction() returns (r: int) {
  var x: int := 0;
  var y: int := x + 1;
  var z: int := y + 1;
  return z
};

procedure callLetsInFunction() opaque {
  var x: int := letsInFunction();
  assert x == 2
};

procedure localVariableWithoutInitializer(): int {
  var x: int;
//^^^^^^^^^^ error: local variables must have initializers in transparent bodies or contracts
  return 3
};
#end

/-! ## if-then-else must be the last statement in a transparent body -/

#eval testLaurel <|
#strata
program Laurel;

procedure deadCodeAfterIfElse(x: int) returns (r: int) {
  if x > 0 then { return 1 } else { return 2 };
//^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ error: in a transparent body, if-then-else is only supported as the last statement in a block
  return 3
};

procedure transparentBodyMultipleOuts() returns (q: int, r: int)
{
  assert true;
  q := 3;
  r := 2
//^^^^^^ error: ending a transparent body with a Assign statement is not supported
};

procedure transparentBodyNoOuts()
{
  assert true;
  3
//^ error: ending a transparent body with a LiteralInt statement is not supported
};

procedure transparentProcedureCaller() opaque {
  assign var x: int, var y: int := transparentBodyMultipleOuts();
  assert x == 3;
  assert y == 2;

  transparentBodyNoOuts()
};
#end
