/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import StrataLaurel.Tests.Util.TestLaurel

open StrataTest.Util
open Strata

#eval testLaurelExecution {} <|
#strata
program Laurel;
procedure assertAndAssumeInFunctions(a: int) returns (r: int)
{
  assert 2 == 3;
//^^^^^^^^^^^^^ error: assertion does not hold
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

// An unused declaration with no initializer binds nothing and is simply dropped,
// so this body is legal. Reading such a variable is reported instead; see
// `readBeforeAssign` in the verification tests.
procedure localVariableWithoutInitializer(): int {
  var x: int;
  return 3
};
#end

/-! ## A transparent body must yield a single value

`FunctionalRewrite` turns a body into one expression, and an expression evaluates
to a single value, so a body with several outputs cannot be functionalized. (A
body with *no* outputs is fine: its procedure carries the meaning, and its unused
function copy is simply left alone — see `valuelessEarlyReturn` in the
verification tests.)

An if-then-else followed by more statements is *not* an error: the continuation
is duplicated into both branches. See `deadCodeAfterIfElse` in
`Verification/Fundamentals/TransparentBody.lean`. -/

#eval testLaurelExecution {} <|
#strata
program Laurel;

procedure transparentBodyMultipleOuts() returns (q: int, r: int)
//        ^^^^^^^^^^^^^^^^^^^^^^^^^^^ error: a transparent body with 2 output parameters is not supported; it must have at most one
{
  assert true;
  q := 3;
  r := 2
};
#end

/-! ## A transparent body with no outputs and a discarded tail expression -/

#eval testLaurelVerification <|
#strata
program Laurel;

procedure transparentBodyNoOuts()
{
  assert true;
  3
};

procedure transparentProcedureCaller() opaque {
  transparentBodyNoOuts()
};
#end
