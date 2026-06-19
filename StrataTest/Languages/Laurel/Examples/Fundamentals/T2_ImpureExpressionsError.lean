/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import StrataTest.Util.TestLaurel

open StrataTest.Util
open Strata

/-! ## Procedures used by the negative tests below -/

-- Resolution-only errors are reported via the resolution pass; we use the full
-- pipeline helper because the expected diagnostics are not pure resolution
-- errors.

#eval testLaurel <|
#strata
program Laurel;
procedure hasMutatingAssignment(): int
  opaque
{
  var x: int := 0;
  x := x + 1;
  x
};

function functionWithMutatingAssignment(x: int): int
{
  x := x + 1
//^^^^^^^^^^ error: destructive assignments are not supported in transparent bodies or contracts
};

function functionWithWhile(x: int): int
{
  while(false) {};
//^^^^^^^^^^^^^^^ error: loops are not supported in functions or contracts
  3
};
function functionCallingHasMutationAssignment(x: int): int
{
  hasMutatingAssignment()
//^^^^^^^^^^^^^^^^^^^^^^^ error: calls to procedures are not supported in functions or contracts
};

procedure impureContractIsNotLegal1(x: int)
  requires x == hasMutatingAssignment()
//              ^^^^^^^^^^^^^^^^^^^^^^^ error: calls to procedures are not supported in functions or contracts
  opaque
{
  assert hasMutatingAssignment() == 1
};

procedure impureContractIsNotLegal2(x: int)
  requires (x := 2) == 2
//          ^^^^^^ error: destructive assignments are not supported in transparent bodies or contracts
  opaque
{
  assert (x := 2) == 2
//        ^^^^^^ error: destructive assignments are not supported in transparent bodies or contracts
};
#end
