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

procedure transparentWithMutatingAssignment(x: int): int
{
  x := x + 1;
//^^^^^^^^^^ error: destructive assignments are not supported in transparent bodies or contracts
  return 3
};

procedure callsHasMutatingAssignment(x: int): int
 opaque
{
  hasMutatingAssignment()
};

procedure impureContractIsLegal1(x: int)
  requires x == hasMutatingAssignment()
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
};
#end
