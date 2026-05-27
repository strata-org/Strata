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

/-- info: 12:2-12  error: destructive assignments are not supported in functions or contracts
17:2-17  error: loops are not supported in functions or contracts
21:2-10  error: calls to procedures are not supported in functions or contracts
25:16-24  error: calls to procedures are not supported in functions or contracts
32:12-18  error: destructive assignments are not supported in functions or contracts
35:10-16  error: destructive assignments are not supported in functions or contracts -/
#guard_msgs in
#eval testLaurelExpect <|
#strata_expect
program Laurel;
procedure impure(): int
  opaque
{
  var x: int := 0;
  x := x + 1;
  x
};

function impureFunction1(x: int): int
{
  x := x + 1
};

function impureFunction2(x: int): int
{
  while(false) {}
};
function impureFunction3(x: int): int
{
  impure()
};

procedure impureContractIsNotLegal1(x: int)
  requires x == impure()
  opaque
{
  assert impure() == 1
};

procedure impureContractIsNotLegal2(x: int)
  requires (x := 2) == 2
  opaque
{
  assert (x := 2) == 2
};
#end
