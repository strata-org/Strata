/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import StrataLaurel.Tests.Util.TestLaurel

open StrataTest.Util
open Strata

/-! A call in a contract clause that follows another runs when the contract is interpreted.
The verifier cannot tell what `five`, opaque and without a contract, returns, so it rejects
`usesFive`'s postcondition, and only the interpreters run this block. -/
#eval testLaurelExecution { skipVerification := true } <|
#strata
program Laurel;

procedure five(x: int) returns (s: int)
  opaque
{
  s := 5
};

procedure usesFive(k: int) returns (r: int)
  opaque
  ensures r == k
  ensures five(r) == 5
{
  r := k
};

procedure main() returns (z: int)
  entry
{
  z := usesFive(1)
};
#end
