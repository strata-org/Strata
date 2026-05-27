/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import StrataTest.Util.TestLaurel

open StrataTest.Util
open Strata

/-- info: 7:2-41  error: divisor is zero does not hold
14:2-28  error: divisor is non-zero does not hold -/
#guard_msgs in
#eval testLaurelExpect <|
#strata_expect
program Laurel;
procedure divide(x: int, y: int) returns (result: int)
  requires y != 0 summary "divisor is non-zero"
// Call elimination reports precondition errors at the call site.
  opaque
{
  assert y == 0 summary "divisor is zero";
  return x
};

procedure checkPositive(n: int) returns (ok: bool)
  opaque
{
  var x: int := divide(3, 0)
};
#end
