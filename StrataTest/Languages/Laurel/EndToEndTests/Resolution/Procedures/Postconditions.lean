/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import StrataTest.Util.TestLaurel

open StrataTest.Util
open Strata

/-! ## Procedures with postconditions -/

#eval testLaurel <|
#strata
program Laurel;

procedure opaqueFunction(x: int) returns (r: int)
  requires x > 0
  opaque
  ensures r > 0
{
  return x
};

procedure callerOfOpaqueFunction()
  opaque
{
  var x: int := opaqueFunction(3);
  assert x > 0;
// The caller only sees the postcondition (r > 0), not the body, so this fails.
  assert x == 3
//^^^^^^^^^^^^^ error: assertion does not hold
};
#end
