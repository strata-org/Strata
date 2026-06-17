/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import StrataTest.Util.TestLaurel

open StrataTest.Util
open Strata

/-! ## Correct heap mutating value return -/

#eval testLaurel
#strata
program Laurel;
composite Container {
  var value: int
}

procedure setAndReturn(c: Container, x: int) returns (r: int)
  opaque
  ensures r == x
  modifies c
{
  c#value := x;
  return x
};
#end

/-! ## Buggy: postcondition r == x + 1 cannot hold when r := x -/

#eval testLaurel <|
#strata
program Laurel;
composite Container {
  var value: int
}

procedure setAndReturnBuggy(c: Container, x: int) returns (r: int)
  opaque
  ensures r == x + 1
//        ^^^^^^^^^^ error: postcondition could not be proved
  modifies c
{
  c#value := x;
  return x
};
#end
