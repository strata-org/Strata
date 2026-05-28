/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import StrataTest.Util.TestLaurel

open StrataTest.Util
open Strata

#eval testLaurelExpect <|
#strata
program Laurel;
procedure opaqueBody(x: int) returns (r: int)
  opaque
  ensures r > 0
{
  if x > 0 then { r := x }
  else { r := 1 }
};

procedure callerOfOpaqueProcedure()
  opaque
{
  var x: int := opaqueBody(3);
  assert x > 0;
  assert x == 3
//^^^^^^^^^^^^^ error: assertion could not be proved
};

procedure invalidPostcondition(x: int)
    opaque
    ensures false
//          ^^^^^ error: assertion does not hold
{
};
#end
