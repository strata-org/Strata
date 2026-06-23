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
  returns (r: int) // TODO, removing this returns triggers a latent bug
  opaque
  ensures false
//        ^^^^^ error: postcondition does not hold
{
};

procedure bar(x: int) returns (r: int)
  requires x > 0
  opaque
  ensures r > 0
{
  r := x + 1
};

procedure caller() returns (out: int)
  opaque
{
  out := bar(bar(5))
};
#end
