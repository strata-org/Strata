/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

meta import all StrataTest.Util.TestDiagnostics
meta import all StrataTest.Languages.Laurel.TestExamples

meta section

open StrataTest.Util
open Strata

namespace Strata.Laurel

def program := r"
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
"

#guard_msgs (drop info, error) in
#eval testInputWithOffset "Postconditions" program 14 processLaurelFile
