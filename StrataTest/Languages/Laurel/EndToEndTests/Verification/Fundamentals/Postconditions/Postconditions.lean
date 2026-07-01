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

/- A postcondition's well-formedness can depend on the procedure's
   preconditions. `safe` is partial (`requires x > 0`), so the postcondition
   `safe(x) == safe(x)` is well-formed only when `x > 0` — which the procedure's
   `requires x > 0` guarantees. This verifies clean only because the contract
   pass attaches the procedure's preconditions to the postcondition helper as
   assumed preconditions; dropping `requires x > 0` makes the well-formedness
   obligation for `safe(x)` fail. The exact lowering is pinned in
   `Idiomaticity/ContractPassConditionModeTest`. -/
#eval testLaurel <|
#strata
program Laurel;
function safe(x: int): int requires x > 0;
procedure foo(x: int) returns (r: int)
  requires x > 0
  opaque
  ensures safe(x) == safe(x)
{
  r := x
};
#end
