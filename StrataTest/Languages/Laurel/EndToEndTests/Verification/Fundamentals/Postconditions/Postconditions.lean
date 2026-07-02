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

/- A postcondition may call another procedure. `safe` is an opaque procedure
   (`requires x > 0`), and the postcondition `safe(x) == safe(x)` references it.
   The contract pass lowers the postcondition into a `$post` helper whose body
   calls `safe`, guarded by the procedure's own preconditions (assumed at the
   top of the helper body). TransparencyPass builds the pure `$asFunction` twin,
   so the call-site assertion `foo$post0$asFunction(x, r)` reduces to
   `safe$asFunction(x) == safe$asFunction(x)`, which holds by reflexivity. This
   verifies clean. The exact lowering is pinned in
   `Idiomaticity/ContractPassConditionModeTest`. -/
#eval testLaurel <|
#strata
program Laurel;
procedure safe(x: int) returns (s: int)
  requires x > 0
  opaque;
procedure foo(x: int) returns (r: int)
  requires x > 0
  opaque
  ensures safe(x) == safe(x)
{
  r := x
};
#end
