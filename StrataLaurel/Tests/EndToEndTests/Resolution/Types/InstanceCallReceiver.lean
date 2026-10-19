/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import StrataLaurel.Tests.Util.TestLaurel

open StrataTest.Util
open Strata

/-! # A `#` call needs a composite receiver

`z#sideEffect(-1)` on an `int` receiver has no method to bind to, and the tempting fallback —
binding it to the same-named top-level `sideEffect` — is UNSOUND rather than merely loose.
`LiftInstanceProcedures` and `ContractPass` inject the callee's precondition only for a
genuine instance call, so a `#` call silently rerouted to a static procedure would drop that
procedure's `requires` entirely. The program below would then verify while calling
`sideEffect(-1)` against `requires x > 0`.

So it is rejected at resolution. The positive side — real instance calls on composite
receivers, including through a field-selected receiver and on generic composites — is in
`Execution/Types/Composites/InstanceProcedures.lean`.
-/

#eval testLaurelResolution <|
#strata
program Laurel;
procedure sideEffect(x: int) requires x > 0 opaque ensures 1 == 1 { };

procedure callerWithNonCompositeReceiver()
  opaque
{
  var z: int := 5;
  z#sideEffect(-1);
//^^^^^^^^^^^^^^^^ error: 'sideEffect' is called with '#' on a non-composite receiver; instance-method calls require a composite receiver
  assert 1 == 1
};
#end
