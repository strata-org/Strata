/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import StrataLaurel.Tests.Util.TestLaurel

open StrataTest.Util
open Strata

/-! # A `#` call needs a composite receiver

`z#sideEffect(-1)` on an `int` receiver has no method to bind to. The tempting fallback,
binding it to the same-named top-level `sideEffect`, leaves an instance call that
`LiftInstanceProcedures` does not lift, and Core translation reports it as a strata-bug.

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
