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
procedure noOutput() opaque { };
composite Cell {}

procedure callerWithNonCompositeReceiver()
  opaque
{
  var z: int := 5;
  z#sideEffect(-1);
//^^^^^^^^^^^^^^^^ error: 'sideEffect' is called with '#' on a non-composite receiver; instance-method calls require a composite receiver
  assert 1 == 1
};

procedure callerWithNoOutputReceiver()
  opaque
{
  noOutput()#sideEffect(-1)
//^^^^^^^^^^^^^^^^^^^^^^^^^ error: 'sideEffect' is called with '#' on a non-composite receiver
};

procedure callerWithFailingReceiver()
  opaque
{
  noOutput(1)#missing()
//^^^^^^^^^^^ error: call to 'noOutput' expects 0 argument(s) but 1 were provided
};

procedure callerWithTypeNameReceiver()
  opaque
{
  // A composite's name is `Unknown` by itself, so the errors above do not explain the call.
  Cell#sideEffect(-1)
//^^^^^^^^^^^^^^^^^^^ error: 'sideEffect' is called with '#' on the composite type 'Cell'
};

procedure callerWithHoleReceiver()
  opaque
{
  <?>#sideEffect(-1)
//^^^^^^^^^^^^^^^^^^ error: 'sideEffect' is called with '#' on a receiver of unknown type
};
#end

/-! Alone in its block, so that the declaration's is the only error before the call. -/

#eval testLaurelResolution <|
#strata
program Laurel;
procedure sideEffect(x: int) opaque { };

procedure callerWithUntypedReceiver()
  opaque
{
  var x;
//^^^^^ error: cannot infer a type for 'x'
  // The declaration's error leaves `x` `Unknown`, so the call adds no second one.
  x#sideEffect(-1)
};
#end

/-! A static procedure declared under a method's key is not a method, so the call binds nothing. -/

#eval testLaurelResolution <|
#strata
program Laurel;
composite Cell { }
procedure Cell$m(a: int, b: bool) opaque { };

procedure callerOfStaticAtMethodKey(c: Cell)
  opaque
{
  c#m(1, true)
//^^^^^^^^^^^^ error: 'Cell$m' resolves to static procedure, but expected instance procedure
};
#end
