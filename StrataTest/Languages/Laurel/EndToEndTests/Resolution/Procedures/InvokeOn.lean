/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import StrataTest.Util.TestLaurel

open StrataTest.Util
open Strata

/-! ## `invokeOn` procedure with an output parameter

An `invokeOn` procedure generates an auto-invocation axiom quantified over its
inputs only, so it may not declare outputs (an output would be unbound in the
axiom). Resolution reports this. -/

#eval testLaurelResolution <|
#strata
program Laurel;
function P(x: int): bool;

procedure foo(x: int) returns (r: int)
//        ^^^ error: 'invokeOn' procedure 'foo' may not have output parameters
  invokeOn P(x)
  opaque
  ensures P(x);
#end

/-! ## `invokeOn` instance procedure with an output parameter

The same rule applies to composite instance procedures. This check runs at
initial resolution, before `LiftInstanceProcedures` moves instance procedures
into the static list, so it must scan instance procedures too — otherwise an
instance `invokeOn` procedure with an output would slip through. -/

#eval testLaurelResolution <|
#strata
program Laurel;
function P(x: int): bool;

composite C {
  var v: int
  procedure m(self: C, x: int) returns (r: int)
//          ^ error: 'invokeOn' procedure 'm' may not have output parameters
    invokeOn P(x)
    opaque
    ensures P(x);
}
#end
