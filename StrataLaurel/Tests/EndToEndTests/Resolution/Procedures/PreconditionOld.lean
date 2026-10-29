/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
meta import StrataLaurel.Tests.Util.TestLaurel

open StrataTest.Util
open Strata

/-! ## `old(...)` in a precondition

A precondition is evaluated on entry, where the current state already is the
pre-state, so `Resolution.validatePreconditionOld` rejects an `old(...)` there.
An `old(...)` in a postcondition, a `throwsOn` guard or a `throwsOn` case's
`ensures` stays legal. -/

#eval testLaurelResolution <|
#strata
program Laurel;
composite Err {}
procedure inRequires(x: int) returns (x: int)
  requires old(x) > 0
//         ^^^^^^ error: `old(...)` is not allowed in a precondition: it is already evaluated in the pre-state
  opaque
{ x := x + 1 };
procedure inPostconditions(x: int) returns (x: int)
  throws (e: Err)
  opaque
  ensures x == old(x) + 1
  throwsOn old(x) < 0 { ensures x == old(x) }
{
  if x < 0 then {
    var err: Err := new Err;
    throw err
  };
  x := x + 1
};
#end
