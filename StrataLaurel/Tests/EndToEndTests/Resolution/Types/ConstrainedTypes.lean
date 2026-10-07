/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
meta import StrataLaurel.Tests.Util.TestLaurel

open StrataTest.Util
open Strata

#eval testLaurelExecution { skipCoreInterpreter := true } <|
#strata
program Laurel;
constrained nat = x: int where x >= 0 witness 0

// Procedure with valid constrained return — 3 satisfies nat's constraint (x >= 0).
procedure goodFunc(): nat { return 3 };

// A transparent procedure keeps its body and its constrained return type is still
// checked — by the generated `$constraintLemma_badFunc` rather than by an `ensures`,
// so the failure is an assertion, reported on the return type.
procedure badFunc(): nat { return -1 };
//                   ^^^ error: assertion does not hold

// Caller of constrained function — body is inlined, caller sees actual value
procedure callerGood()
  opaque
{
  var x: int := goodFunc();
  assert x >= 0
};
#end
