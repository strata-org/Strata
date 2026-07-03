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
constrained nat = x: int where x >= 0 witness 0

// Procedure with valid constrained return — 3 satisfies nat's constraint (x >= 0).
procedure goodFunc(): nat { return 3 };

// Procedure with invalid constrained return — -1 violates nat's constraint (x >= 0).
procedure badFunc(): nat { return -1 };
//                   ^^^ error: postcondition does not hold

// Caller of constrained function — body is inlined, caller sees actual value
procedure callerGood()
  opaque
{
  var x: int := goodFunc();
  assert x >= 0
};
#end
