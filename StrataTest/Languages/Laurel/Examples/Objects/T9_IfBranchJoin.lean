/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import StrataTest.Util.TestLaurel

open StrataTest.Util
open Strata

/-
An `if/else` in check position pushes the expected type into *both* branches
(rather than synth + subsume at the boundary), so a branch whose value doesn't
match the expected type errors at that branch.
-/

#eval testLaurelResolution <|
#strata
program Laurel;
composite Top { }
composite Left extends Top { }
composite Right extends Top { }
procedure test(c: bool) opaque {
  var x: Top := if c then new Left else new Right;
  var y: Left := if c then new Left else new Right
//                                       ^^^^^^^^^ error: expected 'Left', got 'Right'
};
#end
