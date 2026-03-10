/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

import StrataTest.DDM.Elab
-- This tests that we can import a module and see dialects declared there.

/--
error: Unknown dialect FailTest.
-/
#guard_msgs in
def testPgmFail :=
#strata
program FailTest;
#end

def testPgm :=
#strata
program Test;
assert;
#end
