/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import StrataTest.Util.TestLaurel

open StrataTest.Util
open Strata

#eval testLaurelMultiple <|
#strata
program Laurel;
procedure foo(x: int)
  opaque
{
  {
    if x == 0 then {
      exit myBlock
    }
  } myBlock;
  assert false
//^^^^^^^^^^^^ error: assertion does not hold
};

// A parameterless `entry` so the concrete interpreter can drive this too: `foo`
// reaches `assert false` on every path (the `exit` only skips the empty
// remainder of the guarded block), so calling it with any concrete argument
// hits the same failing assertion the verifier reports.
procedure runFoo()
  entry
  opaque
{
  foo(1)
};
#end
