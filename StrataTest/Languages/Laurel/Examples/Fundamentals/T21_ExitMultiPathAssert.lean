/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import StrataTest.Util.TestLaurel

open StrataTest.Util
open Strata

/-- info: 10:2-14  error: assertion does not hold -/
#guard_msgs in
#eval testLaurelExpect <|
#strata_expect
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
};
#end
