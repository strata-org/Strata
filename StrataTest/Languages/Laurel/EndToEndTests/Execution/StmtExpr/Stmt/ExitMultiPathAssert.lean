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
#end
