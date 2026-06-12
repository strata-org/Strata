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

procedure deadCodeAfterIfElse(x: int) returns (r: int) {
  if x > 0 then { return 1 } else { return 2 };
//^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ error: in a transparent body, if-then-else is only supported as the last statement in a block
  return 3
};
#end
