/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import StrataTest.Util.TestLaurel

open StrataTest.Util
open Strata

/-! ## Failing asserts -/

#eval testLaurel <|
#strata
program Laurel;
procedure foo(x: int)
  opaque
{
    assert x == x;
    assert x == 2;
//  ^^^^^^^^^^^^^ error: assertion does not hold
    assert x == 2
//  ^^^^^^^^^^^^^ error: assertion does not hold
};
#end

/-! ## Assume false makes assert false trivially provable -/

#eval testLaurel
#strata
program Laurel;
procedure bar()
  opaque
{
    assume false;
    assert false
};
#end
