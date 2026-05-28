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
procedure foo()
  opaque
{
    assert true;
    assert false;
//  ^^^^^^^^^^^^ error: assertion does not hold
    assert false
//  ^^^^^^^^^^^^ error: assertion does not hold
};
#end

/-! ## Assume false makes assert false trivially provable -/

/-- info: ok -/
#guard_msgs in
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
