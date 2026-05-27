/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import StrataTest.Util.TestLaurel

open StrataTest.Util
open Strata

/-! ## Failing asserts -/

/-- info: 6:4-16  error: assertion does not hold
7:4-16  error: assertion does not hold -/
#guard_msgs in
#eval testLaurelExpect <|
#strata_expect
program Laurel;
procedure foo()
  opaque
{
    assert true;
    assert false;
    assert false
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
