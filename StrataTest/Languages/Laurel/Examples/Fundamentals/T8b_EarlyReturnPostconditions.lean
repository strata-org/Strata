/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import StrataTest.Util.TestLaurel

open StrataTest.Util
open Strata

/-! ## Correct early return -/

/-- info: ok -/
#guard_msgs in
#eval testLaurel
#strata
program Laurel;
procedure earlyReturnCorrect(x: int) returns (r: int)
  opaque
  ensures r >= 0
{
  if x < 0 then {
    return -x
  };
  return x
};
#end

/-! ## Buggy early return: postcondition fails -/

/-- info: 4:10-16  error: assertion does not hold -/
#guard_msgs in
#eval testLaurelExpect <|
#strata_expect
program Laurel;
procedure earlyReturnBuggy(x: int) returns (r: int)
  opaque
  ensures r >= 0
{
  if x < 0 then {
    return x
  };
  return x
};
#end
