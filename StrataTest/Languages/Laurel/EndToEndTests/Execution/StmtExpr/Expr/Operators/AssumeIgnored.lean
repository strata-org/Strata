/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
import StrataTest.Util.TestLaurel

open StrataTest.Util
open Strata

/-! ## `ignoreAssumes` path exercised under concrete execution

`assume false` is a no-op during interpretation (`ignoreAssumes := true`), so
execution proceeds past it and the subsequent `assert true` succeeds. If
`ignoreAssumes` regressed, the interpret path would throw
`assume (…) condition is false` as a non-assertion error and the build would
fail. -/

#guard_msgs (drop info) in
#eval testLaurelMultiple <|
#strata
program Laurel;
procedure ignoresAssume() entry opaque {
  assume false;
  assert true
};
#end
