/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import StrataTest.Util.TestLaurel

open StrataTest.Util
open Strata

/-- info: 5:2-5  error: could not infer type -/
#guard_msgs in
#eval testLaurelExpect <|
#strata_expect
program Laurel;
procedure foo()
  opaque
{
  <?>
};
#end
