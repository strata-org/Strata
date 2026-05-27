/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import StrataTest.Util.TestLaurel

open StrataTest.Util
open Strata

/-- info: 2:10-25  error: transparent procedures are not yet supported. Add 'opaque' to make the procedure opaque -/
#guard_msgs in
#eval testLaurelExpect <|
#strata_expect
program Laurel;
procedure transparentBody()
{
  assert true
};
#end
