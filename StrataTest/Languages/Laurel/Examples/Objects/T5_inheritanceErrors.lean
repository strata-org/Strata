/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import StrataTest.Util.TestLaurel

open StrataTest.Util
open Strata

/-- info: 14:4-10  error: fields that are inherited multiple times can not be accessed. -/
#guard_msgs in
#eval testLaurelExpect <|
#strata_expect
program Laurel;
composite Top {
  var xValue: int
}

composite Left extends Top {}
composite Right extends Top {}
composite Bottom extends Left, Right {}

procedure diamondField(b: Bottom)
  opaque
  modifies b
{
  b#xValue := 1
};
#end
