/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import StrataLaurel.Tests.Util.TestLaurel

open StrataTest.Util
open Strata

#eval testLaurelVerification <|
#strata
program Laurel;

procedure assumeLabelledBlock(x: int)
  opaque
{
  assume { var s: bool := false; { if x > 0 then { s := true; exit m }; s := false } m; s };
  assert x > 0;
  assert x < 0
//^^^^^^^^^^^^ error: assertion does not hold
};
#end
