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
$heapfield var f: int
composite C { var f: int }
procedure main() opaque modifies * { var c: C := new C; c#f := 3; assert c#f == 3 };
#end
