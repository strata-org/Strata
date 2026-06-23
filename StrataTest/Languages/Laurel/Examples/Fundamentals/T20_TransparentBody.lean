/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import StrataTest.Util.TestLaurel

open StrataTest.Util
open Strata

#eval testLaurel <|
#strata
program Laurel;
procedure transparentBody(): int
{
  assert true;
  return 3
};

procedure tranparentCaller(): int {
  return transparentBody()
};

procedure transparentCallerCaller() opaque {
  var x: int := tranparentCaller();
  assert x == 3
};
#end
