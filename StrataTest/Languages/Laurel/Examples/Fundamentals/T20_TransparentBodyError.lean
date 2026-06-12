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
procedure transparentBodyMultipleOuts() returns (q: int, r: int)
{
  assert true;
  q := 3;
//^^^^^^ error: destructive assignments are not supported in transparent bodies or contracts
  r := 2
};

procedure transparentBodyNoOuts()
{
  assert true
};

procedure transparentProcedureCaller() opaque {
  assign var x: int, var y: int := transparentBodyMultipleOuts();
  assert x == 3;
  assert y == 2;

  transparentBodyNoOuts()
};
#end
