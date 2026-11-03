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

procedure checkedSub(x: int, y: int): int
  requires x - y <= 1000
{
  return x - y
};

procedure clausesDeclareTheSameLocal(b: int) returns (r: int)
  opaque
  ensures { var t: int := checkedSub(1, 1); r == b + t }
  ensures { var t: int := checkedSub(2, 1); r < b + t }
{
  r := b
};
#end

#eval testLaurelVerification <|
#strata
program Laurel;

procedure p(t: int)
  requires t > 0 && { var t: int := 1; t == 1 }
  requires 10 / t > 0
  opaque
{
};
#end
