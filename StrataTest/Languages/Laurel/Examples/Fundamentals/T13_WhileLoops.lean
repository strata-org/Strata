/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import StrataTest.Util.TestLaurel

open StrataTest.Util
open Strata

#eval testLaurel
#strata
program Laurel;
procedure countDown()
  opaque
{
    var i: int := 3;
    while(i > 0)
      invariant i >= 0
    {
        i := i - 1
    };
    assert i == 0
};

procedure countUp()
  opaque
{
    var n: int := 5;
    var i: int := 0;
    while(i < n)
      invariant i >= 0
      invariant i <= n
    {
        i := i + 1
    };
    assert i == n
};
#end
