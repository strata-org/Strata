/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import StrataTest.Util.TestLaurel

open StrataTest.Util
open Strata

#eval testLaurelMultiple
#strata
program Laurel;
procedure exitSkipsRest()
  entry
  opaque
{
    var x: int := 0;
    {
        x := 1;
        exit done
    } done;
    assert x == 1
};

procedure exitFromNestedBlock()
  entry
  opaque
{
    var x: int := 0;
    {
        {
            x := 42;
            exit outer
        } inner;
        x := 99
    } outer;
    assert x == 42
};
#end
