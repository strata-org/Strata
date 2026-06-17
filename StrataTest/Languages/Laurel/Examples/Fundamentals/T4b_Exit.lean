/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import StrataTest.Util.TestLaurel

open StrataTest.Util
open Strata

#guard_msgs (drop info) in
#eval testLaurel
#strata
program Laurel;
procedure exitSkipsRest()
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
