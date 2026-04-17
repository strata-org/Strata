/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import StrataTest.Util.TestDiagnostics
import StrataTest.Languages.Laurel.TestExamples

open StrataTest.Util

namespace Strata.Laurel

def exitProgram := r"
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
"

#guard_msgs(drop info, error) in
#eval testInputWithOffset "Exit" exitProgram 14 processLaurelFile

end Strata.Laurel
