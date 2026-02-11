/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Core.Core
import Strata.Languages.Core.Verifier

---------------------------------------------------------------------
namespace Strata

def gotoPgm : Program :=
#strata
program Core;
var g : bool;
procedure Test1(x : bool) returns (y : bool)
{
    l1: {
      assert [a1]: x == x;
      goto l3;
    }
    l2: {
      assert [a2]: !(x == x); // skipped over
    }
    l3: {
      assert [a3]: x == x;
    }
};

procedure Test2(x : int) returns (y : bool)
{
    l1: {
      assert [a4]: x == x;
      if (x > 0) {
        goto l3;
      } else {
        goto l4;
      }
    }
    l2: {
      assert [a5]: !(x == x); // skipped over
    }
    l3: {
      assert [a6]: x * 2 > x;
      goto l5;
    }
    l4: {
      assert [a7]: x <= 0;
      goto l5;
    }
    l5 : {}
};
#end

-- def p := (translateProgram gotoEnv.commands).run
-- def err := Core.typeCheckAndPartialEval p.fst

/-

info: [Strata.Core] Type checking succeeded.
-/
#guard_msgs in
#eval verify "cvc5" gotoPgm
