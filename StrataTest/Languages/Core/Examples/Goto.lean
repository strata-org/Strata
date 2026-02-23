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

/--
info: [Strata.Core] Type checking succeeded.


VCs:
Label: a1
Property: assert
Obligation:
true

Label: a3
Property: assert
Obligation:
true

Label: a4
Property: assert
Obligation:
true

Label: a6
Property: assert
Assumptions:
<label_ite_cond_true: (~Int.Gt x #0)>: $__x3 > 0
Obligation:
$__x3 * 2 > $__x3

Label: a7
Property: assert
Assumptions:
<label_ite_cond_false: !(~Int.Gt x #0)>: if $__x3 > 0 then false else true
Obligation:
$__x3 <= 0

---
info:
Obligation: a1
Property: assert
Result: ✅ pass

Obligation: a3
Property: assert
Result: ✅ pass

Obligation: a4
Property: assert
Result: ✅ pass

Obligation: a6
Property: assert
Result: ✅ pass

Obligation: a7
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval verify gotoPgm
