/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Core.Core
import Strata.Languages.Core.Verifier

---------------------------------------------------------------------
namespace Strata

/--
Regression test for https://github.com/strata-org/Strata/issues/419
When a procedure contains a goto inside an if branch, the VCG should not
produce duplicate verification obligations for subsequent procedures.

Expected: assert_0 in `second` fails exactly once.
-/
def gotoItePgm : Program :=
#strata
program Core;

procedure first(a : int) returns (r : int)
spec { }
{
  if (a > 0) {
    r := 1;
    goto done;
  }
  r := 0;
  done: { }
};

procedure second(a : int) returns (r : int)
spec { }
{
  assert [assert_0]: a > 0;
  r := a;
};
#end

/--
info: [Strata.Core] Type checking succeeded.


VCs:
Label: assert_0
Property: assert
Assumptions:


Proof Obligation:
(~Int.Gt $__a2 #0)



Result: Obligation: assert_0
Property: assert
Result: ❌ fail
Model:
($__a2, 0)


Evaluated program:
procedure first :  ((a : int)) → ((r : int))
  modifies: []
  preconditions: 
  postconditions: 
{
  {
    #[<[fileRange]: :623-669>] if #true {
      $_then :
      {
        r := #1
        #[<[fileRange]: :652-662>] goto done
      }
    }
    else {}
    #[<[fileRange]: :679-688>] done : {}
  }
}
procedure second :  ((a : int)) → ((r : int))
  modifies: []
  preconditions: 
  postconditions: 
{
  {
    assert [assert_0] (~Int.Gt $__a2 #0)
    r := $__a2
  }
}
---
info:
Obligation: assert_0
Property: assert
Result: ❌ fail
Model:
($__a2, 0)
-/
#guard_msgs in
#eval verify "cvc5" gotoItePgm

end Strata
