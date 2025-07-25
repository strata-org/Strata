/-
  Copyright Strata Contributors

  Licensed under the Apache License, Version 2.0 (the "License");
  you may not use this file except in compliance with the License.
  You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

  Unless required by applicable law or agreed to in writing, software
  distributed under the License is distributed on an "AS IS" BASIS,
  WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
  See the License for the specific language governing permissions and
  limitations under the License.
-/

import Strata.Languages.Boogie.Boogie
import Strata.Languages.Boogie.Verifier

---------------------------------------------------------------------
namespace Strata

def gotoEnv : Environment :=
#strata
program Boogie;
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
-- def err := Boogie.typeCheckAndPartialEval p.fst

/--
info: [Strata.Boogie] Type checking succeeded.


Obligation a1 proved via evaluation!


Obligation a3 proved via evaluation!


Obligation a4 proved via evaluation!


VCs:
Label: a6
Assumptions:
(<label_ite_cond_true: ((~Int.Gt x) #0)>, ((~Int.Gt $__x2) #0))
Proof Obligation:
((~Int.Gt ((~Int.Mul $__x2) #2)) $__x2)

Label: a7
Assumptions:
(<label_ite_cond_false: !((~Int.Gt x) #0)>, (if ((~Int.Gt $__x2) #0) then #false else #true))
Proof Obligation:
((~Int.Le $__x2) #0)

Wrote problem to vcs/a6.smt2.
Wrote problem to vcs/a7.smt2.
---
info:
Obligation: a6
Result: verified

Obligation: a7
Result: verified
-/
#guard_msgs in
#eval verify "cvc5" gotoEnv
