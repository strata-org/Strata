/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
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


VCs:
Label: a1
Assumptions:
Proof Obligation:
#true

Label: a3
Assumptions:
Proof Obligation:
#true

Label: a4
Assumptions:
Proof Obligation:
#true

Label: a6
Assumptions:
(<label_ite_cond_true: ((~Int.Gt x) #0)>, ((~Int.Gt $__x2) #0))
Proof Obligation:
((~Int.Gt ((~Int.Mul $__x2) #2)) $__x2)

Label: a1
Assumptions:
Proof Obligation:
#true

Label: a3
Assumptions:
Proof Obligation:
#true

Label: a4
Assumptions:
Proof Obligation:
#true

Label: a7
Assumptions:
(<label_ite_cond_false: !((~Int.Gt x) #0)>, (if ((~Int.Gt $__x2) #0) then #false else #true))
Proof Obligation:
((~Int.Le $__x2) #0)

Wrote problem to vcs/a1.smt2.
Wrote problem to vcs/a3.smt2.
Wrote problem to vcs/a4.smt2.
Wrote problem to vcs/a6.smt2.
Wrote problem to vcs/a1.smt2.
Wrote problem to vcs/a3.smt2.
Wrote problem to vcs/a4.smt2.
Wrote problem to vcs/a7.smt2.
---
info:
Obligation: a1
Result: verified

Obligation: a3
Result: verified

Obligation: a4
Result: verified

Obligation: a6
Result: verified

Obligation: a1
Result: verified

Obligation: a3
Result: verified

Obligation: a4
Result: verified

Obligation: a7
Result: verified
-/
#guard_msgs in
#eval verify "cvc5" gotoEnv
