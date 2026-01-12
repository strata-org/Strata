/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Boogie.Verifier

---------------------------------------------------------------------
namespace Strata

def coverPgm :=
#strata
program Boogie;
procedure Test(x : int) returns ()
spec {
  requires x > 1;
}
{
  if (x <= 1) {
    cover [ctest1]: (true);
  } else {
    cover [ctest2]: (x > 2);
    assert [atest2]: (x > 1);
  }
};
#end

/--
info: [Strata.Boogie] Type checking succeeded.


VCs:
Label: ctest1
Property: cover
Assumptions:
(<label_ite_cond_true: ((~Int.Le x) #1)>, ((~Int.Le $__x0) #1))
(Test_requires_0, ((~Int.Gt $__x0) #1))

Proof Obligation:
#true

Label: ctest2
Property: cover
Assumptions:
(<label_ite_cond_false: !((~Int.Le x) #1)>, (if ((~Int.Le $__x0) #1) then #false else #true))
(Test_requires_0, ((~Int.Gt $__x0) #1))

Proof Obligation:
((~Int.Gt $__x0) #2)

Label: atest2
Property: assert
Assumptions:
(<label_ite_cond_false: !((~Int.Le x) #1)>, (if ((~Int.Le $__x0) #1) then #false else #true))
(Test_requires_0, ((~Int.Gt $__x0) #1))

Proof Obligation:
((~Int.Gt $__x0) #1)

Wrote problem to vcs/ctest1.smt2.


Result: Obligation: ctest1
Property: cover
Result: ❌ fail


Evaluated program:
(procedure Test :  ((x : int)) → ())
modifies: []
preconditions: (Test_requires_0, (((~Int.Gt : (arrow int (arrow int bool))) (x : int)) #1))
postconditions: ⏎
body: assume [Test_requires_0] ((~Int.Gt $__x0) #1)
#[<[fileRange]: :⟨0, 0⟩-⟨0, 0⟩>] if (((~Int.Le : (arrow int (arrow int bool))) ($__x0 : int)) #1) then {$$_then : {cover [ctest1] #true}}
else{$$_else : {cover [ctest2] ((~Int.Gt $__x0) #2)
  assert [atest2] ((~Int.Gt $__x0) #1)}}

Wrote problem to vcs/ctest2.smt2.
Wrote problem to vcs/atest2.smt2.
---
info:
Obligation: ctest1
Property: cover
Result: ❌ fail

Obligation: ctest2
Property: cover
Result: ✅ pass
Model:
($__x0, 3)

Obligation: atest2
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval verify "z3" coverPgm (options := Options.default)

---------------------------------------------------------------------
