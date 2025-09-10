/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/


import Strata.Languages.Boogie.Verifier

---------------------------------------------------------------------
namespace Strata

def axiomPgm :=
#strata
program Boogie;

const x : int;
axiom [a1]: x == 5;

const y : int;
axiom [a2]: y == 2;

function f(x: int): int;
axiom [f1]: (forall y : int :: f(y) > y);

procedure P() returns (ret : int)
  spec {
    ensures [use_f1]: ret > 7;
  }
{
  assert [use_a1_a2]: x > y;
  ret := f(x + y);
};

procedure P2() returns ()
{
  assert [use_a1_again]: y == 2;
  assert [use_a2_again]: f(y) > y;
};

#end

/--
info: [Strata.Boogie] Type checking succeeded.


VCs:
Label: use_a1_a2
Assumptions:

(a1, (~x == #5))
(a2, (~y == #2)) (f1, (∀ ((~Int.Gt (~f %0)) %0)))
Proof Obligation:
((~Int.Gt ~x) ~y)

Label: use_f1
Assumptions:

(a1, (~x == #5))
(a2, (~y == #2)) (f1, (∀ ((~Int.Gt (~f %0)) %0)))
Proof Obligation:
((~Int.Gt (~f ((~Int.Add ~x) ~y))) #7)

Label: use_a1_again
Assumptions:

(a1, (~x == #5))
(a2, (~y == #2)) (f1, (∀ ((~Int.Gt (~f %0)) %0)))
Proof Obligation:
(~y == #2)

Label: use_a2_again
Assumptions:

(a1, (~x == #5))
(a2, (~y == #2)) (f1, (∀ ((~Int.Gt (~f %0)) %0)))
Proof Obligation:
((~Int.Gt (~f ~y)) ~y)

Wrote problem to vcs/use_a1_a2.smt2.
Wrote problem to vcs/use_f1.smt2.
Wrote problem to vcs/use_a1_again.smt2.
Wrote problem to vcs/use_a2_again.smt2.
---
info:
Obligation: use_a1_a2
Result: verified

Obligation: use_f1
Result: verified

Obligation: use_a1_again
Result: verified

Obligation: use_a2_again
Result: verified
-/
#guard_msgs in
#eval verify "cvc5" axiomPgm
