/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/


import Strata.Languages.Boogie.Verifier

---------------------------------------------------------------------
namespace Strata

def axiomEnv : Environment :=
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

#end

/--
info: [Strata.Boogie] Type checking succeeded.


VCs:
Label: use_a1_a2
Assumptions:
(f1, (∀ ((~Int.Gt (~f %0)) %0)))
(a2, (~y == #2))
(a1, (~x == #5))
Proof Obligation:
((~Int.Gt ~x) ~y)

Label: use_f1
Assumptions:
(f1, (∀ ((~Int.Gt (~f %0)) %0)))
(a2, (~y == #2))
(a1, (~x == #5))
Proof Obligation:
((~Int.Gt (~f ((~Int.Add ~x) ~y))) #7)

Wrote problem to vcs/use_a1_a2.smt2.
Wrote problem to vcs/use_f1.smt2.
---
info:
Obligation: use_a1_a2
Result: verified

Obligation: use_f1
Result: verified
-/
#guard_msgs in
#eval verify "cvc5" axiomEnv
