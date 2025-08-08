/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Boogie.Verifier

---------------------------------------------------------------------
namespace Strata

def testEnv : Program :=
#strata
program Boogie;

procedure min(n : int, m : int) returns (k : int)
spec {
  ensures ((k <= n) && (k <= m));
}
{
  k := if (n < m) then n else m;
  k := k;
};
#end


/--
info: [Strata.Boogie] Type checking succeeded.


VCs:
Label: min_ensures_0
Assumptions:
Proof Obligation:
((~Bool.And ((~Int.Le (if ((~Int.Lt $__n0) $__m1) then $__n0 else $__m1)) $__n0)) ((~Int.Le (if ((~Int.Lt $__n0) $__m1) then $__n0 else $__m1)) $__m1))

Wrote problem to vcs/min_ensures_0.smt2.
---
info:
Obligation: min_ensures_0
Result: verified
-/
#guard_msgs in
#eval verify "cvc5" testEnv

---------------------------------------------------------------------
