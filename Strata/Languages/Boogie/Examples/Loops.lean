/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Boogie.Verifier

---------------------------------------------------------------------
namespace Strata

def gaussEnv : Environment :=
#strata
program Boogie;

procedure sum(n : int) returns (s : int)
spec {
  requires (n >= 0);
  ensures (s == ((n * (n + 1)) div 2));
}
{
  var i : int;
  i := 0;
  s := 0;
  while (i < n)
    invariant 0 <= i &&
              i <= n &&
              s == (i * (i + 1)) div 2;
  {
    i := (i + 1);
    s := (s + i);
  }
};
#end

/--
info: [Strata.Boogie] Type checking succeeded.


VCs:
Label: entry_invariant_0
Assumptions:
(<label_ite_cond_true: ((~Int.Lt i) n)>, ((~Int.Lt #0) $__n0))
(sum_requires_0, ((~Int.Ge $__n0) #0))
Proof Obligation:
((~Bool.And ((~Bool.And #true) ((~Int.Le #0) $__n0))) #true)

Label: arbitrary_iter_maintain_invariant_0
Assumptions:
(<label_ite_cond_true: ((~Int.Lt i) n)>, ((~Int.Lt #0) $__n0))
(assume_guard_0, ((~Int.Lt $__i2) $__n0)) (assume_invariant_0, ((~Bool.And ((~Bool.And ((~Int.Le #0) $__i2)) ((~Int.Le $__i2) $__n0))) ($__s3 == ((~Int.Div ((~Int.Mul $__i2) ((~Int.Add $__i2) #1))) #2))))
(sum_requires_0, ((~Int.Ge $__n0) #0))
Proof Obligation:
((~Bool.And ((~Bool.And ((~Int.Le #0) ((~Int.Add $__i2) #1))) ((~Int.Le ((~Int.Add $__i2) #1)) $__n0))) (((~Int.Add $__s3) ((~Int.Add $__i2) #1)) == ((~Int.Div ((~Int.Mul ((~Int.Add $__i2) #1)) ((~Int.Add ((~Int.Add $__i2) #1)) #1))) #2)))

Label: sum_ensures_1
Assumptions:
(sum_requires_0, ((~Int.Ge $__n0) #0))
(<label_ite_cond_true: ((~Int.Lt i) n)>, (if ((~Int.Lt #0) $__n0) then ((~Int.Lt #0) $__n0) else #true)) (assume_guard_0, (if ((~Int.Lt #0) $__n0) then ((~Int.Lt $__i2) $__n0) else #true)) (assume_invariant_0, (if ((~Int.Lt #0) $__n0) then ((~Bool.And ((~Bool.And ((~Int.Le #0) $__i2)) ((~Int.Le $__i2) $__n0))) ($__s3 == ((~Int.Div ((~Int.Mul $__i2) ((~Int.Add $__i2) #1))) #2))) else #true)) (not_guard_0, (if ((~Int.Lt #0) $__n0) then (~Bool.Not ((~Int.Lt $__i4) $__n0)) else #true)) (invariant_0, (if ((~Int.Lt #0) $__n0) then ((~Bool.And ((~Bool.And ((~Int.Le #0) $__i4)) ((~Int.Le $__i4) $__n0))) ($__s5 == ((~Int.Div ((~Int.Mul $__i4) ((~Int.Add $__i4) #1))) #2))) else #true)) (<label_ite_cond_false: !((~Int.Lt i) n)>, (if (if ((~Int.Lt #0) $__n0) then #false else #true) then (if ((~Int.Lt #0) $__n0) then #false else #true) else #true))
Proof Obligation:
((if ((~Int.Lt #0) $__n0) then $__s5 else #0) == ((~Int.Div ((~Int.Mul $__n0) ((~Int.Add $__n0) #1))) #2))

Wrote problem to vcs/entry_invariant_0.smt2.
Wrote problem to vcs/arbitrary_iter_maintain_invariant_0.smt2.
Wrote problem to vcs/sum_ensures_1.smt2.
---
info:
Obligation: entry_invariant_0
Result: verified

Obligation: arbitrary_iter_maintain_invariant_0
Result: verified

Obligation: sum_ensures_1
Result: verified
-/
#guard_msgs in
#eval verify "cvc5" gaussEnv

def nestedEnv : Environment :=
#strata
program Boogie;

procedure nested(n : int) returns (s : int)
spec {
  requires [n_pos]: n > 0;
} {
  var x: int;
  var y: int;
  x := 0;
  while (x < n)
    invariant x >= 0 && x <= n;
  {
    y := 0;
    while (y < x)
      invariant y >= 0 && y <= x;
    {
      y := y + 1;
    }
    x := x + 1;
  }
};
#end

/--
info: [Strata.Boogie] Type checking succeeded.


VCs:
Label: entry_invariant_0
Assumptions:
(<label_ite_cond_true: ((~Int.Lt x) n)>, ((~Int.Lt #0) $__n0))
(n_pos, ((~Int.Gt $__n0) #0))
Proof Obligation:
((~Bool.And #true) ((~Int.Le #0) $__n0))

Label: entry_invariant_2
Assumptions:
(<label_ite_cond_true: ((~Int.Lt y) x)>, ((~Int.Lt #0) $__x4))
(<label_ite_cond_true: ((~Int.Lt x) n)>, ((~Int.Lt #0) $__n0))
(assume_guard_0, ((~Int.Lt $__x4) $__n0)) (assume_invariant_0, ((~Bool.And ((~Int.Ge $__x4) #0)) ((~Int.Le $__x4) $__n0)))
(n_pos, ((~Int.Gt $__n0) #0))
Proof Obligation:
((~Bool.And #true) ((~Int.Le #0) $__x4))

Label: arbitrary_iter_maintain_invariant_2
Assumptions:
(<label_ite_cond_true: ((~Int.Lt y) x)>, ((~Int.Lt #0) $__x4))
(assume_guard_2, ((~Int.Lt $__y5) $__x4)) (assume_invariant_2, ((~Bool.And ((~Int.Ge $__y5) #0)) ((~Int.Le $__y5) $__x4)))
(<label_ite_cond_true: ((~Int.Lt x) n)>, ((~Int.Lt #0) $__n0))
(assume_guard_0, ((~Int.Lt $__x4) $__n0)) (assume_invariant_0, ((~Bool.And ((~Int.Ge $__x4) #0)) ((~Int.Le $__x4) $__n0)))
(n_pos, ((~Int.Gt $__n0) #0))
Proof Obligation:
((~Bool.And ((~Int.Ge ((~Int.Add $__y5) #1)) #0)) ((~Int.Le ((~Int.Add $__y5) #1)) $__x4))

Label: entry_invariant_0
Assumptions:
(<label_ite_cond_true: ((~Int.Lt x) n)>, ((~Int.Lt #0) $__n0))
(n_pos, ((~Int.Gt $__n0) #0))
Proof Obligation:
((~Bool.And #true) ((~Int.Le #0) $__n0))

Label: arbitrary_iter_maintain_invariant_0
Assumptions:
(<label_ite_cond_true: ((~Int.Lt x) n)>, ((~Int.Lt #0) $__n0))
(assume_guard_0, ((~Int.Lt $__x4) $__n0)) (assume_invariant_0, ((~Bool.And ((~Int.Ge $__x4) #0)) ((~Int.Le $__x4) $__n0))) (<label_ite_cond_true: ((~Int.Lt y) x)>, (if ((~Int.Lt #0) $__x4) then ((~Int.Lt #0) $__x4) else #true)) (assume_guard_2, (if ((~Int.Lt #0) $__x4) then ((~Int.Lt $__y5) $__x4) else #true)) (assume_invariant_2, (if ((~Int.Lt #0) $__x4) then ((~Bool.And ((~Int.Ge $__y5) #0)) ((~Int.Le $__y5) $__x4)) else #true)) (not_guard_2, (if ((~Int.Lt #0) $__x4) then (~Bool.Not ((~Int.Lt $__y6) $__x4)) else #true)) (invariant_2, (if ((~Int.Lt #0) $__x4) then ((~Bool.And ((~Int.Ge $__y6) #0)) ((~Int.Le $__y6) $__x4)) else #true)) (<label_ite_cond_false: !((~Int.Lt y) x)>, (if (if ((~Int.Lt #0) $__x4) then #false else #true) then (if ((~Int.Lt #0) $__x4) then #false else #true) else #true))
(n_pos, ((~Int.Gt $__n0) #0))
Proof Obligation:
((~Bool.And ((~Int.Ge ((~Int.Add $__x4) #1)) #0)) ((~Int.Le ((~Int.Add $__x4) #1)) $__n0))

Wrote problem to vcs/entry_invariant_0.smt2.
Wrote problem to vcs/entry_invariant_2.smt2.
Wrote problem to vcs/arbitrary_iter_maintain_invariant_2.smt2.
Wrote problem to vcs/entry_invariant_0.smt2.
Wrote problem to vcs/arbitrary_iter_maintain_invariant_0.smt2.
---
info:
Obligation: entry_invariant_0
Result: verified

Obligation: entry_invariant_2
Result: verified

Obligation: arbitrary_iter_maintain_invariant_2
Result: verified

Obligation: entry_invariant_0
Result: verified

Obligation: arbitrary_iter_maintain_invariant_0
Result: verified
-/
#guard_msgs in
#eval verify "cvc5" nestedEnv
