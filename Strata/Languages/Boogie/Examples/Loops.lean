/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Boogie.Verifier
import Strata.Transform.StructuredToUnstructured

---------------------------------------------------------------------
namespace Strata

def gaussPgm :=
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

def singleCFG (p : Program) : Imperative.CFG String (Imperative.DetBlock String Boogie.Command Boogie.Expression) :=
  let boogiePgm := TransM.run (translateProgram p) |>.fst
  let proc := match boogiePgm.decls.filter (λ d => d.kind = .proc) with | (.proc p) :: _ => p | _ => panic!"No procedure!"
  Imperative.stmtsToCFG proc.body

/--
info: Entry: l_6

[l_6:
   [init (i : int) := init_i_0]
   cgoto #true l_5 l_5,
 l_5:
   [i := #0]
   cgoto #true l_4 l_4,
 l_4:
   [s := #0]
   cgoto #true loop_entry_1 loop_entry_1,
 loop_entry_1:
   [assert [inv] (((~Bool.And : (arrow bool (arrow bool bool))) (((~Bool.And : (arrow bool (arrow bool bool))) (((~Int.Le : (arrow int (arrow int bool))) #0) (i : int))) (((~Int.Le : (arrow int (arrow int bool))) (i : int)) (n : int)))) ((s : int) == (((~Int.Div : (arrow int (arrow int int))) (((~Int.Mul : (arrow int (arrow int int))) (i : int)) (((~Int.Add : (arrow int (arrow int int))) (i : int)) #1))) #2)))]
   cgoto (((~Int.Lt : (arrow int (arrow int bool))) (i : int)) (n : int)) l_3 end_0,
 l_3:
   [i := (((~Int.Add : (arrow int (arrow int int))) (i : int)) #1)]
   cgoto #true l_2 l_2,
 l_2:
   [s := (((~Int.Add : (arrow int (arrow int int))) (s : int)) (i : int))]
   cgoto #true loop_entry_1 loop_entry_1,
 end_0:
   []
   finish]
-/
#guard_msgs in
#eval (Std.format (singleCFG gaussPgm))

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
#eval verify "cvc5" gaussPgm

def nestedPgm :=
#strata
program Boogie;

const top : int;
axiom [top100]: top == 100;

procedure nested(n : int) returns (s : int)
spec {
  requires [n_pos]: n > 0;
  requires [n_lt_top]: n < top;
} {
  var x: int;
  var y: int;
  x := 0;
  while (x < n)
    invariant x >= 0 && x <= n && n < top;
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
info: Entry: l_8

[l_8:
   [init (x : int) := init_x_0]
   cgoto #true l_7 l_7,
 l_7:
   [init (y : int) := init_y_1]
   cgoto #true l_6 l_6,
 l_6:
   [x := #0]
   cgoto #true loop_entry_1 loop_entry_1,
 loop_entry_1:
   [assert [inv] (((~Bool.And : (arrow bool (arrow bool bool))) (((~Bool.And : (arrow bool (arrow bool bool))) (((~Int.Ge : (arrow int (arrow int bool))) (x : int)) #0)) (((~Int.Le : (arrow int (arrow int bool))) (x : int)) (n : int)))) (((~Int.Lt : (arrow int (arrow int bool))) (n : int)) (~top : int)))]
   cgoto (((~Int.Lt : (arrow int (arrow int bool))) (x : int)) (n : int)) l_5 end_0,
 l_5:
   [y := #0]
   cgoto #true loop_entry_3 loop_entry_3,
 loop_entry_3:
   [assert [inv] (((~Bool.And : (arrow bool (arrow bool bool))) (((~Int.Ge : (arrow int (arrow int bool))) (y : int)) #0)) (((~Int.Le : (arrow int (arrow int bool))) (y : int)) (x : int)))]
   cgoto (((~Int.Lt : (arrow int (arrow int bool))) (y : int)) (x : int)) l_4 l_2,
 l_4:
   [y := (((~Int.Add : (arrow int (arrow int int))) (y : int)) #1)]
   cgoto #true loop_entry_3 loop_entry_3,
 l_2:
   [x := (((~Int.Add : (arrow int (arrow int int))) (x : int)) #1)]
   cgoto #true loop_entry_1 loop_entry_1,
 end_0:
   []
   finish]
-/
#guard_msgs in
#eval (Std.format (singleCFG nestedPgm))

/--
info:
Obligation: entry_invariant_0
Result: verified

Obligation: entry_invariant_1
Result: verified

Obligation: arbitrary_iter_maintain_invariant_1
Result: verified

Obligation: arbitrary_iter_maintain_invariant_0
Result: verified
-/
#guard_msgs in
#eval verify "cvc5" nestedPgm Options.quiet
