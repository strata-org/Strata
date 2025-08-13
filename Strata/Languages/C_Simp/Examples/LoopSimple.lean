/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.C_Simp.C_Simp
import Strata.Languages.C_Simp.Verify

def LoopSimplePgm :=
#strata
program C_Simp;

procedure loopSimple (n: int) -> int
  @pre (n >= #0)
  @post true
{
  var sum : int;
  var i : int;

  sum := #0;
  i := #0;
  while(i < n)
  @decreases (n-i)
  @invariant (i <= n && ((i * (i-#1))/#2 == sum))
  {
    sum := sum + i;
    i := i + #1;
  }
  @assert [sum_assert] ((n * (n-#1))/#2 == sum);
  return sum;
}

#end

/--
info: program C_Simp;
procedureloopSimple(n:int)->int@pre(n)>=(#(0))@posttrue({
  varsum:int;
  vari:int;
  (sum):=#(0);
  (i):=#(0);
  while((i)<(n))@decreases((n)-(i))@invariant(((i)<=(n))&&((((i)*((i)-(#(1))))/(#(2)))==(sum)))({
  (sum):=(sum)+(i);
  (i):=(i)+(#(1));
  }
  )@assert[sum_assert](((n)*((n)-(#(1))))/(#(2)))==(sum);
  returnsum;
  }
  )
-/
#guard_msgs in
#eval IO.println LoopSimplePgm.format.render

/--
info: function loopSimple {
  pre: ((~Int.Ge n) #0)
  post: #true
  body:
init (sum : int) := init_sum
init (i : int) := init_i
sum := #0
i := #0
while (((~Int.Lt i) n)) (some ((~Int.Sub n) i)) (some ((~Bool.And ((~Int.Le i) n)) (((~Int.Div ((~Int.Mul i) ((~Int.Sub i) #1))) #2) == sum))) {sum := ((~Int.Add sum) i)
 i := ((~Int.Add i) #1)}
assert [sum_assert] (((~Int.Div ((~Int.Mul n) ((~Int.Sub n) #1))) #2) == sum)
return := sum
}
-/
#guard_msgs in
#eval Strata.C_Simp.get_program LoopSimplePgm

/--
info: (procedure loopSimple :  ((n : int)) → ((return : int)))
modifies: []
preconditions: (pre, ((~Int.Ge n) #0))
postconditions: (post, #true)
body: init (sum : int) := init_sum
init (i : int) := init_i
sum := #0
i := #0
if ((~Int.Lt i) n) then {first_iter_asserts : {assert [entry_invariant] ((~Bool.And ((~Int.Le i) n)) (((~Int.Div ((~Int.Mul i) ((~Int.Sub i) #1))) #2) == sum))
  assert [assert measure_pos] ((~Int.Ge ((~Int.Sub n) i)) #0)}
 arbitrary iter facts : {loop havoc : {havoc sum
   havoc i}
  arbitrary_iter_assumes : {assume [assume_guard] ((~Int.Lt i) n)
   assume [assume_invariant] ((~Bool.And ((~Int.Le i) n)) (((~Int.Div ((~Int.Mul i) ((~Int.Sub i) #1))) #2) == sum))
   assume [assume_measure_pos] ((~Int.Ge ((~Int.Sub n) i)) #0)}
  init (special-name-for-old-measure-value : int) := ((~Int.Sub n) i)
  sum := ((~Int.Add sum) i)
  i := ((~Int.Add i) #1)
  assert [measure_decreases] ((~Int.Lt ((~Int.Sub n) i)) special-name-for-old-measure-value)
  assert [measure_imp_not_guard] (if ((~Int.Le ((~Int.Sub n) i)) #0) then (~Bool.Not ((~Int.Lt i) n)) else #true)
  assert [arbitrary_iter_maintain_invariant] ((~Bool.And ((~Int.Le i) n)) (((~Int.Div ((~Int.Mul i) ((~Int.Sub i) #1))) #2) == sum))}
 loop havoc : {havoc sum
  havoc i}
 assume [not_guard] (~Bool.Not ((~Int.Lt i) n))
 assume [invariant] ((~Bool.And ((~Int.Le i) n)) (((~Int.Div ((~Int.Mul i) ((~Int.Sub i) #1))) #2) == sum))}
else{}
assert [sum_assert] (((~Int.Div ((~Int.Mul n) ((~Int.Sub n) #1))) #2) == sum)
return := sum
-/
#guard_msgs in
#eval Strata.to_boogie (Strata.C_Simp.get_program LoopSimplePgm)

/--
info: [Strata.Boogie] Type checking succeeded.


VCs:
Label: entry_invariant
Assumptions:
(<label_ite_cond_true: ((~Int.Lt i) n)>, ((~Int.Lt #0) $__n0))
(pre, ((~Int.Ge $__n0) #0))
Proof Obligation:
((~Bool.And ((~Int.Le #0) $__n0)) #true)

Label: assert measure_pos
Assumptions:
(<label_ite_cond_true: ((~Int.Lt i) n)>, ((~Int.Lt #0) $__n0))
(pre, ((~Int.Ge $__n0) #0))
Proof Obligation:
((~Int.Ge ((~Int.Sub $__n0) #0)) #0)

Label: measure_decreases
Assumptions:
(<label_ite_cond_true: ((~Int.Lt i) n)>, ((~Int.Lt #0) $__n0))
(assume_guard, ((~Int.Lt $__i3) $__n0)) (assume_invariant, ((~Bool.And ((~Int.Le $__i3) $__n0)) (((~Int.Div ((~Int.Mul $__i3) ((~Int.Sub $__i3) #1))) #2) == $__sum2))) (assume_measure_pos, ((~Int.Ge ((~Int.Sub $__n0) $__i3)) #0))
(pre, ((~Int.Ge $__n0) #0))
Proof Obligation:
((~Int.Lt ((~Int.Sub $__n0) ((~Int.Add $__i3) #1))) ((~Int.Sub $__n0) $__i3))

Label: measure_imp_not_guard
Assumptions:
(<label_ite_cond_true: ((~Int.Lt i) n)>, ((~Int.Lt #0) $__n0))
(assume_guard, ((~Int.Lt $__i3) $__n0)) (assume_invariant, ((~Bool.And ((~Int.Le $__i3) $__n0)) (((~Int.Div ((~Int.Mul $__i3) ((~Int.Sub $__i3) #1))) #2) == $__sum2))) (assume_measure_pos, ((~Int.Ge ((~Int.Sub $__n0) $__i3)) #0))
(pre, ((~Int.Ge $__n0) #0))
Proof Obligation:
(if ((~Int.Le ((~Int.Sub $__n0) ((~Int.Add $__i3) #1))) #0) then (~Bool.Not ((~Int.Lt ((~Int.Add $__i3) #1)) $__n0)) else #true)

Label: arbitrary_iter_maintain_invariant
Assumptions:
(<label_ite_cond_true: ((~Int.Lt i) n)>, ((~Int.Lt #0) $__n0))
(assume_guard, ((~Int.Lt $__i3) $__n0)) (assume_invariant, ((~Bool.And ((~Int.Le $__i3) $__n0)) (((~Int.Div ((~Int.Mul $__i3) ((~Int.Sub $__i3) #1))) #2) == $__sum2))) (assume_measure_pos, ((~Int.Ge ((~Int.Sub $__n0) $__i3)) #0))
(pre, ((~Int.Ge $__n0) #0))
Proof Obligation:
((~Bool.And ((~Int.Le ((~Int.Add $__i3) #1)) $__n0)) (((~Int.Div ((~Int.Mul ((~Int.Add $__i3) #1)) ((~Int.Sub ((~Int.Add $__i3) #1)) #1))) #2) == ((~Int.Add $__sum2) $__i3)))

Label: sum_assert
Assumptions:
(pre, ((~Int.Ge $__n0) #0))
(<label_ite_cond_true: ((~Int.Lt i) n)>, (if ((~Int.Lt #0) $__n0) then ((~Int.Lt #0) $__n0) else #true)) (assume_guard, (if ((~Int.Lt #0) $__n0) then ((~Int.Lt $__i3) $__n0) else #true)) (assume_invariant, (if ((~Int.Lt #0) $__n0) then ((~Bool.And ((~Int.Le $__i3) $__n0)) (((~Int.Div ((~Int.Mul $__i3) ((~Int.Sub $__i3) #1))) #2) == $__sum2)) else #true)) (assume_measure_pos, (if ((~Int.Lt #0) $__n0) then ((~Int.Ge ((~Int.Sub $__n0) $__i3)) #0) else #true)) (not_guard, (if ((~Int.Lt #0) $__n0) then (~Bool.Not ((~Int.Lt $__i5) $__n0)) else #true)) (invariant, (if ((~Int.Lt #0) $__n0) then ((~Bool.And ((~Int.Le $__i5) $__n0)) (((~Int.Div ((~Int.Mul $__i5) ((~Int.Sub $__i5) #1))) #2) == $__sum4)) else #true)) (<label_ite_cond_false: !((~Int.Lt i) n)>, (if (if ((~Int.Lt #0) $__n0) then #false else #true) then (if ((~Int.Lt #0) $__n0) then #false else #true) else #true))
Proof Obligation:
(((~Int.Div ((~Int.Mul $__n0) ((~Int.Sub $__n0) #1))) #2) == (if ((~Int.Lt #0) $__n0) then $__sum4 else #0))

Label: post
Assumptions:
(pre, ((~Int.Ge $__n0) #0))
(<label_ite_cond_true: ((~Int.Lt i) n)>, (if ((~Int.Lt #0) $__n0) then ((~Int.Lt #0) $__n0) else #true)) (assume_guard, (if ((~Int.Lt #0) $__n0) then ((~Int.Lt $__i3) $__n0) else #true)) (assume_invariant, (if ((~Int.Lt #0) $__n0) then ((~Bool.And ((~Int.Le $__i3) $__n0)) (((~Int.Div ((~Int.Mul $__i3) ((~Int.Sub $__i3) #1))) #2) == $__sum2)) else #true)) (assume_measure_pos, (if ((~Int.Lt #0) $__n0) then ((~Int.Ge ((~Int.Sub $__n0) $__i3)) #0) else #true)) (not_guard, (if ((~Int.Lt #0) $__n0) then (~Bool.Not ((~Int.Lt $__i5) $__n0)) else #true)) (invariant, (if ((~Int.Lt #0) $__n0) then ((~Bool.And ((~Int.Le $__i5) $__n0)) (((~Int.Div ((~Int.Mul $__i5) ((~Int.Sub $__i5) #1))) #2) == $__sum4)) else #true)) (<label_ite_cond_false: !((~Int.Lt i) n)>, (if (if ((~Int.Lt #0) $__n0) then #false else #true) then (if ((~Int.Lt #0) $__n0) then #false else #true) else #true))
Proof Obligation:
#true

Wrote problem to vcs/entry_invariant.smt2.
Wrote problem to vcs/assert_measure_pos.smt2.
Wrote problem to vcs/measure_decreases.smt2.
Wrote problem to vcs/measure_imp_not_guard.smt2.
Wrote problem to vcs/arbitrary_iter_maintain_invariant.smt2.
Wrote problem to vcs/sum_assert.smt2.
Wrote problem to vcs/post.smt2.
---
info:
Obligation: entry_invariant
Result: verified

Obligation: assert measure_pos
Result: verified

Obligation: measure_decreases
Result: verified

Obligation: measure_imp_not_guard
Result: verified

Obligation: arbitrary_iter_maintain_invariant
Result: verified

Obligation: sum_assert
Result: verified

Obligation: post
Result: verified
-/
#guard_msgs in
#eval Strata.C_Simp.verify "cvc5" LoopSimplePgm
