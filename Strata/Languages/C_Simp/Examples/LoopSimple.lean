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

import Strata.Languages.C_Simp.C_Simp
import Strata.Languages.C_Simp.Verify

def LoopSimpleEnv :=
#strata
program C_Simp;

procedure loopSimple (n: int) -> int
  @pre true
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
info: procedureloopSimple(n:int)->int@pretrue@posttrue({
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
#eval IO.println LoopSimpleEnv.format.render

/--
info: function loopSimple {
  pre: #true
  post: #true
  body:
init (sum : int) := init_sum
init (i : int) := init_i
sum := #0
i := #0
while(((~Int.Lt i) n))
(some ((~Int.Sub n) i))
(some ((~Bool.And ((~Int.Le i) n)) (((~Int.Div ((~Int.Mul i) ((~Int.Sub i) #1))) #2) == sum)))
{sum := ((~Int.Add sum) i)
 i := ((~Int.Add i) #1)}
assert [sum_assert] (((~Int.Div ((~Int.Mul n) ((~Int.Sub n) #1))) #2) == sum)
return := sum
}
-/
#guard_msgs in
#eval Strata.C_Simp.get_program LoopSimpleEnv

/--
info: (procedure loopSimple :  ((n : int)) → ((return : int)))
modifies: []
preconditions: (pre, #true)
postconditions: (post, #true)
body: init (sum : int) := init_sum
init (i : int) := init_i
sum := #0
i := #0
transformed loop block : {if ((~Int.Lt i) n) then {assert [entry_invariant] ((~Bool.And ((~Int.Le i) n)) (((~Int.Div ((~Int.Mul i) ((~Int.Sub i) #1))) #2) == sum))
  assert [assert measure_pos] ((~Int.Ge ((~Int.Sub n) i)) #0)}
 else{}
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
assert [sum_assert] (((~Int.Div ((~Int.Mul n) ((~Int.Sub n) #1))) #2) == sum)
return := sum
-/
#guard_msgs in
#eval Strata.to_boogie (Strata.C_Simp.get_program LoopSimpleEnv)

/--
info: [Strata.Boogie] Type checking succeeded.

[assume] pre satisfied via evaluation.


Obligation post proved via evaluation!


VCs:
Label: entry_invariant
Assumptions:
(<label_ite_cond_true: ((~Int.Lt i) n)>, ((~Int.Lt #0) $__n0))
Proof Obligation:
((~Bool.And ((~Int.Le #0) $__n0)) #true)

Label: assert measure_pos
Assumptions:
(<label_ite_cond_true: ((~Int.Lt i) n)>, ((~Int.Lt #0) $__n0))
Proof Obligation:
((~Int.Ge ((~Int.Sub $__n0) #0)) #0)

Label: measure_decreases
Assumptions:
(<label_ite_cond_true: ((~Int.Lt i) n)>, (if ((~Int.Lt #0) $__n0) then ((~Int.Lt #0) $__n0) else #true))
(<label_ite_cond_false: !((~Int.Lt i) n)>, (if (if ((~Int.Lt #0) $__n0) then #false else #true) then (if ((~Int.Lt #0) $__n0) then #false else #true) else #true)) (assume_guard, ((~Int.Lt $__i3) $__n0)) (assume_invariant, ((~Bool.And ((~Int.Le $__i3) $__n0)) (((~Int.Div ((~Int.Mul $__i3) ((~Int.Sub $__i3) #1))) #2) == $__sum2))) (assume_measure_pos, ((~Int.Ge ((~Int.Sub $__n0) $__i3)) #0))
Proof Obligation:
((~Int.Lt ((~Int.Sub $__n0) ((~Int.Add $__i3) #1))) ((~Int.Sub $__n0) $__i3))

Label: measure_imp_not_guard
Assumptions:
(<label_ite_cond_true: ((~Int.Lt i) n)>, (if ((~Int.Lt #0) $__n0) then ((~Int.Lt #0) $__n0) else #true))
(<label_ite_cond_false: !((~Int.Lt i) n)>, (if (if ((~Int.Lt #0) $__n0) then #false else #true) then (if ((~Int.Lt #0) $__n0) then #false else #true) else #true)) (assume_guard, ((~Int.Lt $__i3) $__n0)) (assume_invariant, ((~Bool.And ((~Int.Le $__i3) $__n0)) (((~Int.Div ((~Int.Mul $__i3) ((~Int.Sub $__i3) #1))) #2) == $__sum2))) (assume_measure_pos, ((~Int.Ge ((~Int.Sub $__n0) $__i3)) #0))
Proof Obligation:
(if ((~Int.Le ((~Int.Sub $__n0) ((~Int.Add $__i3) #1))) #0) then (~Bool.Not ((~Int.Lt ((~Int.Add $__i3) #1)) $__n0)) else #true)

Label: arbitrary_iter_maintain_invariant
Assumptions:
(<label_ite_cond_true: ((~Int.Lt i) n)>, (if ((~Int.Lt #0) $__n0) then ((~Int.Lt #0) $__n0) else #true))
(<label_ite_cond_false: !((~Int.Lt i) n)>, (if (if ((~Int.Lt #0) $__n0) then #false else #true) then (if ((~Int.Lt #0) $__n0) then #false else #true) else #true)) (assume_guard, ((~Int.Lt $__i3) $__n0)) (assume_invariant, ((~Bool.And ((~Int.Le $__i3) $__n0)) (((~Int.Div ((~Int.Mul $__i3) ((~Int.Sub $__i3) #1))) #2) == $__sum2))) (assume_measure_pos, ((~Int.Ge ((~Int.Sub $__n0) $__i3)) #0))
Proof Obligation:
((~Bool.And ((~Int.Le ((~Int.Add $__i3) #1)) $__n0)) (((~Int.Div ((~Int.Mul ((~Int.Add $__i3) #1)) ((~Int.Sub ((~Int.Add $__i3) #1)) #1))) #2) == ((~Int.Add $__sum2) $__i3)))

Label: sum_assert
Assumptions:
(<label_ite_cond_true: ((~Int.Lt i) n)>, (if ((~Int.Lt #0) $__n0) then ((~Int.Lt #0) $__n0) else #true))
(<label_ite_cond_false: !((~Int.Lt i) n)>, (if (if ((~Int.Lt #0) $__n0) then #false else #true) then (if ((~Int.Lt #0) $__n0) then #false else #true) else #true)) (assume_guard, ((~Int.Lt $__i3) $__n0)) (assume_invariant, ((~Bool.And ((~Int.Le $__i3) $__n0)) (((~Int.Div ((~Int.Mul $__i3) ((~Int.Sub $__i3) #1))) #2) == $__sum2))) (assume_measure_pos, ((~Int.Ge ((~Int.Sub $__n0) $__i3)) #0)) (not_guard, (~Bool.Not ((~Int.Lt $__i5) $__n0))) (invariant, ((~Bool.And ((~Int.Le $__i5) $__n0)) (((~Int.Div ((~Int.Mul $__i5) ((~Int.Sub $__i5) #1))) #2) == $__sum4)))
Proof Obligation:
(((~Int.Div ((~Int.Mul $__n0) ((~Int.Sub $__n0) #1))) #2) == $__sum4)

Wrote problem to vcs/entry_invariant.smt2.
Wrote problem to vcs/assert measure_pos.smt2.
Wrote problem to vcs/measure_decreases.smt2.
Wrote problem to vcs/measure_imp_not_guard.smt2.
Wrote problem to vcs/arbitrary_iter_maintain_invariant.smt2.
Wrote problem to vcs/sum_assert.smt2.
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
-/
#guard_msgs in
#eval Strata.C_Simp.verify "cvc5" LoopSimpleEnv
