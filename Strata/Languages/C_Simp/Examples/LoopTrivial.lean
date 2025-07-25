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

def LoopTrivialEnv :=
#strata
program C_Simp;

procedure loopTrivial (n: int) -> int
  @pre true
  @post true
{
  var i : int;

  i := #0;
  while
  (i < n)
  @decreases (n-i)
  @invariant (i <= n)
  {
    i := i + #1;
  }

  @assert [i_eq_n] (i == n);
  return i;
}

#end

/--
info: procedureloopTrivial(n:int)->int@pretrue@posttrue({
  vari:int;
  (i):=#(0);
  while((i)<(n))@decreases((n)-(i))@invariant((i)<=(n))({
  (i):=(i)+(#(1));
  }
  )@assert[i_eq_n](i)==(n);
  returni;
  }
  )
-/
#guard_msgs in
#eval IO.println LoopTrivialEnv.format.render

/--
info: function loopTrivial {
  pre: #true
  post: #true
  body:
init (i : int) := init_i
i := #0
while(((~Int.Lt i) n))
(some ((~Int.Sub n) i))
(some ((~Int.Le i) n))
{i := ((~Int.Add i) #1)}
assert [i_eq_n] (i == n)
return := i
}
Errors: #[]
-/
#guard_msgs in
open Strata.C_Simp in
#eval TransM.run (translateProgram (LoopTrivialEnv.commands))

/--
info: (procedure loopTrivial :  ((n : int)) → ((return : int)))
modifies: []
preconditions: (pre, #true)
postconditions: (post, #true)
body: init (i : int) := init_i
i := #0
transformed loop block : {if ((~Int.Lt i) n) then {assert [entry_invariant] ((~Int.Le i) n)
  assert [assert measure_pos] ((~Int.Ge ((~Int.Sub n) i)) #0)}
 else{}
 arbitrary iter facts : {loop havoc : {havoc i}
  arbitrary_iter_assumes : {assume [assume_guard] ((~Int.Lt i) n)
   assume [assume_invariant] ((~Int.Le i) n)
   assume [assume_measure_pos] ((~Int.Ge ((~Int.Sub n) i)) #0)}
  init (special-name-for-old-measure-value : int) := ((~Int.Sub n) i)
  i := ((~Int.Add i) #1)
  assert [measure_decreases] ((~Int.Lt ((~Int.Sub n) i)) special-name-for-old-measure-value)
  assert [measure_imp_not_guard] (if ((~Int.Le ((~Int.Sub n) i)) #0) then (~Bool.Not ((~Int.Lt i) n)) else #true)
  assert [arbitrary_iter_maintain_invariant] ((~Int.Le i) n)}
 loop havoc : {havoc i}
 assume [not_guard] (~Bool.Not ((~Int.Lt i) n))
 assume [invariant] ((~Int.Le i) n)}
assert [i_eq_n] (i == n)
return := i
-/
#guard_msgs in
#eval Strata.to_boogie (Strata.C_Simp.get_program LoopTrivialEnv)

/--
info: [Strata.Boogie] Type checking succeeded.

[assume] pre satisfied via evaluation.


Obligation post proved via evaluation!


VCs:
Label: entry_invariant
Assumptions:
(<label_ite_cond_true: ((~Int.Lt i) n)>, ((~Int.Lt #0) $__n0))
Proof Obligation:
((~Int.Le #0) $__n0)

Label: assert measure_pos
Assumptions:
(<label_ite_cond_true: ((~Int.Lt i) n)>, ((~Int.Lt #0) $__n0))
Proof Obligation:
((~Int.Ge ((~Int.Sub $__n0) #0)) #0)

Label: measure_decreases
Assumptions:
(<label_ite_cond_true: ((~Int.Lt i) n)>, (if ((~Int.Lt #0) $__n0) then ((~Int.Lt #0) $__n0) else #true))
(<label_ite_cond_false: !((~Int.Lt i) n)>, (if (if ((~Int.Lt #0) $__n0) then #false else #true) then (if ((~Int.Lt #0) $__n0) then #false else #true) else #true)) (assume_guard, ((~Int.Lt $__i2) $__n0)) (assume_invariant, ((~Int.Le $__i2) $__n0)) (assume_measure_pos, ((~Int.Ge ((~Int.Sub $__n0) $__i2)) #0))
Proof Obligation:
((~Int.Lt ((~Int.Sub $__n0) ((~Int.Add $__i2) #1))) ((~Int.Sub $__n0) $__i2))

Label: measure_imp_not_guard
Assumptions:
(<label_ite_cond_true: ((~Int.Lt i) n)>, (if ((~Int.Lt #0) $__n0) then ((~Int.Lt #0) $__n0) else #true))
(<label_ite_cond_false: !((~Int.Lt i) n)>, (if (if ((~Int.Lt #0) $__n0) then #false else #true) then (if ((~Int.Lt #0) $__n0) then #false else #true) else #true)) (assume_guard, ((~Int.Lt $__i2) $__n0)) (assume_invariant, ((~Int.Le $__i2) $__n0)) (assume_measure_pos, ((~Int.Ge ((~Int.Sub $__n0) $__i2)) #0))
Proof Obligation:
(if ((~Int.Le ((~Int.Sub $__n0) ((~Int.Add $__i2) #1))) #0) then (~Bool.Not ((~Int.Lt ((~Int.Add $__i2) #1)) $__n0)) else #true)

Label: arbitrary_iter_maintain_invariant
Assumptions:
(<label_ite_cond_true: ((~Int.Lt i) n)>, (if ((~Int.Lt #0) $__n0) then ((~Int.Lt #0) $__n0) else #true))
(<label_ite_cond_false: !((~Int.Lt i) n)>, (if (if ((~Int.Lt #0) $__n0) then #false else #true) then (if ((~Int.Lt #0) $__n0) then #false else #true) else #true)) (assume_guard, ((~Int.Lt $__i2) $__n0)) (assume_invariant, ((~Int.Le $__i2) $__n0)) (assume_measure_pos, ((~Int.Ge ((~Int.Sub $__n0) $__i2)) #0))
Proof Obligation:
((~Int.Le ((~Int.Add $__i2) #1)) $__n0)

Label: i_eq_n
Assumptions:
(<label_ite_cond_true: ((~Int.Lt i) n)>, (if ((~Int.Lt #0) $__n0) then ((~Int.Lt #0) $__n0) else #true))
(<label_ite_cond_false: !((~Int.Lt i) n)>, (if (if ((~Int.Lt #0) $__n0) then #false else #true) then (if ((~Int.Lt #0) $__n0) then #false else #true) else #true)) (assume_guard, ((~Int.Lt $__i2) $__n0)) (assume_invariant, ((~Int.Le $__i2) $__n0)) (assume_measure_pos, ((~Int.Ge ((~Int.Sub $__n0) $__i2)) #0)) (not_guard, (~Bool.Not ((~Int.Lt $__i3) $__n0))) (invariant, ((~Int.Le $__i3) $__n0))
Proof Obligation:
($__i3 == $__n0)

Wrote problem to vcs/entry_invariant.smt2.
Wrote problem to vcs/assert measure_pos.smt2.
Wrote problem to vcs/measure_decreases.smt2.
Wrote problem to vcs/measure_imp_not_guard.smt2.
Wrote problem to vcs/arbitrary_iter_maintain_invariant.smt2.
Wrote problem to vcs/i_eq_n.smt2.
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

Obligation: i_eq_n
Result: verified
-/
#guard_msgs in
#eval Strata.C_Simp.verify "cvc5" LoopTrivialEnv
