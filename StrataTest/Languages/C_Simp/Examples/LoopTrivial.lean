/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.C_Simp.C_Simp
import Strata.Languages.C_Simp.Verify

def LoopTrivialPgm :=
#strata
program C_Simp;

int procedure loopTrivial (n: int)
  //@pre (n >= 0);
  //@post true;
{
  var i : int;

  i = 0;
  while
  (i < n)
  //@decreases (n-i)
  //@invariant (i <= n)
  {
    i = i + 1;
  }

  //@assert [i_eq_n] (i == n);
  return i;
}

#end

/--
info: program C_Simp;
int procedure loopTrivial(n:int)//@pren>=(0);
//@posttrue;
  ({
  vari:int;
  i=0;
  while(i<n)
  //@decreases(n-i)//@invariant(i<=n)({
  i=i+(1);
  }
  )//@assert [i_eq_n]i==n;
  returni;
  }
  )
-/
#guard_msgs in
#eval IO.println LoopTrivialPgm

/-

info: function loopTrivial {
  pre: (~Int.Ge n #0)
  post: #true
  body:
init (i : int) := init_i
i := #0
while ((~Int.Lt i n)) (some (~Int.Sub n i)) (some (~Int.Le i n)) {i := (~Int.Add i #1)}
assert [i_eq_n] (i == n)
return := i
}
Errors: #[]
-/
#guard_msgs in
open Strata.C_Simp in
#eval TransM.run (translateProgram (LoopTrivialPgm.commands))

/-

info: procedure loopTrivial :  ((n : int)) → ((return : int))
  modifies: []
  preconditions: (pre, (~Int.Ge n #0))
  postconditions: (post, #true)
{
  init (i : int) := init_i
  i := #0
  if (~Int.Lt i n) then {first_iter_asserts : {assert [entry_invariant] (~Int.Le i n)
    assert [assert_measure_pos] (~Int.Ge (~Int.Sub n i) #0)}
   arbitrary iter facts : {loop havoc : {havoc i}
    arbitrary_iter_assumes : {assume [assume_guard] (~Int.Lt i n)
     assume [assume_invariant] (~Int.Le i n)
     assume [assume_measure_pos] (~Int.Ge (~Int.Sub n i) #0)}
    init (special-name-for-old-measure-value : int) := (~Int.Sub n i)
    i := (~Int.Add i #1)
    assert [measure_decreases] (~Int.Lt (~Int.Sub n i) special-name-for-old-measure-value)
    assert [measure_imp_not_guard] (if (~Int.Le (~Int.Sub n i) #0) then (~Bool.Not (~Int.Lt i n)) else #true)
    assert [arbitrary_iter_maintain_invariant] (~Int.Le i n)}
   loop havoc : {havoc i}
   assume [not_guard] (~Bool.Not (~Int.Lt i n))
   assume [invariant] (~Int.Le i n)}
  else{}
  assert [i_eq_n] (i == n)
  return := i
}
-/
#guard_msgs in
#eval Strata.to_core (Strata.C_Simp.get_program LoopTrivialPgm)

/-

info: [Strata.Core] Type checking succeeded.
-/
#guard_msgs in
#eval Strata.C_Simp.verify "cvc5" LoopTrivialPgm
