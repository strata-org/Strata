/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.C_Simp.C_Simp
import Strata.Languages.C_Simp.Verify

def LoopSimplePgm :=
#strata
program C_Simp;

int procedure loopSimple (n: int)
  //@pre (n >= 0);
  //@post true;
{
  var sum : int;
  var i : int;

  sum = 0;
  i = 0;
  while(i < n)
  //@decreases (n-i)
  //@invariant (i <= n && ((i * (i-1))/2 == sum))
  {
    sum = sum + i;
    i = i + 1;
  }
  //@assert [sum_assert] ((n * (n-1))/2 == sum);
  return sum;
}

#end

/--
info: program C_Simp;
int procedure loopSimple(n:int)//@pren>=(0);
//@posttrue;
  ({
  varsum:int;
  vari:int;
  sum=0;
  i=0;
  while(i<n)
  //@decreases(n-i)//@invariant((i<=n)&&(((i*(i-(1)))/(2))==sum))({
  sum=sum+i;
  i=i+(1);
  }
  )//@assert [sum_assert]((n*(n-(1)))/(2))==sum;
  returnsum;
  }
  )
-/
#guard_msgs in
#eval IO.println LoopSimplePgm

/-

info: function loopSimple {
  pre: (~Int.Ge n #0)
  post: #true
  body:
init (sum : int) := init_sum
init (i : int) := init_i
sum := #0
i := #0
while ((~Int.Lt
 i
 n)) (some (~Int.Sub
 n
 i)) (some (~Bool.And (~Int.Le i n) ((~Int.Div (~Int.Mul i (~Int.Sub i #1)) #2) == sum))) {sum := (~Int.Add sum i)
 i := (~Int.Add i #1)}
assert [sum_assert] ((~Int.Div (~Int.Mul n (~Int.Sub n #1)) #2) == sum)
return := sum
}
-/
#guard_msgs in
#eval Strata.C_Simp.get_program LoopSimplePgm

/-

info: procedure loopSimple :  ((n : int)) → ((return : int))
  modifies: []
  preconditions: (pre, (~Int.Ge n #0))
  postconditions: (post, #true)
{
  init (sum : int) := init_sum
  init (i : int) := init_i
  sum := #0
  i := #0
  if (~Int.Lt
   i
   n) then {first_iter_asserts : {assert [entry_invariant] (~Bool.And
     (~Int.Le i n)
     ((~Int.Div (~Int.Mul i (~Int.Sub i #1)) #2) == sum))
    assert [assert_measure_pos] (~Int.Ge (~Int.Sub n i) #0)}
   arbitrary iter facts : {loop havoc : {havoc sum
     havoc i}
    arbitrary_iter_assumes : {assume [assume_guard] (~Int.Lt i n)
     assume [assume_invariant] (~Bool.And (~Int.Le i n) ((~Int.Div (~Int.Mul i (~Int.Sub i #1)) #2) == sum))
     assume [assume_measure_pos] (~Int.Ge (~Int.Sub n i) #0)}
    init (special-name-for-old-measure-value : int) := (~Int.Sub n i)
    sum := (~Int.Add sum i)
    i := (~Int.Add i #1)
    assert [measure_decreases] (~Int.Lt (~Int.Sub n i) special-name-for-old-measure-value)
    assert [measure_imp_not_guard] (if (~Int.Le (~Int.Sub n i) #0) then (~Bool.Not (~Int.Lt i n)) else #true)
    assert [arbitrary_iter_maintain_invariant] (~Bool.And
     (~Int.Le i n)
     ((~Int.Div (~Int.Mul i (~Int.Sub i #1)) #2) == sum))}
   loop havoc : {havoc sum
    havoc i}
   assume [not_guard] (~Bool.Not (~Int.Lt i n))
   assume [invariant] (~Bool.And (~Int.Le i n) ((~Int.Div (~Int.Mul i (~Int.Sub i #1)) #2) == sum))}
  else{}
  assert [sum_assert] ((~Int.Div (~Int.Mul n (~Int.Sub n #1)) #2) == sum)
  return := sum
}
-/
#guard_msgs in
#eval Strata.to_core (Strata.C_Simp.get_program LoopSimplePgm)

/-

info: [Strata.Core] Type checking succeeded.
-/
#guard_msgs in
#eval Strata.C_Simp.verify "cvc5" LoopSimplePgm
