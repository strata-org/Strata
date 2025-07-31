/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.C_Simp.C_Simp
import Strata.Languages.C_Simp.Verify

def CoprimeEnv :=
#strata
program C_Simp;

procedure coprime (a: int, b: int) -> bool
  @pre ((a > #0) && (b > #0))
  @post true
{
  var (i: int) := a;
  if (b < a) then {
    i := b;
  }

  while (i > #1)
    @decreases i
    @invariant true
  {
    if (((b % i) == #0) && ((a % i) == #0)) then {
      return false;
    }
    i := i - #1;
  }
  return true;
}

#end

/--
info: procedurecoprime(a:int, b:int)->bool@pre((a)>(#(0)))&&((b)>(#(0)))@posttrue({
  var(i:int):=a;
  if((b)<(a))then{
  (i):=b;
  }
  ()while((i)>(#(1)))@decreases(i)@invariant(true)({
  if((((b)%(i))==(#(0)))&&(((a)%(i))==(#(0))))then{
  returnfalse;
  }
  ()(i):=(i)-(#(1));
  }
  )returntrue;
  }
  )
-/
#guard_msgs in
#eval IO.println CoprimeEnv.format.render


/--
info: function coprime {
  pre: ((~Bool.And ((~Int.Gt a) #0)) ((~Int.Gt b) #0))
  post: #true
  body:
init (i : int) := a
if ((~Int.Lt b) a) then {i := b}
else{}
while (((~Int.Gt i) #1)) (some i) (some #true) {if ((~Bool.And (((~Int.Mod b) i) == #0)) (((~Int.Mod a) i) == #0)) then {return := #false}
 else{}
 i := ((~Int.Sub i) #1)}
return := #true
}
Errors: #[]
-/
#guard_msgs in
open Strata.C_Simp in
#eval TransM.run (translateProgram (CoprimeEnv.commands))

/--
info: (procedure coprime :  ((a : int) (b : int)) → ((return : bool)))
modifies: []
preconditions: (pre, ((~Bool.And ((~Int.Gt a) #0)) ((~Int.Gt b) #0)))
postconditions: (post, #true)
body: init (i : int) := a
if ((~Int.Lt b) a) then {i := b}
else{}
if ((~Int.Gt i) #1) then {first_iter_asserts : {assert [entry_invariant] #true
  assert [assert measure_pos] ((~Int.Ge i) #0)}
 arbitrary iter facts : {loop havoc : {havoc return
   havoc i}
  arbitrary_iter_assumes : {assume [assume_guard] ((~Int.Gt i) #1)
   assume [assume_invariant] #true
   assume [assume_measure_pos] ((~Int.Ge i) #0)}
  init (special-name-for-old-measure-value : int) := i
  if ((~Bool.And (((~Int.Mod b) i) == #0)) (((~Int.Mod a) i) == #0)) then {return := #false}
  else{}
  i := ((~Int.Sub i) #1)
  assert [measure_decreases] ((~Int.Lt i) special-name-for-old-measure-value)
  assert [measure_imp_not_guard] (if ((~Int.Le i) #0) then (~Bool.Not ((~Int.Gt i) #1)) else #true)
  assert [arbitrary_iter_maintain_invariant] #true}
 loop havoc : {havoc return
  havoc i}
 assume [not_guard] (~Bool.Not ((~Int.Gt i) #1))
 assume [invariant] #true}
else{}
return := #true
-/
#guard_msgs in
#eval Strata.to_boogie (Strata.C_Simp.get_program CoprimeEnv)
