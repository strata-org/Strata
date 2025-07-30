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

def LinearSearchEnv :=
#strata
program C_Simp;

procedure linearSearch (arr: intArr, e: int) -> bool
  @pre true
  @post true
{
  var idx : int;

  idx := #0;
  while
  (idx < len(arr))
  @decreases (len(arr)-idx)
  @invariant true
  {
    if (e == get(arr, idx)) then {
      return true;
    }
    idx := idx + #1;
  }

  return false;
}

#end

/--
info: procedurelinearSearch(arr:intArr, e:int)->bool@pretrue@posttrue({
  varidx:int;
  (idx):=#(0);
  while((idx)<(len(arr)))@decreases((len(arr))-(idx))@invariant(true)({
  if((e)==(get(arr,idx)))then{
  returntrue;
  }
  ()(idx):=(idx)+(#(1));
  }
  )returnfalse;
  }
  )
-/
#guard_msgs in
#eval IO.println LinearSearchEnv.format.render

/--
info: function linearSearch {
  pre: #true
  post: #true
  body:
init (idx : int) := init_idx
idx := #0
while (((~Int.Lt idx) (~Array.Len arr))) (some ((~Int.Sub (~Array.Len arr)) idx)) (some #true) {if (e == ((~Array.Get arr) idx)) then {return := #true}
 else{}
 idx := ((~Int.Add idx) #1)}
return := #false
}
Errors: #[]
-/
#guard_msgs in
open Strata.C_Simp in
#eval TransM.run (translateProgram (LinearSearchEnv.commands))

/--
info: (procedure linearSearch :  ((arr : intArr) (e : int)) → ((return : bool)))
modifies: []
preconditions: (pre, #true)
postconditions: (post, #true)
body: init (idx : int) := init_idx
idx := #0
transformed loop block : {if ((~Int.Lt idx) (~Array.Len arr)) then {assert [entry_invariant] #true
  assert [assert measure_pos] ((~Int.Ge ((~Int.Sub (~Array.Len arr)) idx)) #0)}
 else{}
 arbitrary iter facts : {loop havoc : {havoc return
   havoc idx}
  arbitrary_iter_assumes : {assume [assume_guard] ((~Int.Lt idx) (~Array.Len arr))
   assume [assume_invariant] #true
   assume [assume_measure_pos] ((~Int.Ge ((~Int.Sub (~Array.Len arr)) idx)) #0)}
  init (special-name-for-old-measure-value : int) := ((~Int.Sub (~Array.Len arr)) idx)
  if (e == ((~Array.Get arr) idx)) then {return := #true}
  else{}
  idx := ((~Int.Add idx) #1)
  assert [measure_decreases] ((~Int.Lt ((~Int.Sub (~Array.Len arr)) idx)) special-name-for-old-measure-value)
  assert [measure_imp_not_guard] (if ((~Int.Le ((~Int.Sub (~Array.Len arr)) idx)) #0) then (~Bool.Not ((~Int.Lt idx) (~Array.Len arr))) else #true)
  assert [arbitrary_iter_maintain_invariant] #true}
 loop havoc : {havoc return
  havoc idx}
 assume [not_guard] (~Bool.Not ((~Int.Lt idx) (~Array.Len arr)))
 assume [invariant] #true}
return := #false
-/
#guard_msgs in
#eval Strata.to_boogie (Strata.C_Simp.get_program LinearSearchEnv)
