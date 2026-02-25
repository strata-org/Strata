/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.C_Simp.C_Simp
import Strata.Languages.C_Simp.Verify

def LinearSearchEnv :=
#strata
program C_Simp;

bool procedure linearSearch (arr: intArr, e: int)
  //@pre true;
  //@post true;
{
  var idx : int;

  idx = 0;
  while
  (idx < len(arr))
  //@decreases (len(arr)-idx)
  //@invariant true
  {
    if (e == get(arr, idx)) {
      return true;
    }
    idx = idx + 1;
  }

  return false;
}

#end

/--
info: program C_Simp;
bool procedure linearSearch(arr:intArr, e:int)//@pre true;
//@post true;
  ({
  varidx:int;
  idx=0;
  while(idx<(len(arr)))
  //@decreases ((len(arr))-idx)//@invariant true({
  if(e==(get(arr,idx))){
  returntrue;
  }
  ()idx=idx+1;
  }
  )returnfalse;
  }
  )
-/
#guard_msgs in
#eval IO.println LinearSearchEnv

/--
info: function linearSearch {
  pre: #true
  post: #true
  body:
{
  init (idx : int)
  idx := #0
  while
    (~Int.Lt idx (~Array.Len arr))
    (some (~Int.Sub (~Array.Len arr) idx))
    [#true]
  {
    if (e == (~Array.Get arr idx)) {
      return := #true
    }
    else {}
    idx := (~Int.Add idx #1)
  }
  return := #false
}
}
Errors: #[]
-/
#guard_msgs in
open Strata.C_Simp in
#eval TransM.run (translateProgram (LinearSearchEnv.commands))

/--
info: procedure linearSearch (arr : intArr, e : int) returns (return : bool)
spec {
  requires [pre]: true;
  ensures [post]: true;
  } {
  var idx : int;
  idx := 0;
  if (idx < Array.Len(arr)) {
    first_iter_asserts: {
      assert [entry_invariant_0]: true;
      assert [assert_measure_pos]: Array.Len(arr) - idx >= 0;
      }
    |arbitrary iter facts|: {
      |loop havoc|: {
        havoc return;
        havoc idx;
        }
      arbitrary_iter_assumes: {
        assume [assume_guard]: idx < Array.Len(arr);
        assume [assume_invariant_0]: true;
        assume [assume_measure_pos]: Array.Len(arr) - idx >= 0;
        }
      var |special-name-for-old-measure-value| : int := Array.Len(arr) - idx;
      if (e == Array.Get(arr, idx)) {
        return := true;
        }
      idx := idx + 1;
      assert [measure_decreases]: Array.Len(arr) - idx < special-name-for-old-measure-value;
      assert [measure_imp_not_guard]: if Array.Len(arr) - idx <= 0 then !(idx < Array.Len(arr)) else true;
      assert [arbitrary_iter_maintain_invariant_0]: true;
      }
    |loop havoc|: {
      havoc return;
      havoc idx;
      }
    assume [not_guard]: !(idx < Array.Len(arr));
    assume [invariant_0]: true;
    }
  return := false;
  };
-/
#guard_msgs in
#eval Strata.Core.formatProgram
        (Strata.to_core (Strata.C_Simp.get_program LinearSearchEnv))
        (extraFreeVars := #["intArr", "boolArr", "Array.Len", "Array.Get"])
