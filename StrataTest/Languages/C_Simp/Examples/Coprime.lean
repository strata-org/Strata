/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.C_Simp.C_Simp
import Strata.Languages.C_Simp.Verify

def CoprimePgm :=
#strata
program C_Simp;

bool procedure coprime (a: int, b: int)
  //@pre ((a > 0) && (b > 0));
  //@post true;
{
  var i : int;
  i = a;
  if (b < a) {
    i = b;
  }

  while (i > 1)
    //@decreases i
    //@invariant true
  {
    if (((b % i) == 0) && ((a % i) == 0)) {
      return false;
    }
    i = i - 1;
  }
  return true;
}

#end

/--
info: program C_Simp;
bool procedure coprime(a:int, b:int)//@pre (a>0)&&(b>0);
//@post true;
  ({
  vari:int;
  i=a;
  if(b<a){
  i=b;
  }
  ()while(i>1)
  //@decreases i//@invariant true({
  if(((b%i)==0)&&((a%i)==0)){
  returnfalse;
  }
  ()i=i-1;
  }
  )returntrue;
  }
  )
-/
#guard_msgs in
#eval IO.println CoprimePgm


/--
info: function coprime {
  pre: (~Bool.And (~Int.Gt a #0) (~Int.Gt b #0))
  post: #true
  body:
{
  init (i : int)
  i := a
  if (~Int.Lt b a) {
    i := b
  }
  else {}
  while
    (~Int.Gt i #1)
    (some i)
    [#true]
  {
    if (~Bool.And ((~Int.Mod b i) == #0) ((~Int.Mod a i) == #0)) {
      return := #false
    }
    else {}
    i := (~Int.Sub i #1)
  }
  return := #true
}
}
Errors: #[]
-/
#guard_msgs in
open Strata.C_Simp in
#eval TransM.run Inhabited.default ((translateProgram (CoprimePgm.commands)).map (·.stripMetaData))

/--
info: procedure coprime (a : int, b : int) returns (return : bool)
spec {
  requires [pre]: a > 0 && b > 0;
  ensures [post]: true;
  } {
  var i : int;
  i := a;
  if (b < a) {
    i := b;
    }
  if (i > 1) {
    first_iter_asserts: {
      assert [entry_invariant_0]: true;
      assert [assert_measure_pos]: i >= 0;
      }
    |arbitrary iter facts|: {
      |loop havoc|: {
        havoc return;
        havoc i;
        }
      arbitrary_iter_assumes: {
        assume [assume_guard]: i > 1;
        assume [assume_invariant_0]: true;
        assume [assume_measure_pos]: i >= 0;
        }
      var |special-name-for-old-measure-value| : int := i;
      if (b mod i == 0 && a mod i == 0) {
        return := false;
        }
      i := i - 1;
      assert [measure_decreases]: i < special-name-for-old-measure-value;
      assert [measure_imp_not_guard]: if i <= 0 then !(i > 1) else true;
      assert [arbitrary_iter_maintain_invariant_0]: true;
      }
    |loop havoc|: {
      havoc return;
      havoc i;
      }
    assume [not_guard]: !(i > 1);
    assume [invariant_0]: true;
    }
  return := true;
  };
-/
#guard_msgs in
#eval Strata.to_core (Strata.C_Simp.get_program CoprimePgm)
