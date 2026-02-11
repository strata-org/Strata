/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.C_Simp.C_Simp
import Strata.Languages.C_Simp.Verify

def SimpleTestEnv :=
#strata
program C_Simp;

int procedure simpleTest (x: int, y: int)
  //@pre y > 0;
  //@post true;
{
  var z : int;
  z = x + y;
  //@assert [test_assert] z > x;
  if (z > 10) {
    z = z - 1;
  } else {
    z = z + 1;
  }
  //@assume [test_assume] z > 0;
  return 0;
}

#end

/--
info: program C_Simp;
int procedure simpleTest(x:int, y:int)//@prey>(0);
//@posttrue;
  ({
  varz:int;
  z=x+y;
  //@assert [test_assert]z>x;
  if(z>(10)){
  z=z-(1);
  }
  (else({
  z=z+(1);
  }
  ))//@assume [test_assume]z>(0);
  return0;
  }
  )
-/
#guard_msgs in
#eval IO.println SimpleTestEnv


/-

info: function simpleTest {
  pre: (~Int.Gt y #0)
  post: #true
  body:
init (z : int) := init_z
z := (~Int.Add x y)
assert [test_assert] (~Int.Gt z x)
if (~Int.Gt z #10) then {z := (~Int.Sub z #1)}
else{z := (~Int.Add z #1)}
assume [test_assume] (~Int.Gt z #0)
return := #0
}
Errors: #[]
-/
#guard_msgs in
open Strata.C_Simp in
#eval TransM.run (translateProgram (SimpleTestEnv.commands))

/-

info: [Strata.Core] Type checking succeeded.
-/
#guard_msgs in
#eval Strata.C_Simp.verify "cvc5" SimpleTestEnv
