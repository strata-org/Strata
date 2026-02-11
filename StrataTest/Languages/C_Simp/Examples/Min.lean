/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.C_Simp.C_Simp
import Strata.Languages.C_Simp.Verify

def MinPgm :=
#strata
program C_Simp;

int procedure min (a: int, b: int)
  //@pre true;
  //@post true;
{
  if (a < b) {
    return a;
  } else {
    return b;
  }
}

#end

/--
info: program C_Simp;
int procedure min(a:int, b:int)//@pretrue;
//@posttrue;
  ({
  if(a<b){
  returna;
  }
  (else({
  returnb;
  }
  ))}
  )
-/
#guard_msgs in
#eval IO.println MinPgm

/-

info: function min {
  pre: #true
  post: #true
  body:
if (~Int.Lt a b) then {return := a}
else{return := b}
}
Errors: #[]
-/
#guard_msgs in
open Strata.C_Simp in
#eval TransM.run (translateProgram (MinPgm.commands))

/-

info: [Strata.Core] Type checking succeeded.
-/
#guard_msgs in
#eval Strata.C_Simp.verify "cvc5" MinPgm
