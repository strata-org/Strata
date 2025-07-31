/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.C_Simp.C_Simp
import Strata.Languages.C_Simp.Verify

def MinEnv :=
#strata
program C_Simp;

procedure min (a: int, b: int) -> int
  @pre true
  @post true
{
  if (a < b) then {
    return a;
  } else {
    return b;
  }
}

#end

/--
info: proceduremin(a:int, b:int)->int@pretrue@posttrue({
  if((a)<(b))then{
  returna;
  }
  (else({
  returnb;
  }
  ))}
  )
-/
#guard_msgs in
#eval IO.println MinEnv.format.render

/--
info: function min {
  pre: #true
  post: #true
  body:
if ((~Int.Lt a) b) then {return := a}
else{return := b}
}
Errors: #[]
-/
#guard_msgs in
open Strata.C_Simp in
#eval TransM.run (translateProgram (MinEnv.commands))

/--
info: [Strata.Boogie] Type checking succeeded.

[assume] pre satisfied via evaluation.


Obligation post proved via evaluation!


VCs:

---
info:
-/
#guard_msgs in
#eval Strata.C_Simp.verify "cvc5" MinEnv
