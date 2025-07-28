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
