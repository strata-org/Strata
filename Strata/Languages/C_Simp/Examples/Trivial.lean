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

def TrivialEnv :=
#strata
program C_Simp;

procedure trivial () -> bool
  @pre true
  @post true
{
  return true;
}

#end

/--
info: proceduretrivial()->bool@pretrue@posttrue({
  returntrue;
  }
  )
-/
#guard_msgs in
#eval IO.println TrivialEnv.format.render

/--
info: function trivial {
  pre: #true
  post: #true
  body:
return := #true
}
Errors: #[]
-/
#guard_msgs in
#eval Strata.C_Simp.TransM.run (Strata.C_Simp.translateProgram (TrivialEnv.commands))

/--
info: [Strata.Boogie] Type checking succeeded.

[assume] pre satisfied via evaluation.


Obligation post proved via evaluation!


VCs:

---
info:
-/
#guard_msgs in
#eval Strata.C_Simp.verify "cvc5" TrivialEnv
