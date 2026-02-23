/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.C_Simp.C_Simp
import Strata.Languages.C_Simp.Verify

def TrivialPgm :=
#strata
program C_Simp;

bool procedure trivial ()
  //@pre true;
  //@post true;
{
  return true;
}

#end

/--
info: program C_Simp;
bool procedure trivial()//@pre true;
//@post true;
  ({
  returntrue;
  }
  )
-/
#guard_msgs in
#eval IO.println TrivialPgm

/--
info: function trivial {
  pre: #true
  post: #true
  body:
{
  return := #true
}
}
Errors: #[]
-/
#guard_msgs in
#eval Strata.C_Simp.TransM.run (Strata.C_Simp.translateProgram (TrivialPgm.commands))

/--
info: [Strata.Core] Type checking succeeded.


VCs:
Label: post
Property: assert
Obligation:
true

---
info:
Obligation: post
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval Strata.C_Simp.verify TrivialPgm
