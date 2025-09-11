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
(bool)proceduretrivial()//@pretrue;
//@posttrue;
  ({
  returntrue;
  }
  )
-/
#guard_msgs in
#eval IO.println TrivialPgm.format.render

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
#eval Strata.C_Simp.TransM.run (Strata.C_Simp.translateProgram (TrivialPgm.commands))

/--
info: [Strata.Boogie] Type checking succeeded.


VCs:
Label: post
Assumptions:


Proof Obligation:
#true

Wrote problem to vcs/post.smt2.
---
info:
Obligation: post
Result: verified
-/
#guard_msgs in
#eval Strata.C_Simp.verify "cvc5" TrivialPgm
