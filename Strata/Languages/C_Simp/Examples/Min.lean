/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.C_Simp.C_Simp
import Strata.Languages.C_Simp.Verify

def MinPgm :=
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
info: program C_Simp;
proceduremin(a:int, b:int)->int@pretrue@posttrue({
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
#eval IO.println MinPgm.format.render

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
#eval TransM.run (translateProgram (MinPgm.commands))

/--
info: [Strata.Boogie] Type checking succeeded.


VCs:
Label: post
Assumptions:
(<label_ite_cond_true: ((~Int.Lt a) b)>, (if ((~Int.Lt $__a0) $__b1) then ((~Int.Lt $__a0) $__b1) else #true))
(<label_ite_cond_false: !((~Int.Lt a) b)>, (if (if ((~Int.Lt $__a0) $__b1) then #false else #true) then (if ((~Int.Lt $__a0) $__b1) then #false else #true) else #true))
Proof Obligation:
#true

Wrote problem to vcs/post.smt2.
---
info:
Obligation: post
Result: verified
-/
#guard_msgs in
#eval Strata.C_Simp.verify "cvc5" MinPgm
