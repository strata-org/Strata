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

/--
info: function min {
  pre: #true
  post: #true
  body:
{
  if (~Int.Lt a b) {
    return := a
  }
  else {
    return := b
  }
}
}
Errors: #[]
-/
#guard_msgs in
open Strata.C_Simp in
#eval TransM.run (translateProgram (MinPgm.commands))

/--
info: [Strata.Core] Type checking succeeded.


VCs:
Label: post
Property: assert
Assumptions:
<label_ite_cond_true: (~Int.Lt a b)>: if $__a0 < $__b1 then ($__a0 < $__b1) else true
<label_ite_cond_false: !(~Int.Lt a b)>: if if $__a0 < $__b1 then false else true then if $__a0 < $__b1 then false else true else true
Obligation:
true

---
info:
Obligation: post
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval Strata.C_Simp.verify MinPgm
