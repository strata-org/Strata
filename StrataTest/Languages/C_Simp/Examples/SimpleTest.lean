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
int procedure simpleTest(x:int, y:int)//@pre y>0;
//@post true;
  ({
  varz:int;
  z=x+y;
  //@assert [test_assert]z>x;
  if(z>10){
  z=z-1;
  }
  (else({
  z=z+1;
  }
  ))//@assume [test_assume]z>0;
  return0;
  }
  )
-/
#guard_msgs in
#eval IO.println SimpleTestEnv


/--
info: function simpleTest {
  pre: (~Int.Gt y #0)
  post: #true
  body:
{
  init (z : int) := init_z
  z := (~Int.Add x y)
  assert [test_assert] (~Int.Gt z x)
  if (~Int.Gt z #10) {
    z := (~Int.Sub z #1)
  }
  else {
    z := (~Int.Add z #1)
  }
  assume [test_assume] (~Int.Gt z #0)
  return := #0
}
}
Errors: #[]
-/
#guard_msgs in
open Strata.C_Simp in
#eval TransM.run (translateProgram (SimpleTestEnv.commands))

/--
info: [Strata.Core] Type checking succeeded.


VCs:
Label: test_assert
Property: assert
Assumptions:
pre: $__y1 > 0
Obligation:
$__x0 + $__y1 > $__x0

Label: post
Property: assert
Assumptions:
pre: $__y1 > 0
<label_ite_cond_true: (~Int.Gt z #10)>: if $__x0 + $__y1 > 10 then ($__x0 + $__y1 > 10) else true
<label_ite_cond_false: !(~Int.Gt z #10)>: if if $__x0 + $__y1 > 10 then false else true then if $__x0 + $__y1 > 10 then false else true else true
test_assume: if $__x0 + $__y1 > 10 then ($__x0 + $__y1 - 1) else ($__x0 + $__y1 + 1) > 0
Obligation:
true

---
info:
Obligation: test_assert
Property: assert
Result: ✅ pass

Obligation: post
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval Strata.C_Simp.verify SimpleTestEnv
