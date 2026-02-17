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


/--
info: function simpleTest {
  pre: (~Int.Gt y #0)
  post: #true
  body:
{
  init (z : int) := some init_z
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
(pre, (~Int.Gt $__y1 #0))

Proof Obligation:
(~Int.Gt (~Int.Add $__x0 $__y1) $__x0)

Label: post
Property: assert
Assumptions:
(pre, (~Int.Gt $__y1 #0))
(<label_ite_cond_true: (~Int.Gt z #10)>, (if (~Int.Gt
  (~Int.Add $__x0 $__y1)
  #10) then (~Int.Gt
  (~Int.Add $__x0 $__y1)
  #10) else #true)) (<label_ite_cond_false: !(~Int.Gt z #10)>, (if (if (~Int.Gt
   (~Int.Add $__x0 $__y1)
   #10) then #false else #true) then (if (~Int.Gt
   (~Int.Add $__x0 $__y1)
   #10) then #false else #true) else #true)) (test_assume, (~Int.Gt
 (if (~Int.Gt
   (~Int.Add $__x0 $__y1)
   #10) then (~Int.Sub (~Int.Add $__x0 $__y1) #1) else (~Int.Add (~Int.Add $__x0 $__y1) #1))
 #0))

Proof Obligation:
#true



Obligation test_assert: SMT Solver Invocation Error!

Error: stderr:could not execute external process 'cvc5'
 
Ensure cvc5 is on your PATH or use --solver to specify another SMT solver.
solver stdout: {"caption":"","data":"function simpleTest {\n  pre: (~Int.Gt y #0)\n  post: #true\n  body:\n{\n  init (z : int) := some init_z\n  z := (~Int.Add x y)\n  assert [test_assert] (~Int.Gt z x)\n  if (~Int.Gt z #10) {\n    z := (~Int.Sub z #1)\n  }\n  else {\n    z := (~Int.Add z #1)\n  }\n  assume [test_assume] (~Int.Gt z #0)\n  return := #0\n}\n}\nErrors: #[]","endPos":{"column":5,"line":78},"fileName":"/local/home/mimayere/strata2/StrataTest/Languages/C_Simp/Examples/SimpleTest.lean","isSilent":false,"keepFullRange":false,"kind":"[anonymous]","pos":{"column":0,"line":78},"severity":"information"}
{"caption":"","data":"❌️ Docstring on `#guard_msgs` does not match generated message:\n\n  info: function simpleTest {\n    pre: (~Int.Gt y #0)\n    post: #true\n    body:\n  {\n-   init (z : int) := init_z\n+   init (z : int) := some init_z\n    z := (~Int.Add x y)\n    assert [test_assert] (~Int.Gt z x)\n    if (~Int.Gt z #10) {\n      z := (~Int.Sub z #1)\n    }\n    else {\n      z := (~Int.Add z #1)\n    }\n    assume [test_assume] (~Int.Gt z #0)\n    return := #0\n  }\n  }\n  Errors: #[]\n","endPos":{"column":11,"line":76},"fileName":"/local/home/mimayere/strata2/StrataTest/Languages/C_Simp/Examples/SimpleTest.lean","isSilent":false,"keepFullRange":false,"kind":"[anonymous]","pos":{"column":0,"line":76},"severity":"error"}



Evaluated program:
procedure simpleTest :  ((x : int) (y : int)) → ((return : int))
  modifies: []
  preconditions: (pre, ((~Int.Gt : (arrow int (arrow int bool))) (y : int) #0))
  postconditions: (post, #true)
{
  {
    assume [pre] (~Int.Gt $__y1 #0)
    init (z : int) := some init_z
    z := (~Int.Add $__x0 $__y1)
    assert [test_assert] (~Int.Gt (~Int.Add $__x0 $__y1) $__x0)
    if ((~Int.Gt : (arrow int (arrow int bool)))
       ((~Int.Add : (arrow int (arrow int int))) ($__x0 : int) ($__y1 : int))
       #10) {
      $_then :
      {
        z := (~Int.Sub (~Int.Add $__x0 $__y1) #1)
      }
    }
    else {
      $_else :
      {
        z := (~Int.Add (~Int.Add $__x0 $__y1) #1)
      }
    }
    assume [test_assume] (~Int.Gt
     (if (~Int.Gt
       (~Int.Add $__x0 $__y1)
       #10) then (~Int.Sub (~Int.Add $__x0 $__y1) #1) else (~Int.Add (~Int.Add $__x0 $__y1) #1))
     #0)
    return := #0
    assert [post] #true
  }
}
---
error: stderr:could not execute external process 'cvc5'
 
Ensure cvc5 is on your PATH or use --solver to specify another SMT solver.
solver stdout: {"caption":"","data":"function simpleTest {\n  pre: (~Int.Gt y #0)\n  post: #true\n  body:\n{\n  init (z : int) := some init_z\n  z := (~Int.Add x y)\n  assert [test_assert] (~Int.Gt z x)\n  if (~Int.Gt z #10) {\n    z := (~Int.Sub z #1)\n  }\n  else {\n    z := (~Int.Add z #1)\n  }\n  assume [test_assume] (~Int.Gt z #0)\n  return := #0\n}\n}\nErrors: #[]","endPos":{"column":5,"line":78},"fileName":"/local/home/mimayere/strata2/StrataTest/Languages/C_Simp/Examples/SimpleTest.lean","isSilent":false,"keepFullRange":false,"kind":"[anonymous]","pos":{"column":0,"line":78},"severity":"information"}
{"caption":"","data":"❌️ Docstring on `#guard_msgs` does not match generated message:\n\n  info: function simpleTest {\n    pre: (~Int.Gt y #0)\n    post: #true\n    body:\n  {\n-   init (z : int) := init_z\n+   init (z : int) := some init_z\n    z := (~Int.Add x y)\n    assert [test_assert] (~Int.Gt z x)\n    if (~Int.Gt z #10) {\n      z := (~Int.Sub z #1)\n    }\n    else {\n      z := (~Int.Add z #1)\n    }\n    assume [test_assume] (~Int.Gt z #0)\n    return := #0\n  }\n  }\n  Errors: #[]\n","endPos":{"column":11,"line":76},"fileName":"/local/home/mimayere/strata2/StrataTest/Languages/C_Simp/Examples/SimpleTest.lean","isSilent":false,"keepFullRange":false,"kind":"[anonymous]","pos":{"column":0,"line":76},"severity":"error"}
-/
#guard_msgs in
#eval Strata.C_Simp.verify SimpleTestEnv
