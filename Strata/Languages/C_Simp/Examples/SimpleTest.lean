/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.C_Simp.C_Simp
import Strata.Languages.C_Simp.Verify

def SimpleTestEnv :=
#strata
program C_Simp;

procedure simpleTest (x: int, y: int) -> int
  @pre y > #0
  @post true
{
  var z : int;
  z := x + y;
  @assert [test_assert] z > x;
  if (z > #10) then {
    z := z - #1;
  } else {
    z := z + #1;
  }
  @assume [test_assume] z > #0;
  return #0;
}

#end

/--
info: proceduresimpleTest(x:int, y:int)->int@pre(y)>(#(0))@posttrue({
  varz:int;
  (z):=(x)+(y);
  @assert[test_assert](z)>(x);
  if((z)>(#(10)))then{
  (z):=(z)-(#(1));
  }
  (else({
  (z):=(z)+(#(1));
  }
  ))@assume[test_assume](z)>(#(0));
  return#(0);
  }
  )
-/
#guard_msgs in
#eval IO.println SimpleTestEnv.format.render


/--
info: function simpleTest {
  pre: ((~Int.Gt y) #0)
  post: #true
  body:
init (z : int) := init_z
z := ((~Int.Add x) y)
assert [test_assert] ((~Int.Gt z) x)
if ((~Int.Gt z) #10) then {z := ((~Int.Sub z) #1)}
else{z := ((~Int.Add z) #1)}
assume [test_assume] ((~Int.Gt z) #0)
return := #0
}
Errors: #[]
-/
#guard_msgs in
open Strata.C_Simp in
#eval TransM.run (translateProgram (SimpleTestEnv.commands))

/--
info: [Strata.Boogie] Type checking succeeded.


Obligation post proved via evaluation!


VCs:
Label: test_assert
Assumptions:
(pre, ((~Int.Gt $__y1) #0))
Proof Obligation:
((~Int.Gt ((~Int.Add $__x0) $__y1)) $__x0)

Label: test_assert
Assumptions:
(pre, ((~Int.Gt $__y1) #0))
Proof Obligation:
((~Int.Gt ((~Int.Add $__x0) $__y1)) $__x0)

Wrote problem to vcs/test_assert.smt2.
Wrote problem to vcs/test_assert.smt2.
---
info:
Obligation: test_assert
Result: verified

Obligation: test_assert
Result: verified
-/
#guard_msgs in
#eval Strata.C_Simp.verify "cvc5" SimpleTestEnv
