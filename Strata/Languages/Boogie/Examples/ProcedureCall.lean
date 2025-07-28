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

import Strata.Languages.Boogie.Verifier

---------------------------------------------------------------------
namespace Strata

def globalCounterEnv : Environment :=
#strata
program Boogie;

var counter : int;

inline function Add(x : int, y : int) : int { x + y }

procedure Inc(a : int) returns (ret : int)
spec {
  modifies counter;
  requires [a_positive]:      (a > 0);
  ensures  [new_g_value]:     (counter == old(counter) + a);
  ensures  [old_g_property]:  (ret - a == old(counter));
}
{
  counter := Add(counter, a);
  ret := counter;
};

procedure P() returns (b : int)
spec {
  modifies counter;
  ensures [return_value_lemma]: (b == old(counter) + 16);
}
{
  call b := Inc(8);
  call b := Inc(8);
};

procedure Q1() returns () {
  assert true;
};

procedure Q2() returns () {
  call Q1();
};
#end

/--
info: [Strata.Boogie] Type checking succeeded.


Obligation new_g_value proved via evaluation!


Obligation <Origin:Inc_Requires>a_positive proved via evaluation!


Obligation <Origin:Inc_Requires>a_positive proved via evaluation!


Obligation assert: (#true : bool) proved via evaluation!


VCs:
Label: old_g_property
Assumptions:
(a_positive, ((~Int.Gt $__a1) #0))
Proof Obligation:
(((~Int.Sub ((~Int.Add $__counter0) $__a1)) $__a1) == $__counter0)

Label: return_value_lemma
Assumptions:
(<Origin:Inc_Ensures>new_g_value, ($__counter6 == ((~Int.Add $__counter3) #8)))
(<Origin:Inc_Ensures>old_g_property, (((~Int.Sub $__b5) #8) == $__counter3))
(<Origin:Inc_Ensures>new_g_value, ($__counter8 == ((~Int.Add $__counter6) #8)))
(<Origin:Inc_Ensures>old_g_property, (((~Int.Sub $__b7) #8) == $__counter6))
Proof Obligation:
($__b7 == ((~Int.Add $__counter3) #16))

Wrote problem to vcs/old_g_property.smt2.
Wrote problem to vcs/return_value_lemma.smt2.
---
info:
Obligation: old_g_property
Result: verified

Obligation: return_value_lemma
Result: verified
-/
#guard_msgs in
#eval verify "cvc5" globalCounterEnv

---------------------------------------------------------------------

/-
-- DDM AST
#eval globalCounterEnv.commands

-- Translation from DDM AST to Boogie/Strata AST
#eval TransM.run (translateProgram (globalCounterEnv.commands))
-/

---------------------------------------------------------------------
