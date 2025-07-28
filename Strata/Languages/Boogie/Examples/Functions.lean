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

def funcEnv : Environment :=
#strata
program Boogie;
const fooConst : int;
inline function fooTest() : int { fooConst }

function barTest1(x : int) : int { x }
inline function barTest2(y : int) : int { y }

procedure fooProc(a : int) returns () {
  assert [barEq]: (barTest1(a) == barTest2(a));
  assert [fooEq]: (fooConst == fooTest);
};

#end

/--
info: [Strata.Boogie] Type checking succeeded.


Obligation fooEq proved via evaluation!


VCs:
Label: barEq
Assumptions:
Proof Obligation:
((~barTest1 $__a0) == $__a0)

Wrote problem to vcs/barEq.smt2.
---
info:
Obligation: barEq
Result: verified
-/
#guard_msgs in
#eval verify "cvc5" funcEnv

---------------------------------------------------------------------
