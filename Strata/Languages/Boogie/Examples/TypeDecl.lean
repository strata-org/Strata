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

def typeDeclEnv1 : Environment :=
#strata
program Boogie;
type Foo (a : Type, b : Type);

const fooConst : Foo int bool;

procedure P () returns () {
  var f : Foo int bool;
  f := fooConst;
  assert [f_test]: (f == fooConst);
};
#end

/-- info: #[] -/
#guard_msgs in
#eval TransM.run (translateProgram (typeDeclEnv1.commands)) |>.snd

/--
info: [Strata.Boogie] Type checking succeeded.


Obligation f_test proved via evaluation!


VCs:

---
info:
-/
#guard_msgs in
#eval verify "cvc5" typeDeclEnv1

--------------------------------------------------------------------

/--
error: Expression has type Foo bool int when Foo bool bool expected.
-/
#guard_msgs in
def typeDeclEnv2 : Environment :=
#strata
program Boogie;

type Foo (a : Type, b : Type);

procedure P () returns () {
  var f1 : Foo bool bool;
  var f2 : Foo int bool;
  assert [f_test]: (f1 == f2);
};
#end

--------------------------------------------------------------------

def typeDeclEnv3 : Environment :=
#strata
program Boogie;
type Foo (a : Type, b : Type);

const fooVal : Foo int bool;
const fooConst1 : Foo int bool;
const fooConst2 : Foo int bool;

procedure P () returns () {
  assume [fooConst1_value]: (fooConst1 == fooVal);
  assume [fooConst2_value]: (fooConst2 == fooVal);
  assert [fooAssertion]: (fooConst1 == fooConst2);
};
#end

/-- info: #[] -/
#guard_msgs in
#eval TransM.run (translateProgram (typeDeclEnv3.commands)) |>.snd

/--
info: [Strata.Boogie] Type checking succeeded.


VCs:
Label: fooAssertion
Assumptions:
(fooConst1_value, (~fooConst1 == ~fooVal))
(fooConst2_value, (~fooConst2 == ~fooVal))
Proof Obligation:
(~fooConst1 == ~fooConst2)

Wrote problem to vcs/fooAssertion.smt2.
---
info:
Obligation: fooAssertion
Result: verified
-/
#guard_msgs in
#eval verify "cvc5" typeDeclEnv3


--------------------------------------------------------------------
