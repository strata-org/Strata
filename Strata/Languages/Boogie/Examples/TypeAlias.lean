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

/--
error: Expression has type FooAlias Foo int int when Foo bool int expected.
---
error: Expression has type FooAlias Foo int int when Foo bool int expected.
-/
#guard_msgs in
def badTypeAliasEnv : Environment :=
#strata
program Boogie;
type Foo (a : Type, b : Type);
type FooAlias (a : Type) := Foo bool bool;

const fooVal : FooAlias (Foo int int);
const fooConst1 : Foo int bool;
const fooConst2 : Foo int bool;

procedure P () returns () {
  assume [fooConst1_value]: (fooConst1 == fooVal);
  assume [fooConst2_value]: (fooConst2 == fooVal);
  assert [fooAssertion]: (fooConst1 == fooConst2);
};
#end

--------------------------------------------------------------------

def goodTypeAliasEnv : Environment :=
#strata
program Boogie;
type Foo (a : Type, b : Type);
type FooAlias (a : Type) := Foo int bool;
type FooAlias2 (a : Type) := FooAlias (FooAlias bool);

const fooVal : FooAlias2 (Foo int int);
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
#eval TransM.run (translateProgram (goodTypeAliasEnv.commands)) |>.snd

/--
info: type Boogie.Boundedness.Infinite Foo [_, _]
type FooAlias a := (Foo int bool)
type FooAlias2 a := (FooAlias (FooAlias bool))
func fooVal :  () → (FooAlias2 (Foo int int));
func fooConst1 :  () → (Foo int bool);
func fooConst2 :  () → (Foo int bool);
(procedure P :  () → ())
modifies: []
preconditions: ⏎
postconditions: ⏎
body: assume [fooConst1_value] (~fooConst1 == ~fooVal)
assume [fooConst2_value] (~fooConst2 == ~fooVal)
assert [fooAssertion] (~fooConst1 == ~fooConst2)
-/
#guard_msgs in
#eval TransM.run (translateProgram (goodTypeAliasEnv.commands)) |>.fst

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
#eval verify "cvc5" goodTypeAliasEnv

--------------------------------------------------------------------
