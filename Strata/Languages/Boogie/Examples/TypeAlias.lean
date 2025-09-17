/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Boogie.Verifier

---------------------------------------------------------------------
namespace Strata

/--
error: Expression has type FooAlias (Foo int int) when Foo bool int expected.
---
error: Expression has type FooAlias (Foo int int) when Foo bool int expected.
-/
#guard_msgs in
def badTypeAlias : Program :=
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

def goodTypeAlias : Program :=
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
#eval TransM.run (translateProgram goodTypeAlias) |>.snd

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
body: assume [fooConst1_value] ((~fooConst1 : (Foo int bool)) == (~fooVal : (FooAlias2 (Foo int int))))
assume [fooConst2_value] ((~fooConst2 : (Foo int bool)) == (~fooVal : (FooAlias2 (Foo int int))))
assert [fooAssertion] ((~fooConst1 : (Foo int bool)) == (~fooConst2 : (Foo int bool)))
-/
#guard_msgs in
#eval TransM.run (translateProgram goodTypeAlias) |>.fst

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
#eval verify "cvc5" goodTypeAlias

--------------------------------------------------------------------
