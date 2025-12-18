/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Boogie.Verifier

---------------------------------------------------------------------
namespace Strata

private def typeDeclPgm1 : Program :=
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
#eval TransM.run Inhabited.default (translateProgram typeDeclPgm1) |>.snd

/--
info: [Strata.Boogie] Type checking succeeded.


VCs:
Label: f_test
Assumptions:


Proof Obligation:
#true

---
info:
Obligation: f_test
Result: verified
-/
#guard_msgs in
#eval verify "cvc5" typeDeclPgm1

--------------------------------------------------------------------

/--
error: Expression has type Foo bool int when Foo bool bool expected.
-/
#guard_msgs in
def typeDeclPgm2 :=
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

def typeDeclPgm3 : Program :=
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
#eval TransM.run Inhabited.default (translateProgram typeDeclPgm3) |>.snd

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
#eval verify "cvc5" typeDeclPgm3


--------------------------------------------------------------------

def typeDeclPgm4 :=
#strata
program Boogie;
type int := bool;
#end

/--
error: [Strata.Boogie] Type checking error: This type declaration's name is reserved!
int := bool
KnownTypes' names:
[arrow, TriggerGroup, real, string, bitvec, Triggers, int, bool, Map, regex]
-/
#guard_msgs in
#eval verify "cvc5" typeDeclPgm4

--------------------------------------------------------------------
