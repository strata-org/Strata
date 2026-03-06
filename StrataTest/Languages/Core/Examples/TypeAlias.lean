/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Core.Verifier

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
program Core;
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
program Core;
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
#eval TransM.run Inhabited.default (translateProgram goodTypeAlias) |>.snd

/--
info: type Foo (a0 : Type, a1 : Type);
type FooAlias (a : Type) := Foo int bool;
type FooAlias2 (a : Type) := FooAlias (FooAlias bool);
function fooVal () : FooAlias2 (Foo int int);
function fooConst1 () : Foo int bool;
function fooConst2 () : Foo int bool;
procedure P () returns ()
{
  assume [fooConst1_value]: fooConst1 == fooVal;
  assume [fooConst2_value]: fooConst2 == fooVal;
  assert [fooAssertion]: fooConst1 == fooConst2;
  };
-/
#guard_msgs in
#eval TransM.run Inhabited.default (translateProgram goodTypeAlias) |>.fst

/--
info: [Strata.Core] Type checking succeeded.


VCs:
Label: fooAssertion
Property: assert
Assumptions:
fooConst1_value: fooConst1 == fooVal
fooConst2_value: fooConst2 == fooVal
Obligation:
fooConst1 == fooConst2

---
info:
Obligation: fooAssertion
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval verify goodTypeAlias

--------------------------------------------------------------------

def funcAndTypeAliasesPgm : Program :=
#strata
program Core;

type MapInt := Map int int;

function MapInt_get (d : MapInt, k : int) : int;
function MapGetEq (d: MapInt, k: int, v : int) : bool {
  MapInt_get (d, k) == v
}

procedure test () returns () {
  var d : MapInt, k : int, v : int, b : bool;
  b := MapGetEq(d, k, v);
  assume (v == 0);
  assert (b == MapGetEq(d, k, 0));
};
#end

/--
info: [Strata.Core] Type checking succeeded.


VCs:
Label: assert_0
Property: assert
Assumptions:
assume_0: $__v2 == 0
Obligation:
MapGetEq($__d0, $__k1, $__v2) == MapGetEq($__d0, $__k1, 0)

---
info:
Obligation: assert_0
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval verify funcAndTypeAliasesPgm

--------------------------------------------------------------------
