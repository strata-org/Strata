/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

meta import Strata.Languages.Core
import StrataDDM.Integration.Lean.HashCommands

meta section
open StrataDDM (Program)
---------------------------------------------------------------------
namespace Strata

def badTypeAlias : Program :=
#strata
program Core;
type Foo (a : Type, b : Type);
type FooAlias (a : Type) := Foo a a;

const fooVal : FooAlias bool;
const fooConst1 : Foo int bool;
const fooConst2 : Foo int bool;

procedure P () {
  assume [fooConst1_value]: (fooConst1 == fooVal);
  assume [fooConst2_value]: (fooConst2 == fooVal);
  assert [fooAssertion]: (fooConst1 == fooConst2);
};
#end

-- `FooAlias bool` = `Foo bool bool` does not unify with `Foo int bool`.
/--
error: ❌ Type checking error.
Impossible to unify (Foo int bool) with (Foo bool bool).
First mismatch: int with bool.
-/
#guard_msgs in
#eval Core.verify badTypeAlias (options := .quiet)

--------------------------------------------------------------------

def goodTypeAlias : Program :=
#strata
program Core;
type Foo (a : Type, b : Type);
type FooAlias (a : Type) := Foo a bool;
type FooAlias2 (a : Type) := FooAlias (FooAlias a);

const fooVal : FooAlias2 int;
const fooConst1 : Foo (Foo int bool) bool;
const fooConst2 : Foo (Foo int bool) bool;

procedure P () {
  assume [fooConst1_value]: (fooConst1 == fooVal);
  assume [fooConst2_value]: (fooConst2 == fooVal);
  assert [fooAssertion]: (fooConst1 == fooConst2);
};
#end

/--
info: #[]
-/
#guard_msgs in
#eval TransM.run Inhabited.default (translateProgram goodTypeAlias) |>.snd

/--
info: program Core;

type Foo (a : Type, b : Type);
type FooAlias (a : Type) := Foo a bool;
type FooAlias2 (a : Type) := FooAlias (FooAlias a);
function fooVal () : FooAlias2 int;
function fooConst1 () : Foo (Foo int bool) bool;
function fooConst2 () : Foo (Foo int bool) bool;
procedure P ()
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
#eval Core.verify goodTypeAlias

--------------------------------------------------------------------

def funcAndTypeAliasesPgm : Program :=
#strata
program Core;

type MapInt := Map int int;

function MapInt_get (d : MapInt, k : int) : int;
function MapGetEq (d: MapInt, k: int, v : int) : bool {
  MapInt_get (d, k) == v
}

procedure test () {
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
assume_0: v@1 == 0
Obligation:
MapGetEq(d@1, k@1, v@1) == MapGetEq(d@1, k@1, 0)

---
info:
Obligation: assert_0
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval Core.verify funcAndTypeAliasesPgm

--------------------------------------------------------------------

def unusedParamTypeAlias : Program :=
#strata
program Core;
type Foo (a : Type) := int;
#end

-- `Foo a := int` is rejected: the parameter `a` does not occur in the body.
/--
error: ❌ Type checking error.
Type synonym 'Foo': type argument 'a' is not used in the definition
-/
#guard_msgs in
#eval Core.verify unusedParamTypeAlias (options := .quiet)

end Strata
end
--------------------------------------------------------------------
