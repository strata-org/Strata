/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

meta import Strata.Languages.Core.Core
import StrataDDM.Integration.Lean.HashCommands

meta section
open StrataDDM (Program)

---------------------------------------------------------------------
namespace Strata

def genLabelsPgm : Program :=
#strata
program Core;

type Ref;
type Field;

type Struct := Map Field int;
type Heap := Map Ref Struct;

axiom forall m: Struct, okk: Field, kk: Field, vv: int :: okk != kk ==> m[okk] == m[kk := vv][okk];
axiom forall m: Struct, kk: Field, vv: int :: m[kk := vv][kk] == vv;

axiom forall m: Heap, okk: Ref, kk: Ref, vv: Struct :: okk != kk ==> m[okk] == m[kk := vv][okk];
axiom forall m: Heap, kk: Ref, vv: Struct :: m[kk := vv][kk] == vv;

procedure test(h: Heap, ref: Ref, field: Field)
{
  var newH: Heap := h[ref := h[ref][field := h[ref][field] + 1]];
  assert newH[ref][field] == h[ref][field] + 1;
};

#end

/--
info: program Core;

type Ref;
type Field;
type Struct := Map Field int;
type Heap := Map Ref Struct;
axiom [axiom_0]: forall m : Struct :: forall okk : Field :: forall kk : Field :: forall vv : int :: !(okk == kk) ==> m[okk] == (m[kk:=vv])[okk];
axiom [axiom_1]: forall m : Struct :: forall kk : Field :: forall vv : int :: (m[kk:=vv])[kk] == vv;
axiom [axiom_2]: forall m : Heap :: forall okk : Ref :: forall kk : Ref :: forall vv : Struct :: !(okk == kk) ==> m[okk] == (m[kk:=vv])[okk];
axiom [axiom_3]: forall m : Heap :: forall kk : Ref :: forall vv : Struct :: (m[kk:=vv])[kk] == vv;
procedure test (h : Heap, ref : Ref, field : Field)
{
  var newH : Heap := h[ref:=(h[ref])[field:=(h[ref])[field] + 1]];
  assert [assert_0]: (newH[ref])[field] == (h[ref])[field] + 1;
};
-/
#guard_msgs in
#eval (TransM.run Inhabited.default (translateProgram genLabelsPgm) |>.fst)

/--
info: [Strata.Core] Type checking succeeded.


VCs:
Label: assert_0
Property: assert
Assumptions:
axiom_0: forall m : (Map Field int) :: forall okk : Field :: forall kk : Field :: forall vv : int :: !(okk == kk) ==> m[okk] == (m[kk:=vv])[okk]
axiom_1: forall m : (Map Field int) :: forall kk : Field :: forall vv : int :: (m[kk:=vv])[kk] == vv
axiom_2: forall m : (Map Ref (Map Field int)) :: forall okk : Ref :: forall kk : Ref :: forall vv : (Map Field int) :: !(okk == kk) ==> m[okk] == (m[kk:=vv])[okk]
axiom_3: forall m : (Map Ref (Map Field int)) :: forall kk : Ref :: forall vv : (Map Field int) :: (m[kk:=vv])[kk] == vv
Obligation:
((h@1[ref@1:=(h@1[ref@1])[field@1:=(h@1[ref@1])[field@1] + 1]])[ref@1])[field@1] == (h@1[ref@1])[field@1] + 1

---
info:
Obligation: assert_0
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval Core.verify genLabelsPgm

end Strata

end
