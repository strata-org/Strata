/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Core.Verifier

---------------------------------------------------------------------
namespace Strata

def QuantTypeAliases :=
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

procedure test(h: Heap, ref: Ref, field: Field) returns ()
{
  var newH: Heap := h[ref := h[ref][field := h[ref][field] + 1]];
  assert [assert0]: newH[ref][field] == h[ref][field] + 1;
};

#end

#guard TransM.run Inhabited.default (translateProgram QuantTypeAliases) |>.snd |>.isEmpty

/--
info: type Ref;
type Field;
type Struct := Map Field int;
type Heap := Map Ref Struct;
axiom [axiom_0]: forall __q0 : Struct :: forall __q1 : Field :: forall __q2 : Field :: forall __q3 : int :: !(__q1 == __q2) ==> __q0[__q1] == (__q0[__q2:=__q3])[__q1];
axiom [axiom_1]: forall __q0 : Struct :: forall __q1 : Field :: forall __q2 : int :: (__q0[__q1:=__q2])[__q1] == __q2;
axiom [axiom_2]: forall __q0 : Heap :: forall __q1 : Ref :: forall __q2 : Ref :: forall __q3 : Struct :: !(__q1 == __q2) ==> __q0[__q1] == (__q0[__q2:=__q3])[__q1];
axiom [axiom_3]: forall __q0 : Heap :: forall __q1 : Ref :: forall __q2 : Struct :: (__q0[__q1:=__q2])[__q1] == __q2;
procedure test (h : Heap, ref : Ref, field : Field) returns ()
{
  var newH : Heap := h[ref:=(h[ref])[field:=(h[ref])[field] + 1]];
  assert [assert0]: (newH[ref])[field] == (h[ref])[field] + 1;
  };
-/
#guard_msgs in
#eval TransM.run Inhabited.default (translateProgram QuantTypeAliases) |>.fst


/--
info: [Strata.Core] Type checking succeeded.


VCs:
Label: assert0
Property: assert
Assumptions:
axiom_0: forall __q0 : (Map Field int) :: forall __q1 : Field :: forall __q2 : Field :: forall __q3 : int :: !(__q1 == __q2) ==> __q0[__q1] == (__q0[__q2:=__q3])[__q1]
axiom_1: forall __q0 : (Map Field int) :: forall __q1 : Field :: forall __q2 : int :: (__q0[__q1:=__q2])[__q1] == __q2
axiom_2: forall __q0 : (Map Ref (Map Field int)) :: forall __q1 : Ref :: forall __q2 : Ref :: forall __q3 : (Map Field int) :: !(__q1 == __q2) ==> __q0[__q1] == (__q0[__q2:=__q3])[__q1]
axiom_3: forall __q0 : (Map Ref (Map Field int)) :: forall __q1 : Ref :: forall __q2 : (Map Field int) :: (__q0[__q1:=__q2])[__q1] == __q2
Obligation:
(($__h0[$__ref1:=($__h0[$__ref1])[$__field2:=($__h0[$__ref1])[$__field2] + 1]])[$__ref1])[$__field2] == ($__h0[$__ref1])[$__field2] + 1

---
info:
Obligation: assert0
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval verify QuantTypeAliases
