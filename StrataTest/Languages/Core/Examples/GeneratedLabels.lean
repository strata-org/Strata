/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Core.Verifier

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

procedure test(h: Heap, ref: Ref, field: Field) returns ()
{
  var newH: Heap := h[ref := h[ref][field := h[ref][field] + 1]];
  assert newH[ref][field] == h[ref][field] + 1;
};

#end

/--
info: type Ref;
type Field;
type Struct := Map Field int;
type Heap := Map Ref Struct;
axiom [axiom_0]: forall x0 : Struct :: forall x1 : Field :: forall x2 : Field :: forall x3 : int :: !(x1 == x2) ==> x0[x1] == (x0[x2:=x3])[x1];
axiom [axiom_1]: forall x0 : Struct :: forall x1 : Field :: forall x2 : int :: (x0[x1:=x2])[x1] == x2;
axiom [axiom_2]: forall x0 : Heap :: forall x1 : Ref :: forall x2 : Ref :: forall x3 : Struct :: !(x1 == x2) ==> x0[x1] == (x0[x2:=x3])[x1];
axiom [axiom_3]: forall x0 : Heap :: forall x1 : Ref :: forall x2 : Struct :: (x0[x1:=x2])[x1] == x2;
procedure test (h : Heap, ref : Ref, field : Field) returns ()
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

(axiom_0, (∀ (∀ (∀ (∀ (~Bool.Implies (~Bool.Not (%2 == %1)) ((~select %3 %2) == (~select (~update %3 %1 %0) %2))))))))
(axiom_1, (∀ (∀ (∀ ((~select
     (~update %2 %1 %0)
     %1) == %0))))) (axiom_2, (∀ (∀ (∀ (∀ (~Bool.Implies
     (~Bool.Not (%2 == %1))
     ((~select
       %3
       %2) == (~select (~update %3 %1 %0) %2)))))))) (axiom_3, (∀ (∀ (∀ ((~select (~update %2 %1 %0) %1) == %0)))))
Proof Obligation:
((~select
  (~select
   (~update
    $__h0
    $__ref1
    (~update (~select $__h0 $__ref1) $__field2 (~Int.Add (~select (~select $__h0 $__ref1) $__field2) #1)))
   $__ref1)
  $__field2) == (~Int.Add (~select (~select $__h0 $__ref1) $__field2) #1))

---
info:
Obligation: assert_0
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval verify genLabelsPgm
