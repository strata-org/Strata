/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Boogie.Verifier

---------------------------------------------------------------------
namespace Strata

def genLabelsPgm : Program :=
#strata
program Boogie;

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
info: type Boogie.Boundedness.Infinite Ref []
type Boogie.Boundedness.Infinite Field []
type Struct := (Map Field int)
type Heap := (Map Ref Struct)
axiom axiom_0: (∀ (∀ (∀ (∀ (((~Bool.Implies : (arrow bool (arrow bool bool))) (~Bool.Not (%2 == %1))) ((((~select : (arrow (Map Field int) (arrow Field int))) %3) %2) == (((~select : (arrow (Map Field int) (arrow Field int))) ((((~update : (arrow (Map Field int) (arrow Field (arrow int (Map Field int))))) %3) %1) %0)) %2)))))));
axiom axiom_1: (∀ (∀ (∀ ((((~select : (arrow (Map Field int) (arrow Field int))) ((((~update : (arrow (Map Field int) (arrow Field (arrow int (Map Field int))))) %2) %1) %0)) %1) == %0))));
axiom axiom_2: (∀ (∀ (∀ (∀ (((~Bool.Implies : (arrow bool (arrow bool bool))) (~Bool.Not (%2 == %1))) ((((~select : (arrow (Map Ref Struct) (arrow Ref Struct))) %3) %2) == (((~select : (arrow (Map Ref Struct) (arrow Ref Struct))) ((((~update : (arrow (Map Ref Struct) (arrow Ref (arrow Struct (Map Ref Struct))))) %3) %1) %0)) %2)))))));
axiom axiom_3: (∀ (∀ (∀ ((((~select : (arrow (Map Ref Struct) (arrow Ref Struct))) ((((~update : (arrow (Map Ref Struct) (arrow Ref (arrow Struct (Map Ref Struct))))) %2) %1) %0)) %1) == %0))));
(procedure test :  ((h : Heap) (ref : Ref) (field : Field)) → ())
modifies: []
preconditions: ⏎
postconditions: ⏎
body: init (newH : Heap) := ((((~update : (arrow (Map Ref Struct) (arrow Ref (arrow Struct (Map Ref Struct))))) h) ref) ((((~update : (arrow (Map Field int) (arrow Field (arrow int (Map Field int))))) (((~select : (arrow (Map Ref Struct) (arrow Ref Struct))) h) ref)) field) (((~Int.Add : (arrow int (arrow int int))) (((~select : (arrow (Map Field int) (arrow Field int))) (((~select : (arrow (Map Ref Struct) (arrow Ref Struct))) h) ref)) field)) (#1 : int))))
assert [assert_0] ((((~select : (arrow (Map Field int) (arrow Field int))) (((~select : (arrow (Map Ref Struct) (arrow Ref Struct))) newH) ref)) field) == (((~Int.Add : (arrow int (arrow int int))) (((~select : (arrow (Map Field int) (arrow Field int))) (((~select : (arrow (Map Ref Struct) (arrow Ref Struct))) h) ref)) field)) (#1 : int)))
-/
#guard_msgs in
#eval (TransM.run (translateProgram genLabelsPgm) |>.fst)

/--
info: [Strata.Boogie] Type checking succeeded.


VCs:
Label: assert_0
Assumptions:
(axiom_3, (∀ (∀ (∀ (((~select (((~update %2) %1) %0)) %1) == %0)))))
(axiom_2, (∀ (∀ (∀ (∀ ((~Bool.Implies (~Bool.Not (%2 == %1))) (((~select %3) %2) == ((~select (((~update %3) %1) %0)) %2))))))))
(axiom_1, (∀ (∀ (∀ (((~select (((~update %2) %1) %0)) %1) == %0)))))
(axiom_0, (∀ (∀ (∀ (∀ ((~Bool.Implies (~Bool.Not (%2 == %1))) (((~select %3) %2) == ((~select (((~update %3) %1) %0)) %2))))))))
Proof Obligation:
(((~select ((~select (((~update $__h0) $__ref1) (((~update ((~select $__h0) $__ref1)) $__field2) ((~Int.Add ((~select ((~select $__h0) $__ref1)) $__field2)) #1)))) $__ref1)) $__field2) == ((~Int.Add ((~select ((~select $__h0) $__ref1)) $__field2)) #1))

Wrote problem to vcs/assert_0.smt2.
---
info:
Obligation: assert_0
Result: verified
-/
#guard_msgs in
#eval verify "cvc5" genLabelsPgm
