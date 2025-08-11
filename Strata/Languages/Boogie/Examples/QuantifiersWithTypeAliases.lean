/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Boogie.Verifier

---------------------------------------------------------------------
namespace Strata

def QuantTypeAliases :=
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

#guard TransM.run (translateProgram (QuantTypeAliases.commands)) |>.snd |>.isEmpty

/--
info: type Boogie.Boundedness.Infinite Ref []
type Boogie.Boundedness.Infinite Field []
type Struct := (Map Field int)
type Heap := (Map Ref Struct)
axiom TODO: (∀ (∀ (∀ (∀ (((~Bool.Implies : (arrow bool (arrow bool bool))) (~Bool.Not (%2 == %1))) ((((~select : (arrow (Map Field int) (arrow Field int))) %3) %2) == (((~select : (arrow (Map Field int) (arrow Field int))) ((((~update : (arrow (Map Field int) (arrow Field (arrow int (Map Field int))))) %3) %1) %0)) %2)))))));
axiom TODO: (∀ (∀ (∀ ((((~select : (arrow (Map Field int) (arrow Field int))) ((((~update : (arrow (Map Field int) (arrow Field (arrow int (Map Field int))))) %2) %1) %0)) %1) == %0))));
axiom TODO: (∀ (∀ (∀ (∀ (((~Bool.Implies : (arrow bool (arrow bool bool))) (~Bool.Not (%2 == %1))) ((((~select : (arrow (Map Ref Struct) (arrow Ref Struct))) %3) %2) == (((~select : (arrow (Map Ref Struct) (arrow Ref Struct))) ((((~update : (arrow (Map Ref Struct) (arrow Ref (arrow Struct (Map Ref Struct))))) %3) %1) %0)) %2)))))));
axiom TODO: (∀ (∀ (∀ ((((~select : (arrow (Map Ref Struct) (arrow Ref Struct))) ((((~update : (arrow (Map Ref Struct) (arrow Ref (arrow Struct (Map Ref Struct))))) %2) %1) %0)) %1) == %0))));
(procedure test :  ((h : Heap) (ref : Ref) (field : Field)) → ())
modifies: []
preconditions: ⏎
postconditions: ⏎
body: init (newH : Heap) := ((((~update : (arrow (Map Ref Struct) (arrow Ref (arrow Struct (Map Ref Struct))))) h) ref) ((((~update : (arrow (Map Field int) (arrow Field (arrow int (Map Field int))))) (((~select : (arrow (Map Ref Struct) (arrow Ref Struct))) h) ref)) field) (((~Int.Add : (arrow int (arrow int int))) (((~select : (arrow (Map Field int) (arrow Field int))) (((~select : (arrow (Map Ref Struct) (arrow Ref Struct))) h) ref)) field)) (#1 : int))))
assert [assert: ((((~select : (arrow (Map Field int) (arrow Field int))) (((~select : (arrow (Map Ref Struct) (arrow Ref Struct))) newH) ref)) field) == (((~Int.Add : (arrow int (arrow int int))) (((~select : (arrow (Map Field int) (arrow Field int))) (((~select : (arrow (Map Ref Struct) (arrow Ref Struct))) h) ref)) field)) (#1 : int)))] ((((~select : (arrow (Map Field int) (arrow Field int))) (((~select : (arrow (Map Ref Struct) (arrow Ref Struct))) newH) ref)) field) == (((~Int.Add : (arrow int (arrow int int))) (((~select : (arrow (Map Field int) (arrow Field int))) (((~select : (arrow (Map Ref Struct) (arrow Ref Struct))) h) ref)) field)) (#1 : int)))

Errors: #[]
-/
#guard_msgs in
#eval TransM.run (translateProgram (QuantTypeAliases.commands))

/-
FIXME.  The code below triggers a unification error due to
lack of alias support (see PR #39).

/--
info: [Strata.Boogie] Type checking succeeded.


VCs:
Label: assert: (((~select ((~select newH) ref)) field) == ((~Int.Add ((~select ((~select h) ref)) field)) (#1 : int)))
Assumptions:
(TODO, (∀ (∀ (∀ (((~select (((~update %2) %1) %0)) %1) == %0)))))
(TODO, (∀ (∀ (∀ (∀ ((~Bool.Implies (~Bool.Not (%2 == %1))) (((~select %3) %2) == ((~select (((~update %3) %1) %0)) %2))))))))
(TODO, (∀ (∀ (∀ (((~select (((~update %2) %1) %0)) %1) == %0)))))
(TODO, (∀ (∀ (∀ (∀ ((~Bool.Implies (~Bool.Not (%2 == %1))) (((~select %3) %2) == ((~select (((~update %3) %1) %0)) %2))))))))
Proof Obligation:
(((~select ((~select (((~update $__h0) $__ref1) (((~update ((~select $__h0) $__ref1)) $__field2) ((~Int.Add ((~select ((~select $__h0) $__ref1)) $__field2)) #1)))) $__ref1)) $__field2) == ((~Int.Add ((~select ((~select $__h0) $__ref1)) $__field2)) #1))

Wrote problem to vcs/assert: (((~select ((~select newH) ref)) field) == ((~Int.Add ((~select ((~select h) ref)) field)) (#1 : int))).smt2.
---
info:
Obligation: assert: (((~select ((~select newH) ref)) field) == ((~Int.Add ((~select ((~select h) ref)) field)) (#1 : int)))
Result: verified
-/
#guard_msgs in
#eval verify "cvc5" QuantTypeAliases
-/
