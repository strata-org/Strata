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

#guard TransM.run (translateProgram QuantTypeAliases) |>.snd |>.isEmpty

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
#eval TransM.run (translateProgram QuantTypeAliases)

/-
FIXME.  The code below triggers a unification error due to
lack of alias support (see PR #39).

/--
error: [Strata.Boogie] Type checking error: Cannot unify differently named type constructors (Map Field int) and Struct!
-/
#guard_msgs in
#eval verify "cvc5" QuantTypeAliases
-/
