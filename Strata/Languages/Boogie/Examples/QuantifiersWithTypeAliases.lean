/-
  Copyright Strata Contributors

  Licensed under the Apache License, Version 2.0 (the "License");
  you may not use this file except in compliance with the License.
  You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

  Unless required by applicable law or agreed to in writing, software
  distributed under the License is distributed on an "AS IS" BASIS,
  WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
  See the License for the specific language governing permissions and
  limitations under the License.
-/

import Strata.Languages.Boogie.Verifier

---------------------------------------------------------------------
namespace Strata

def QuantTypeAliases : Environment :=
#strata
open Boogie;

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

#eval TransM.run (translateProgram (QuantTypeAliases.commands)) |>.snd |>.isEmpty

/--
info: type Boogie.Boundedness.Infinite Ref []
type Boogie.Boundedness.Infinite Field []
type Struct := (Map Field int)
type Heap := (Map Ref Struct)
axiom TODO: (∀ (∀ (∀ (∀ ((~Bool.Implies (~Bool.Not (%2 == %1))) (((~select %3) %2) == ((~select (((~update %3) %1) %0)) %2)))))));
axiom TODO: (∀ (∀ (∀ (((~select (((~update %2) %1) %0)) %1) == %0))));
axiom TODO: (∀ (∀ (∀ (∀ ((~Bool.Implies (~Bool.Not (%2 == %1))) (((~select %3) %2) == ((~select (((~update %3) %1) %0)) %2)))))));
axiom TODO: (∀ (∀ (∀ (((~select (((~update %2) %1) %0)) %1) == %0))));
(procedure test :  ((h : Heap) (ref : Ref) (field : Field)) → ())
modifies: []
preconditions: ⏎
postconditions: ⏎
body: init (newH : Heap) := (((~update h) ref) (((~update ((~select h) ref)) field) ((~Int.Add ((~select ((~select h) ref)) field)) (#1 : int))))
assert [assert: (((~select ((~select newH) ref)) field) == ((~Int.Add ((~select ((~select h) ref)) field)) (#1 : int)))] (((~select ((~select newH) ref)) field) == ((~Int.Add ((~select ((~select h) ref)) field)) (#1 : int)))

Errors: #[]
-/
#guard_msgs in
#eval TransM.run (translateProgram (QuantTypeAliases.commands))

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
