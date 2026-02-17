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
info: type Core.Boundedness.Infinite Ref []
type Core.Boundedness.Infinite Field []
type Struct := (Map Field int)
type Heap := (Map Ref Struct)
axiom axiom_0: (∀ (∀ (∀ (∀ ((~Bool.Implies : (arrow bool (arrow bool bool)))
     ((~Bool.Not : (arrow bool bool)) (%2 == %1))
     (((~select : (arrow (Map Field int) (arrow Field int)))
       %3
       %2) == ((~select : (arrow (Map Field int) (arrow Field int)))
       ((~update : (arrow (Map Field int) (arrow Field (arrow int (Map Field int))))) %3 %1 %0)
       %2)))))));
axiom axiom_1: (∀ (∀ (∀ (((~select : (arrow (Map Field int) (arrow Field int)))
     ((~update : (arrow (Map Field int) (arrow Field (arrow int (Map Field int))))) %2 %1 %0)
     %1) == %0))));
axiom axiom_2: (∀ (∀ (∀ (∀ ((~Bool.Implies : (arrow bool (arrow bool bool)))
     ((~Bool.Not : (arrow bool bool)) (%2 == %1))
     (((~select : (arrow (Map Ref Struct) (arrow Ref Struct)))
       %3
       %2) == ((~select : (arrow (Map Ref Struct) (arrow Ref Struct)))
       ((~update : (arrow (Map Ref Struct) (arrow Ref (arrow Struct (Map Ref Struct))))) %3 %1 %0)
       %2)))))));
axiom axiom_3: (∀ (∀ (∀ (((~select : (arrow (Map Ref Struct) (arrow Ref Struct)))
     ((~update : (arrow (Map Ref Struct) (arrow Ref (arrow Struct (Map Ref Struct))))) %2 %1 %0)
     %1) == %0))));
procedure test :  ((h : Heap) (ref : Ref) (field : Field)) → ()
  modifies: []
  preconditions: 
  postconditions: 
{
  {
    init (newH : Heap) := some ((~update : (arrow (Map Ref Struct) (arrow Ref (arrow Struct (Map Ref Struct)))))
     (h : Heap)
     (ref : Ref)
     ((~update : (arrow (Map Field int) (arrow Field (arrow int (Map Field int)))))
      ((~select : (arrow (Map Ref Struct) (arrow Ref Struct))) (h : Heap) (ref : Ref))
      (field : Field)
      ((~Int.Add : (arrow int (arrow int int)))
       ((~select : (arrow (Map Field int) (arrow Field int)))
        ((~select : (arrow (Map Ref Struct) (arrow Ref Struct))) (h : Heap) (ref : Ref))
        (field : Field))
       #1)))
    assert [assert0] (((~select : (arrow (Map Field int) (arrow Field int)))
      ((~select : (arrow (Map Ref Struct) (arrow Ref Struct))) (newH : Heap) (ref : Ref))
      (field : Field)) == ((~Int.Add : (arrow int (arrow int int)))
      ((~select : (arrow (Map Field int) (arrow Field int)))
       ((~select : (arrow (Map Ref Struct) (arrow Ref Struct))) (h : Heap) (ref : Ref))
       (field : Field))
      #1))
  }
}
Errors: #[]
-/
#guard_msgs in
#eval TransM.run Inhabited.default (translateProgram QuantTypeAliases)


/--
info: [Strata.Core] Type checking succeeded.


VCs:
Label: assert0
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



Obligation assert0: SMT Solver Invocation Error!

Error: stderr:could not execute external process 'cvc5'
 
Ensure cvc5 is on your PATH or use --solver to specify another SMT solver.
solver stdout: : (∀ (∀ (∀ (((~select : (arrow (Map Ref Struct) (arrow Ref Struct)))\n       ((~update : (arrow (Map Ref Struct) (arrow Ref (arrow Struct (Map Ref Struct))))) %2 %1 %0)\n       %1) == %0))));\n  procedure test :  ((h : Heap) (ref : Ref) (field : Field)) → ()\n    modifies: []\n    preconditions: \n    postconditions: \n  {\n    {\n-     init (newH : Heap) := ((~update : (arrow (Map Ref Struct) (arrow Ref (arrow Struct (Map Ref Struct)))))\n+     init (newH : Heap) := some ((~update : (arrow (Map Ref Struct) (arrow Ref (arrow Struct (Map Ref Struct)))))\n       (h : Heap)\n       (ref : Ref)\n       ((~update : (arrow (Map Field int) (arrow Field (arrow int (Map Field int)))))\n        ((~select : (arrow (Map Ref Struct) (arrow Ref Struct))) (h : Heap) (ref : Ref))\n        (field : Field)\n        ((~Int.Add : (arrow int (arrow int int)))\n         ((~select : (arrow (Map Field int) (arrow Field int)))\n          ((~select : (arrow (Map Ref Struct) (arrow Ref Struct))) (h : Heap) (ref : Ref))\n          (field : Field))\n         #1)))\n      assert [assert0] (((~select : (arrow (Map Field int) (arrow Field int)))\n        ((~select : (arrow (Map Ref Struct) (arrow Ref Struct))) (newH : Heap) (ref : Ref))\n        (field : Field)) == ((~Int.Add : (arrow int (arrow int int)))\n        ((~select : (arrow (Map Field int) (arrow Field int)))\n         ((~select : (arrow (Map Ref Struct) (arrow Ref Struct))) (h : Heap) (ref : Ref))\n         (field : Field))\n        #1))\n    }\n  }\n  Errors: #[]\n","endPos":{"column":11,"line":91},"fileName":"/local/home/mimayere/strata2/StrataTest/Languages/Core/Examples/QuantifiersWithTypeAliases.lean","isSilent":false,"keepFullRange":false,"kind":"[anonymous]","pos":{"column":0,"line":91},"severity":"error"}



Evaluated program:
type Core.Boundedness.Infinite Ref []
type Core.Boundedness.Infinite Field []
type Struct := (Map Field int)
type Heap := (Map Ref Struct)
axiom axiom_0: (∀ (∀ (∀ (∀ ((~Bool.Implies : (arrow bool (arrow bool bool)))
     ((~Bool.Not : (arrow bool bool)) (%2 == %1))
     (((~select : (arrow (Map Field int) (arrow Field int)))
       %3
       %2) == ((~select : (arrow (Map Field int) (arrow Field int)))
       ((~update : (arrow (Map Field int) (arrow Field (arrow int (Map Field int))))) %3 %1 %0)
       %2)))))));
axiom axiom_1: (∀ (∀ (∀ (((~select : (arrow (Map Field int) (arrow Field int)))
     ((~update : (arrow (Map Field int) (arrow Field (arrow int (Map Field int))))) %2 %1 %0)
     %1) == %0))));
axiom axiom_2: (∀ (∀ (∀ (∀ ((~Bool.Implies : (arrow bool (arrow bool bool)))
     ((~Bool.Not : (arrow bool bool)) (%2 == %1))
     (((~select : (arrow (Map Ref (Map Field int)) (arrow Ref (Map Field int))))
       %3
       %2) == ((~select : (arrow (Map Ref (Map Field int)) (arrow Ref (Map Field int))))
       ((~update : (arrow (Map Ref (Map Field int)) (arrow Ref (arrow (Map Field int) (Map Ref (Map Field int))))))
        %3
        %1
        %0)
       %2)))))));
axiom axiom_3: (∀ (∀ (∀ (((~select : (arrow (Map Ref (Map Field int)) (arrow Ref (Map Field int))))
     ((~update : (arrow (Map Ref (Map Field int)) (arrow Ref (arrow (Map Field int) (Map Ref (Map Field int))))))
      %2
      %1
      %0)
     %1) == %0))));
procedure test :  ((h : (Map Ref (Map Field int))) (ref : Ref) (field : Field)) → ()
  modifies: []
  preconditions: 
  postconditions: 
{
  {
    init (newH : (Map Ref (Map Field int))) := some (~update
     $__h0
     $__ref1
     (~update (~select $__h0 $__ref1) $__field2 (~Int.Add (~select (~select $__h0 $__ref1) $__field2) #1)))
    assert [assert0] ((~select
      (~select
       (~update
        $__h0
        $__ref1
        (~update (~select $__h0 $__ref1) $__field2 (~Int.Add (~select (~select $__h0 $__ref1) $__field2) #1)))
       $__ref1)
      $__field2) == (~Int.Add (~select (~select $__h0 $__ref1) $__field2) #1))
  }
}
---
error: stderr:could not execute external process 'cvc5'
 
Ensure cvc5 is on your PATH or use --solver to specify another SMT solver.
solver stdout: : (∀ (∀ (∀ (((~select : (arrow (Map Ref Struct) (arrow Ref Struct)))\n       ((~update : (arrow (Map Ref Struct) (arrow Ref (arrow Struct (Map Ref Struct))))) %2 %1 %0)\n       %1) == %0))));\n  procedure test :  ((h : Heap) (ref : Ref) (field : Field)) → ()\n    modifies: []\n    preconditions: \n    postconditions: \n  {\n    {\n-     init (newH : Heap) := ((~update : (arrow (Map Ref Struct) (arrow Ref (arrow Struct (Map Ref Struct)))))\n+     init (newH : Heap) := some ((~update : (arrow (Map Ref Struct) (arrow Ref (arrow Struct (Map Ref Struct)))))\n       (h : Heap)\n       (ref : Ref)\n       ((~update : (arrow (Map Field int) (arrow Field (arrow int (Map Field int)))))\n        ((~select : (arrow (Map Ref Struct) (arrow Ref Struct))) (h : Heap) (ref : Ref))\n        (field : Field)\n        ((~Int.Add : (arrow int (arrow int int)))\n         ((~select : (arrow (Map Field int) (arrow Field int)))\n          ((~select : (arrow (Map Ref Struct) (arrow Ref Struct))) (h : Heap) (ref : Ref))\n          (field : Field))\n         #1)))\n      assert [assert0] (((~select : (arrow (Map Field int) (arrow Field int)))\n        ((~select : (arrow (Map Ref Struct) (arrow Ref Struct))) (newH : Heap) (ref : Ref))\n        (field : Field)) == ((~Int.Add : (arrow int (arrow int int)))\n        ((~select : (arrow (Map Field int) (arrow Field int)))\n         ((~select : (arrow (Map Ref Struct) (arrow Ref Struct))) (h : Heap) (ref : Ref))\n         (field : Field))\n        #1))\n    }\n  }\n  Errors: #[]\n","endPos":{"column":11,"line":91},"fileName":"/local/home/mimayere/strata2/StrataTest/Languages/Core/Examples/QuantifiersWithTypeAliases.lean","isSilent":false,"keepFullRange":false,"kind":"[anonymous]","pos":{"column":0,"line":91},"severity":"error"}
-/
#guard_msgs in
#eval verify QuantTypeAliases
