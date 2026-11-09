/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

meta import StrataLaurel.Tests.Util.TestLaurel
import StrataLaurel.Implementation.LowerComposite
import StrataLaurel.Implementation.ConstrainedTypeElim
import StrataLaurel.Implementation.HeapParameterization

open Strata
open StrataTest.Util

namespace Strata.Laurel

private meta def lowered (program : LaurelProgram) (model : SemanticModel) : LaurelProgram :=
  match lowerComposite model program with
  | .ok p =>
    let r := resolve p (some model)
    let (c, _) := constrainedTypeElim r.model r.program
    (resolve c (some r.model)).program
  | .error _ => program

/--
info: datatype Field { Node.value, Node.next, Node.flag }
datatype $Box { BoxInt(intVal: int), BoxComposite(compositeVal: Composite) }
datatype NotSupportedYet {  }
datatype Heap { MkHeap(data: (TotalMap int (TotalMap Field $Box)), nextReference: int) }
datatype TypeTag { Node_TypeTag }
datatype Composite { MkComposite(ref: int, typeTag: TypeTag) }
 var $heap: Heap
procedure readField(heap: Heap, obj: int, field: Field): $Box
return select(select(Heap..data!(heap), obj), field);
procedure updateField(heap: Heap, obj: int, field: Field, val: $Box): Heap
return MkHeap(update(Heap..data!(heap), obj, update(select(Heap..data!(heap), obj), field, val)), Heap..nextReference!(heap));
procedure increment(heap: Heap): Heap
return MkHeap(Heap..data!(heap), Heap..nextReference!(heap) + 1);
procedure Node$constraint($c: Composite): bool
{
  $result := Composite..typeTag!($c) == Node_TypeTag();
  return
};
procedure read(n: Composite)
  returns (r: int)
  free requires Composite..ref!(n) < Heap..nextReference!($heap) summary "input is allocated on the heap"
  free requires Node$constraint(n)
  opaque
{
  r := $Box..intVal!(readField($heap, Composite..ref!(n), Node.value()));
  r
};
procedure link(n: Composite, m: Composite)
  free requires Composite..ref!(n) < Heap..nextReference!($heap) summary "input is allocated on the heap"
  free requires Composite..ref!(m) < Heap..nextReference!($heap) summary "input is allocated on the heap"
  free requires Node$constraint(n)
  free requires Node$constraint(m)
  opaque
  free ensures old(Heap..nextReference!($heap)) <= Heap..nextReference!($heap) summary "monotonic heap pointer"
  modifies n
  writes $heap
{
  var $writeValue0: Composite := m;
  $heap := updateField($heap, Composite..ref!(n), Node.next(), BoxComposite($writeValue0));
  var $writeValue1: int := $Box..intVal!(readField($heap, Composite..ref!(n), Node.value())) + 1;
  $heap := updateField($heap, Composite..ref!(n), Node.value(), BoxInt($writeValue1))
};
procedure fresh()
  returns (r: Composite)
  opaque
  free ensures old(Heap..nextReference!($heap)) <= Heap..nextReference!($heap) summary "monotonic heap pointer"
  free ensures Composite..ref!(r) < Heap..nextReference!($heap) summary "output is allocated on the heap"
  free ensures Node$constraint(r)
  modifies *
  writes $heap
{
  r := MkComposite({
    var $allocated2: int := Heap..nextReference!($heap);
    $heap := increment($heap);
    $allocated2
  }, Node_TypeTag());
  r
};
procedure pure(x: int)
  returns (r: int)
  opaque
{
  r := x
};
procedure $witness_Node()
  opaque
{
  var $witness: Composite := MkComposite(0, Node_TypeTag());
  assert Node$constraint($witness)
};
procedure downcast$Node(p: Composite)
  returns (r: Composite)
  requires Node$constraint(p)
{
  r := p
};
-/
#guard_msgs in
#eval runPassAfterForIdiomaticity heapParameterizationPass lowered <|
#strata
program Laurel;
composite Node { var value: int  var next: Node  flag: bool }
procedure read(n: Node) returns (r: int)
  opaque
{
  r := n#value
};
procedure link(n: Node, m: Node)
  opaque
  modifies n
{
  n#next := m;
  n#value := n#value + 1
};
procedure fresh() returns (r: Node)
  opaque
  modifies *
{
  r := new Node
};
procedure pure(x: int) returns (r: int)
  opaque
{
  r := x
};
#end

end Strata.Laurel
