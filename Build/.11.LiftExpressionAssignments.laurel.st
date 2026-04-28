datatype TypeTag {  }

datatype Field {  }

datatype Box {  }

datatype Composite { MkComposite(ref: int, typeTag: TypeTag) }

datatype NotSupportedYet {  }

datatype Heap { MkHeap(data: (Map Composite (Map Field Box)), nextReference: int) }

function readField(heap: Heap, obj: Composite, field: Field): Box
{ select(select(Heap..data!(heap), obj), field) };

function updateField(heap: Heap, obj: Composite, field: Field, val: Box): Heap
{ MkHeap(update(Heap..data!(heap), obj, update(select(Heap..data!(heap), obj), field, val)), Heap..nextReference!(heap)) };

function increment(heap: Heap): Heap
{ MkHeap(Heap..data!(heap), Heap..nextReference!(heap) + 1) };

function select(map: int, key: int): intexternal;

function update(map: int, key: int, value: int): intexternal;

function const(value: int): intexternal;

procedure imperativeProc(x: int)
  returns (r: int)
  opaque
  ensures r == x + 1
{ r := x + 1; r };

procedure imperativeCallInExpressionPosition()
  opaque
{ var x: int := 0; var $c_0: int; $c_0 := imperativeProc(x); var y: int := $c_0 + x; assert y == 1; assert x == 0 };
