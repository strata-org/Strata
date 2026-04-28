program Core;

datatype TypeTag {
  MkTypeTag()
};
datatype Field {
  MkField()
};
datatype Box {
  MkBox()
};
datatype Composite {
  MkComposite(ref : int, typeTag : TypeTag)
};
datatype NotSupportedYet {
  MkNotSupportedYet()
};
datatype Heap {
  MkHeap(data : Map Composite (Map Field Box), nextReference : int)
};
function readField (heap : Heap, obj : Composite, field : Field) : Box {
  ((Heap..data!(heap))[obj])[field]
}
function updateField (heap : Heap, obj : Composite, field : Field, val : Box) : Heap {
  MkHeap((Heap..data!(heap))[obj:=((Heap..data!(heap))[obj])[field:=val]], Heap..nextReference!(heap))
}
function increment (heap : Heap) : Heap {
  MkHeap(Heap..data!(heap), Heap..nextReference!(heap) + 1)
}
procedure imperativeProc (x : int, out r : int)
spec {
  ensures [postcondition]: r == x + 1;
  } {
  $body: {
    r := x + 1;
    var $unused_1 : $__ty_unused_1 := r;
  }
};
procedure imperativeCallInExpressionPosition ()
{
  $body: {
    var x : int := 0;
    var $c_0 : int;
    call imperativeProc(x, out $c_0);
    var y : int := $c_0 + x;
    assert [|assert(509)|]: y == 1;
    assert [|assert(526)|]: x == 0;
  }
};

