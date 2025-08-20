program Boogie;
// lake exe StrataVerify Strata/Languages/Boogie/Examples/HeapReasoning.boogie.st 

// Prelude begin --------------------------------------------------
type Ref;
type Field;
type Box;

const null: Ref;

type Struct := Map Field Box;
type Heap := Map Ref Struct;


function isInt(v: Box): bool;
function isBool(v: Box): bool;
function isString(v: Box): bool;
function isRef(v: Box): bool;

// Replace by allocation time, one tick per 1) allocation 2) method call, const for each Ref = allocation time, prove disjointness by proving that the allocation is greater
var tickingClock: int;
function allocationTime(r: Ref): int;

axiom [allocationTimeOfNullIsSmallerThanEverything]: allocationTime(null) == -1;


// Monomorphized boxing unboxing functions
// int
function BoxingInt(v: int): Box;
function UnboxingInt(b: Box): int;
axiom [BoxingUnboxingInverseInt]: forall v: int :: { BoxingInt(v) } isInt(BoxingInt(v)) && UnboxingInt(BoxingInt(v)) == v;
axiom [UnboxingBoxingInverseInt]: forall b: Box :: { isInt(b) } isInt(b) ==> BoxingInt(UnboxingInt(b)) == b;
// bool
function BoxingBool(v: bool): Box;
function UnboxingBool(b: Box): bool;
axiom [BoxingUnboxingInverseBool]: forall v: bool :: { BoxingBool(v) } isBool(BoxingBool(v)) && UnboxingBool(BoxingBool(v)) == v;
axiom [UnboxingBoxingInverseBool]: forall b: Box :: { isBool(b) } isBool(b) ==> BoxingBool(UnboxingBool(b)) == b;
// string
function BoxingStr(v: string): Box;
function UnboxingStr(b: Box): string;
axiom [BoxingUnboxingInverseStr]: forall v: string :: { BoxingStr(v) } isString(BoxingStr(v)) && UnboxingStr(BoxingStr(v)) == v;
axiom [UnboxingBoxingInverseStr]: forall b: Box :: { isString(b) } isString(b) ==> BoxingStr(UnboxingStr(b)) == b;
// refs
function BoxingRef(v: Ref): Box;
function UnboxingRef(b: Box): Ref;
axiom [BoxingUnboxingInverseRef]: forall v: Ref :: { BoxingRef(v) } isRef(BoxingRef(v)) && UnboxingRef(BoxingRef(v)) == v;
axiom [UnboxingBoxingInverseRef]: forall b: Box :: { isRef(b) } isRef(b) ==> BoxingRef(UnboxingRef(b)) == b;
// Prelude end ----------------------------------------------------

// Can try Heap: Map Ref -> Box. Box can contain structs. Structs would be axiomatized with the boxing unboxing functions
// Container struct axioms ----------------------------------------
function isContainer(r: Ref): bool;
function isContainerStruct(s: Struct): bool;

const lycheeField: Field;           // int
const pineappleField: Field;        // int
const nextField: Field;             // Ref to a Container
axiom [ContainerFieldsAreDifferent1]: lycheeField != pineappleField && lycheeField != nextField && pineappleField != nextField;

axiom [ContainerstructType]: forall h:Heap, r: Ref :: { h[r] } isContainer(r) ==> isContainerStruct(h[r]);
axiom [lycheeFieldType]: forall s: Struct :: { s[lycheeField] } isContainerStruct(s) ==> isInt(s[lycheeField]);
axiom [pineappleFieldType]: forall s: Struct :: { s[pineappleField] } isContainerStruct(s) ==> isInt(s[pineappleField]);
axiom [nextFieldType]: forall s: Struct :: { s[nextField] } isContainerStruct(s) ==> (isRef(s[nextField]) && isContainer(UnboxingRef(s[nextField])));


// Modifies frame for Container_ctor (manual lambda lifting)
function Container_ctorModifiesFrame(h: Heap, testedRef: Ref, r: Ref, methodEntryTime: int): bool {
  testedRef == r || (allocationTime(testedRef) >= methodEntryTime)
}
procedure Container_ctor(heap: Heap, r: Ref, initialLychee: int, initialPineapple: int, initialNext: Ref) returns (newHeap: Heap)
spec {
  // Refs are allocated
  free requires tickingClock >= 0;
  free requires allocationTime(r) < tickingClock;
  free requires allocationTime(initialNext) < tickingClock;
  requires isContainer(r);

  free ensures (forall o: Ref :: 
    { newHeap[o] } 
    (o != null && allocationTime(o) >= 0 && allocationTime(o) < old(tickingClock))
       ==> (newHeap[o] == heap[o] || o == r));

  // User provided ------------------------------------------------------------------------------------------------------------
  requires isContainer(initialNext) || initialNext == null;
  requires r != initialNext;
  ensures UnboxingInt(newHeap[r][lycheeField]) == initialLychee;
  ensures UnboxingInt(newHeap[r][pineappleField]) == initialPineapple;
  ensures UnboxingRef(newHeap[r][nextField]) == initialNext;

  ensures tickingClock >= old(tickingClock);

}
{
  var heap_var: Heap := heap;
  var methodEntryTime: int := tickingClock;

  // r.lychee = initialLychee
  assert [modifiesFrameRef1]: Container_ctorModifiesFrame(heap_var, r, r, methodEntryTime);
  var rhs1: Box := BoxingInt(initialLychee);
  heap_var := heap_var[r := heap_var[r][lycheeField := rhs1]];

  // r.pineaple = initialPineapple
  assert [modifiesFrameRef1]: Container_ctorModifiesFrame(heap_var, r, r, methodEntryTime);
  var rhs2: Box := BoxingInt(initialPineapple);
  heap_var := heap_var[r := heap_var[r][pineappleField := rhs2]];

  // r.next = initialNext
  assert [modifiesFrameRef1]: Container_ctorModifiesFrame(heap_var, r, r, methodEntryTime);
  var rhs3: Box := BoxingRef(initialNext);
  heap_var := heap_var[r := heap_var[r][nextField := rhs3]];

  newHeap := heap_var;

};

// Modifies frame for UpdateContainers (manual lambda lifting)
function UpdateContainersModifiesFrame(h: Heap, testedRef: Ref, ref1: Ref, ref2: Ref, methodEntryTime: int): bool {
  testedRef == ref1 || testedRef == ref2 || (allocationTime(testedRef) >= methodEntryTime)
}

// Annotated with "modifies ref1, ref2"
procedure UpdateContainers(heap: Heap, ref1: Ref, ref2: Ref) returns (newHeap: Heap)
spec {
  // Refs are allocated
  free requires tickingClock >= 0;
  free requires allocationTime(ref1) < tickingClock;
  free requires allocationTime(ref2) < tickingClock;

  requires isContainer(ref1);
  requires isContainer(ref2);

  ensures tickingClock >= old(tickingClock);

  free ensures (forall o: Ref :: 
    { newHeap[o] } 
    (o != null && allocationTime(o) >= 0 && allocationTime(o) < old(tickingClock))
       ==> (newHeap[o] == heap[o] || o == ref1 || o == ref2));

  // User provided ------------------------------------------------------------------------------------------------------------
  requires ref1 != ref2; // At first, I forgot it, and indeed the verification conditions helped me realizing it

  requires UnboxingInt(heap[ref1][lycheeField]) == 0;
  requires UnboxingInt(heap[ref1][pineappleField]) == 0;
  requires UnboxingInt(heap[ref2][lycheeField]) == 0;
  requires UnboxingInt(heap[ref2][pineappleField]) == 0;

  ensures UnboxingInt(newHeap[ref1][lycheeField]) == 2;
  ensures UnboxingInt(newHeap[ref1][pineappleField]) == 2;
  ensures UnboxingInt(newHeap[ref2][lycheeField]) == 2;
  ensures UnboxingInt(newHeap[ref2][pineappleField]) == 2;

}
{
  var heap_var: Heap := heap;
  var methodEntryTime: int := tickingClock;

  // ref1.lychee += 1
  assert [modifiesFrameRef1]: UpdateContainersModifiesFrame(heap_var, ref1, ref1, ref2, methodEntryTime);
  var rhs1: Box := BoxingInt(UnboxingInt(heap_var[ref1][lycheeField]) + 1);
  heap_var := heap_var[ref1 := heap_var[ref1][lycheeField := rhs1]];

  // ref1.pineapple += 1
  assert [modifiesFrameRef1]: UpdateContainersModifiesFrame(heap_var, ref1, ref1, ref2, methodEntryTime);
  var rhs2: Box := BoxingInt(UnboxingInt(heap_var[ref1][pineappleField]) + 1);
  heap_var := heap_var[ref1 := heap_var[ref1][pineappleField := rhs2]];

  // ref2.lychee += 1
  assert [modifiesFrameRef1]: UpdateContainersModifiesFrame(heap_var, ref2, ref1, ref2, methodEntryTime);
  var rhs3: Box := BoxingInt(UnboxingInt(heap_var[ref2][lycheeField]) + 1);
  heap_var := heap_var[ref2 := heap_var[ref2][lycheeField := rhs3]];

  // ref2.pineapple += 1
  assert [modifiesFrameRef1]: UpdateContainersModifiesFrame(heap_var, ref2, ref1, ref2, methodEntryTime);
  var rhs4: Box := BoxingInt(UnboxingInt(heap_var[ref2][pineappleField]) + 1);
  heap_var := heap_var[ref2 := heap_var[ref2][pineappleField := rhs4]];

  // -----------------------------------------------------------------------------------------------------------------------


  // ref1.lychee += 1
  assert [modifiesFrameRef1]: UpdateContainersModifiesFrame(heap_var, ref1, ref1, ref2, methodEntryTime);
  var rhs5: Box := BoxingInt(UnboxingInt(heap_var[ref1][lycheeField]) + 1);
  heap_var := heap_var[ref1 := heap_var[ref1][lycheeField := rhs5]];

  // ref1.pineapple += 1
  assert [modifiesFrameRef1]: UpdateContainersModifiesFrame(heap_var, ref1, ref1, ref2, methodEntryTime);
  var rhs6: Box := BoxingInt(UnboxingInt(heap_var[ref1][pineappleField]) + 1);
  heap_var := heap_var[ref1 := heap_var[ref1][pineappleField := rhs6]];

  // ref2.lychee += 1
  assert [modifiesFrameRef1]: UpdateContainersModifiesFrame(heap_var, ref2, ref1, ref2, methodEntryTime);
  var rhs7: Box := BoxingInt(UnboxingInt(heap_var[ref2][lycheeField]) + 1);
  heap_var := heap_var[ref2 := heap_var[ref2][lycheeField := rhs7]];

  // ref2.pineapple += 1
  assert [modifiesFrameRef1]: UpdateContainersModifiesFrame(heap_var, ref2, ref1, ref2, methodEntryTime);
  var rhs8: Box := BoxingInt(UnboxingInt(heap_var[ref2][pineappleField]) + 1);
  heap_var := heap_var[ref2 := heap_var[ref2][pineappleField := rhs8]];
  
  // -----------------------------------------------------------------------------------------------------------------------

  // Return the new heap
  newHeap := heap_var;
};

// Modifies frame for Main (manual lambda lifting)
function MainModifiesFrame(h: Heap, testedRef: Ref, methodEntryTime: int): bool {
  (allocationTime(testedRef) >= methodEntryTime)
}

// annotated with "modifies {}"
procedure Main(heap: Heap) returns (newHeap: Heap)
spec {
  modifies tickingClock;

  free requires tickingClock >= 0;
  ensures tickingClock >= old(tickingClock);

  free ensures (forall o: Ref :: 
    { newHeap[o] } 
    (o != null && allocationTime(o) >= 0 && allocationTime(o) < old(tickingClock))
       ==> (newHeap[o] == heap[o]));
}
{
  var heap_var: Heap := heap;
  var methodEntryTime: int := tickingClock;

  // instantiate c1 (i.e., new Container(0, 1, null))
  var c1: Ref;
  assume allocationTime(c1) == tickingClock;
  assume isContainer(c1);
  tickingClock := tickingClock + 1;           // After allocation: increase the tick
  call heap_var := Container_ctor(heap_var, c1, 0, 0, null);

  assert [c1Lychees0]: isContainer(c1) && UnboxingInt(heap_var[c1][lycheeField]) == 0;
  assert [c1Pineapple1]: isContainer(c1) && UnboxingInt(heap_var[c1][pineappleField]) == 0;

  // instantiate c2 (i.e., new Container(0, 0, null))
  var c2: Ref;
  assume allocationTime(c2) == tickingClock;
  assume isContainer(c2);
  tickingClock := tickingClock + 1;           // After allocation: increase the tick
  call heap_var := Container_ctor(heap_var, c2, 0, 0, null);


  call heap_var := UpdateContainers(heap_var, c1, c2);

  assert [c1Lychees1]: isContainer(c1) && UnboxingInt(heap_var[c1][lycheeField]) == 2;
  assert [c1Pineapple2]: isContainer(c1) && UnboxingInt(heap_var[c1][pineappleField]) == 2;
  assert [c2Lychees0]: isContainer(c2) && UnboxingInt(heap_var[c2][lycheeField]) == 2;
  assert [c2Pineapple0]: isContainer(c2) && UnboxingInt(heap_var[c2][pineappleField]) == 2;

  // Return the new heap
  newHeap := heap_var;

};
