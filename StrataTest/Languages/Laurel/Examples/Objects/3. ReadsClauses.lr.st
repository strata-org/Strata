/*
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
*/

/*
Reads clauses CAN be placed on a deterministic procedure to generate a reads axiom.
This axioms states that the result of the procedure is the same if all arguments
and all read heap objects are the same
*/

composite Container {
  var value: int
}

procedure opaqueProcedure(c: Container): int
  reads c
  ensures true

procedure foo(c: Container, d: Container) 
{
  var x = opaqueProcedure(c);
  d.value = 1;
  var y = opaqueProcedure(c);
  assert x == y; // proved using reads clause of opaqueProcedure
  c.value = 1;
  var z = opaqueProcedure(c);
  assert x == z;
//         ^^ error: could not prove assert
}

procedure permissionLessReader(c: Container): int
  reads {}
  { c.value }
//  ^^^^^^^ error: enclosing procedure 'permissionLessReader' does not have permission to read 'c.value'

/*
Translation towards SMT:

type Composite;
type Field;
val value: Field;

function opaqueProcedure_ensures(heap: Heap, c: Container, r: int): boolean {
  true
}

axiom opaqueProcedure_reads(heap1: Heap, heap2: Heap, c: Container) {
  heap1[c] == heap2[c] ==> varReader(heap1, c) == varReader(heap2, c)
}

proof foo_body {
  var heap: Heap;
  var c: Container;
  var d: Container;

  var x: int;
  assume opaqueProcedure_ensures(heap, c, x);
  heap = update(heap, d, value, 1);
  var y: int;
  assume opaqueBody_ensures(heap, c, y);
  assert x == y; // pass
  heap = update(heap, c, value, 1);
  var z: int;
  assume opaqueBody_ensures(heap, c, z);
  assert x == z; // fail
}

proof permissionLessReader_body {
  var heap: Heap
  var c: Container;
  var reads_permissions: Set<Composite>;

  assert reads_permissions[c]; // fail
}
*/

