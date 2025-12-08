/*
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
*/

composite Container {
  var value: int // var indicates mutable field
}

procedure foo(c: Container, d: Container): int
  requires c != d
{ 
  var x = c.value;
  d.value = d.value + 1;
  assert x == c.value; // pass
}

procedure caller(c: Container, d: Container) {
  var x = foo(c, d);
}

procedure impureContract(c: Container)
  ensures foo(c, c) 
//           ^ error: a procedure that modifies the heap may not be called in pure context.

/*
Translation towards SMT:

type Composite;
type Field;
val value: Field

function foo(heap_in: Heap, c: Composite, d: Composite) returns (r: int, out_heap: Heap) {
  var heap = heap_in;
  var x = read(heap, c, value);
  heap = update(heap, d, value, read(heap, d, value));
  heap_out = heap;
}

proof foo_body {
  var heap_in;
  var Heap;
  var c: Composite;
  var d: Composite;
  var r: int;
  var out_heap: Heap;

  var heap = heap_in;
  var x = read(heap, c, value);
  heap = update(heap, d, value, read(heap, d, value));
  assert x == read(heap, c, value);
}

proof caller {
  var heap_in;
  var Heap;
  var c: Composite;
  var d: Composite;
  var heap_out: Heap;

  heap = heap_in;
  var x: int;
  (x, heap) = foo(heap, c, d);
  heap_out = heap;
}
*/