/*
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
*/

/*
A modifies clause CAN be placed on any procedure to generate a modifies axiom.
The modifies clause determines which references the procedure may modify.
This modifies axiom states how the in and out heap of the procedure relate.

A modifies clause is crucial on opaque procedures, 
since otherwise all heap state is lost after calling them.

*/
composite Container {
  var value: int
}

procedure modifyContainerOpaque(c: Container) 
  ensures true // makes this procedure opaque. Maybe we should use explicit syntax
  modifies c
{
  modifyContainerTransparant(c);
}

procedure modifyContainerTransparant(c: Container) 
{
  c.value = c.value + 1;
}

procedure caller(c: Container, d: Container) {
  var x = d.value;
  modifyContainerOpaque(c);
  assert x == d.value; // pass
}

procedure modifyContainerWithoutPermission(c: Container) 
  ensures true
{
  c.value = c.value + 1;
//        ^ error: enclosing procedure 'modifyContainerWithoutPermission' does not have permission to modify 'c.value'
}

/*
Possible translation towards SMT:

type Composite
type Field
val value: Field

function modifyContainer(heap_in: Heap, c: Composite) returns (heap_out: Heap) {
  var heap = update(heap_in, c, value, read(heap_in, c, value))
  heap_out = heap;
}

axiom modifyContainer_modifies(heap_in: Heap, c: Composite, other: Composite, heap_out: Heap) {
  c != other ==> heap_in[other] == heap_out[other]
}

proof caller_body {
  var heap_in: Heap;
  var c: Composite;
  var d: Composite;
  var heap_out: Heap;

  var heap = heap_in;
  var x = read(heap, d, value);
  heap = modifyContainer(heap_in, c);
  assert x = read(heap, d, value);
  heap_out = heap;
}

proof modifyContainer_body {
  var heap_in: Heap;
  var c: Composite; 
  var heap_out: Heap;
  val modify_permission: Set[Composite];

  assume c in modify_permission;
  assert c in modify_permission; // pass
}

proof modifyContainerWithoutPermission_body {
  var heap_in: Heap;
  var c: Composite; 
  var heap_out: Heap;
  val modify_permission: Set[Composite];

  assert c in modify_permission; // fail
}
*/