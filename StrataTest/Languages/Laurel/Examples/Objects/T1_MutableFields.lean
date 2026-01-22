/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import StrataTest.Util.TestDiagnostics
import StrataTest.Languages.Laurel.TestExamples

open StrataTest.Util

namespace Strata
namespace Laurel

def program := r"
composite Container {
  var intValue: int // var indicates mutable field
  var boolValue: bool
}

procedure foo(c: Container, d: Container) returns (r: int)
  requires c != d && d#intValue == 1
  ensures d#intValue == 3
{
  var x: int := c#intValue;
  var initialDValue: int := d#intValue;
  d#intValue := d#intValue + 1;
  c#intValue := c#intValue + 1;
  assert x + 1 == c#intValue; // pass
  assert initialDValue + 1 == d#intValue;

  var e: Container := d;
  e#intValue := e#intValue + 1;
  assert e#intValue == d#intValue;
}

procedure useBool(c: Container) returns (r: bool) {
  r := c#boolValue;
}

// The following two need support for calling procedures in an expression context.
procedure caller(c: Container, d: Container) {
  assume d#intValue == 1;
  var x: int := foo(c, d);
  assert d#intValue == 3;
}

//procedure impureContract(c: Container) {
//  assert foo(c,c) == 3;
//}
"

-- #guard_msgs(drop info, error) in
#eval testInputWithOffset "MutableFields" program 14 processLaurelFile

/-
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
-/
