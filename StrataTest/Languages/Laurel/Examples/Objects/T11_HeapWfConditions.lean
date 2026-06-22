/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

/-
A `modifies` frame condition must survive across repeated opaque calls.

`setIt(c, x) modifies c` is called once and twice from a caller that
also passes a disjoint `d` and asserts `d` is unchanged. The frame
condition of `setIt` only quantifies over objects allocated in the
input heap and distinct from `c`, so two facts must reach the caller
for the assertions to discharge:

  * `Composite..ref!(d) < Heap..nextReference!($heap_in)` — every
    composite is allocated in the input heap. This follows from the
    synthesized `heapIsValid($heap)` precondition supplied by
    `HeapParameterization` (a `forall` over composites).
  * the allocation counter is monotone across each call, so the
    allocation fact carries through a chain of calls. Supplied as a
    synthesized postcondition on every heap-writer.

Disjointness (`c != d`) is *not* synthesized — `c` and `d` may alias —
so the caller states `requires c != d` where it relies on it.
-/

import StrataTest.Util.TestLaurel

open StrataTest.Util
open Strata

#eval testLaurel <|
#strata
program Laurel;
composite Container {
  var value: int
}

procedure setIt(c: Container, x: int) returns (r: int)
  opaque
  ensures r == x
  ensures c#value == x
  modifies c
{
  c#value := x;
  return x
};

// One call: a disjoint `d` is preserved by setIt's frame condition.
procedure oneCall(c: Container, d: Container)
  requires c != d
  opaque
  modifies c
{
  var dOld: int := d#value;
  var r1: int := setIt(c, 10);
  assert d#value == dOld;
  assert c#value == 10;
  var r2: int := setIt(c, 20);
  assert c#value == 20
};

// Two consecutive calls: `d` stays preserved across both, and each call
// observes the latest value written to `c`.
procedure twoCalls(c: Container, d: Container)
  requires c != d
  opaque
  modifies c
{
  var dOld: int := d#value;
  var r1: int := setIt(c, 10);
  assert d#value == dOld;
  assert c#value == 10;
  var r2: int := setIt(c, 20);
  assert d#value == dOld;
  assert c#value == 20
};

// After the second call c#value == 20, so claiming 10 must fail.
procedure staleClaimRejected(c: Container)
  opaque
  modifies c
{
  var r1: int := setIt(c, 10);
  var r2: int := setIt(c, 20);
  assert c#value == 10
//^^^^^^^^^^^^^^^^^^^^ error: assertion could not be proved
};

composite ContainerContainer {
  var c: Container
}

procedure existingObjectsAreAllocated(cc: ContainerContainer) opaque {
  var c: Container := new Container;
  assert c != cc#c
};

#end
