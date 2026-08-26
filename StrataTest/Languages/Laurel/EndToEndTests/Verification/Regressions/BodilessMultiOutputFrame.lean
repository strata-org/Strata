/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import StrataTest.Util.TestLaurel

open StrataTest.Util
open Strata

/-!
## A bodiless frame is honoured whatever the output count

`HeapParameterization` declares the heap write on every procedure `HeapAnalysis` calls a
heap writer, which for a bodiless procedure means one whose `modifies` names a target --
its frame is the only evidence that it touches the heap. The declaration and
`model.heapWriters` therefore agree by construction.

They must: if a procedure is treated as a heap writer when its frame is built but its
heap write is not declared, `GlobalParameterization` threads `$heap` as a plain input
rather than an inout. The caller passes its heap in and receives nothing back, so it
concludes the heap is unchanged -- including at the locations the callee's frame says may
change -- and an assertion that should fail verifies instead.

`f` below is the shape that detects it: bodiless, two value outputs, and a `modifies`
naming a single field.
-/

#guard_msgs (drop info) in
#eval testLaurelVerification <|
#strata
program Laurel;
composite C { var v: int }
procedure f(c: C) returns (a: int, b: int)
  opaque
  ensures a == 1
  ensures b == 2
  modifies c#v;
procedure caller(c: C)
  opaque
  modifies c
{
  c#v := 5;
  var x: int := 0;
  var y: int := 0;
  assign x, y := f(c);
  assert c#v == 5
//^^^^^^^^^^^^^^^ error: assertion could not be proved
};
#end
