/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import StrataTest.Util.TestLaurel

open StrataTest.Util
open Strata

/-! ## No-op `old(...)` diagnostics

`Resolution.validateOldUsage` warns when an `old(...)` cannot capture any
pre/post-state difference. An `old(e)` is meaningful — and must NOT be warned —
whenever either:
- `e` references an inout parameter (its pre-state differs from its post-state,
  per the language definition: "Postconditions may reference `old v` for
  pre-state values of inout variables"), or
- the enclosing procedure (transitively) writes the heap and `e` reads heap
  state.

These tests pin down the cases the heap-only classification regressed:
inout parameters and heap writes performed through an `InstanceCall`. -/

/-! ### Regression 1: `old` of an inout parameter

`inc` writes no heap, but `x` is inout (it appears in both the inputs and the
outputs), so `old(x)` is the pre-state value and is meaningful. No warning. -/

#eval testLaurelResolution <|
#strata
program Laurel;
procedure inc(x: int) returns (x: int)
  opaque
  ensures x == old(x) + 1
{ x := x + 1 };
#end

/-! ### Regression 2: heap write performed through an `InstanceCall`

`caller` writes the heap only by calling `c#bump()`, which is an `InstanceCall`
at initial resolution (before `LiftInstanceProcedures` rewrites it to a static
call). The heap-effect analysis must follow `InstanceCall` callees, otherwise
`caller` is misclassified as non-heap-writing and `old(c#v)` is spuriously
warned. No warning. -/

#eval testLaurelResolution <|
#strata
program Laurel;
composite C {
  var v: int
  procedure bump(self: C)
    opaque
    ensures self#v == old(self#v) + 1
    modifies self
  { self#v := self#v + 1 };
}
procedure caller(c: C)
  opaque
  ensures c#v == old(c#v) + 1
  modifies c
{ c#bump() };
#end

/-! ### `old` of a call to a heap-reading function

`getV` reads the heap (it accesses `c#v`). In `bump`, which writes the heap,
`old(getV(c))` reads heap state only *through the call* — the operand itself
has no direct field access. `containsHeapRead` must follow the callee into the
`heapReaders` set to see this; otherwise it would spuriously warn that the
operand "contains no heap reads". No warning. -/

#eval testLaurelResolution <|
#strata
program Laurel;
composite C {
  var v: int
}
function getV(c: C) returns (r: int)
  opaque
  ensures r == c#v;
procedure bump(c: C)
  opaque
  ensures c#v == old(getV(c)) + 1
  modifies c
{ c#v := c#v + 1 };
#end

/-! ### Heap write performed via `c#f++`

`bumpIncr` writes the heap only through an increment (`c#v++`), which is an
`.IncrDecr` node at initial resolution — before `EliminateIncrDecr` lowers it to
`.Assign .Field`. The heap-effect analysis must recognize `IncrDecr` with a
field target as a write, otherwise `bumpIncr` is misclassified as non-heap
-writing and `old(c#v)` is spuriously warned. No warning. -/

#eval testLaurelResolution <|
#strata
program Laurel;
composite C {
  var v: int
}
procedure bumpIncr(c: C)
  opaque
  ensures c#v == old(c#v) + 1
  modifies c
{ c#v++ };
#end

/-! ### True positive still fires

A procedure that neither writes the heap nor references an inout parameter has
no pre/post distinction, so `old(...)` really is a no-op and must still warn.
This guards against the inout fix over-suppressing legitimate diagnostics. -/

#eval testLaurelResolution <|
#strata
program Laurel;
procedure pure(x: int) returns (r: int)
  opaque
  ensures r == old(x)
//             ^^^^^^ warning: `old(...)` has no effect
{ r := x };
#end
