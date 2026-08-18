/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

/-
These verification-only roots quantify over arbitrary hidden global inputs;
concrete initialized-entry behavior is covered in Execution/GlobalVariables.lean.
-/

import StrataTest.Util.TestLaurel

open StrataTest.Util
open Strata

/-! ## A write through a call is observed by a later read of the same global.
    `setG` writes `g` and exposes `g == v`; after `setG(42)`, `g == 42` holds. -/

#guard_msgs (drop info) in
#eval testLaurelVerification <|
#strata
program Laurel;
var g: int := 0
procedure setG(v: int)
  opaque
  ensures g == v
{
  g := v
};
procedure useG() opaque {
  setG(42);
  assert g == 42
};
#end

/-! ## A read-only global is threaded as a plain input and its value flows in.
    `readG` is transparent (ends in `return`) and reads `g`; after `g := 7`
    the read observes 7. -/

#guard_msgs (drop info) in
#eval testLaurelVerification <|
#strata
program Laurel;
var g: int := 0
procedure readG() returns (r: int) {
  return g
};
procedure check() opaque {
  g := 7;
  var x: int := readG();
  assert x == 7
};
#end

/-! ## Conditional writers preserve incoming state on the no-write path.
    An explicit input records that state because `old(global)` is unsupported. -/

#guard_msgs (drop info) in
#eval testLaurelVerification <|
#strata
program Laurel;
var g: int := 0
procedure maybe(c: bool, incoming: int)
  requires g == incoming
  opaque
  ensures c ==> g == 99
  ensures !c ==> g == incoming
{
  if c then {
    g := 99
  } else {
    assert true
  }
};
procedure keepsValue() opaque {
  g := 5;
  maybe(false, 5);
  assert g == 5
};
#end

/-! ## Two independent globals are framed separately: writing `a` does not
    disturb `b`. `bumpA` touches only `a`, so `b` is not even a parameter of it,
    and the caller's `b` is unchanged across the call. -/

#guard_msgs (drop info) in
#eval testLaurelVerification <|
#strata
program Laurel;
var a: int := 0
var b: int := 0
procedure bumpA()
  opaque
{
  a := a + 1
};
procedure framing() opaque {
  a := 0;
  b := 3;
  bumpA();
  assert b == 3
};
#end

/-! ## Negative: the threaded global carries a real (non-havoc, non-vacuous)
    value, so a wrong assertion about it is correctly flagged. `setG(42)` makes
    `g == 42`, so `assert g == 43` must fail to prove. -/

#guard_msgs (drop info) in
#eval testLaurelVerification <|
#strata
program Laurel;
var g: int := 0
procedure setG(v: int)
  opaque
  ensures g == v
{
  g := v
};
procedure wrongClaim() opaque {
  setG(42);
  assert g == 43
//^^^^^^^^^^^^^^ error: assertion does not hold
};
#end

/-! ## Assigning a writer's return value to the SAME global it writes. `setAndGet`
    writes `g` internally and returns a value; `g := setAndGet(5)` must overwrite
    `g` with the return value. The pass must not emit a duplicate target
    (`g, g := …`); the threaded write-back is routed to a discard so the explicit
    assignment lands the return value in `g`. -/

#guard_msgs (drop info) in
#eval testLaurelVerification <|
#strata
program Laurel;
var g: int := 0
procedure setAndGet(v: int) returns (r: int)
  opaque
  ensures g == v
  ensures r == v
{
  g := v;
  return v
};
procedure useIt() opaque {
  g := setAndGet(5);
  assert g == 5
};
#end

#guard_msgs (drop info) in
#eval testLaurelVerification <|
#strata
program Laurel;
var g: int := 0
procedure inc()
  opaque
{
  g := g + 1
};
procedure withParameter(g: int) returns (r: int)
  opaque
  ensures r == g
{
  inc();
  return g
};
procedure withLocal() returns (r: int)
  opaque
  ensures r == 7
{
  var g: int := 7;
  inc();
  return g
};
procedure checkShadows() opaque {
  g := 0;
  var a: int := withParameter(5);
  var b: int := withLocal();
  assert a == 5 && b == 7
};
#end

/-! ## A global written inside a while-loop body is threaded through the loop.
    The invariant relates the current global value to the loop counter without
    requiring unsupported `old(global)` state. -/

#guard_msgs (drop info) in
#eval testLaurelVerification <|
#strata
program Laurel;
var g: int := 0
procedure setG(v: int)
  opaque
  ensures g == v
{
  g := v
};
procedure setToN(n: int)
  requires n >= 0
  opaque
  ensures g == n
{
  g := 0;
  var i: int := 0;
  while (i < n)
    invariant 0 <= i && i <= n
    invariant g == i {
    i := i + 1;
    setG(i)
  }
};
#end

/-! ## A global read in a `requires` precondition is threaded as an input and the
    caller must establish it. `needsPositive` requires `g > 0`; the caller sets
    `g := 5` first, so the precondition holds at the call site. This exercises
    precondition threading (the reader takes `g` as an input parameter and the
    call site passes the current global in). -/

#guard_msgs (drop info) in
#eval testLaurelVerification <|
#strata
program Laurel;
var g: int := 0
procedure needsPositive()
  requires g > 0
  opaque
{
  assert g > 0
};
procedure caller() opaque {
  g := 5;
  needsPositive()
};
#end

/-! ## Value preservation for an assignment in expression position whose RHS is a
    global-writer. `(x := weird()) + 1` must still evaluate to `x + 1`: `weird`
    returns 7 and writes `g := 100`, so `x == 7` and the expression is `8`. The
    pass threads `g` as a leading write-back target of the lifted call and then
    reads the original target back, so the value flows correctly (without the
    value-preservation suffix this fails re-resolution as a tuple type). -/

#guard_msgs (drop info) in
#eval testLaurelVerification <|
#strata
program Laurel;
var g: int := 0
procedure weird() returns (r: int)
  opaque
  ensures g == 100
  ensures r == 7
{
  g := 100;
  return 7
};
procedure useAssign() returns (r: int)
  opaque
  ensures r == 8
{
  var x: int := 0;
  return (x := weird()) + 1
};
#end

/-! Global references in non-body procedure fields are threaded too. -/

#guard_msgs (drop info) in
#eval testLaurelVerification <|
#strata
program Laurel;
composite CastCell {
  var value: int
}
var castGlobal: int := 0
procedure castWriter() returns (c: CastCell)
  opaque
  ensures castGlobal == 1
{
  castGlobal := 1;
  return new CastCell
};
procedure castCaller() opaque {
  castGlobal := 0;
  castWriter() as CastCell;
  assert castGlobal == 1
};
#end


/-! Effectful explicit arguments are evaluated before a callee samples globals. -/

#guard_msgs (drop info) in
#eval testLaurelVerification <|
#strata
program Laurel;
var g: int := 0
procedure writeAndReturn(v: int) returns (r: int)
  opaque
  ensures g == v
  ensures r == v
{
  g := v;
  return v
};
procedure readAfter(x: int) returns (r: int) {
  return g + x
};

procedure argumentOrder() opaque {
  g := 0;
  var observed: int := readAfter(writeAndReturn(5));
  assert observed == 10
};
#end

/-! All explicit arguments retain left-to-right values when a later one mutates
    a hidden global. The first `g` must remain 2 while the callee's hidden `g`
    observes 5. -/

#guard_msgs (drop info) in
#eval testLaurelVerification <|
#strata
program Laurel;
var g: int := 0
procedure writeAndReturn(v: int) returns (r: int)
  opaque
  ensures g == v
  ensures r == v
{
  g := v;
  return v
};
procedure observe(before: int, written: int) returns (r: int) {
  return before * 100 + g * 10 + written
};
procedure explicitArgumentOrder() opaque {
  g := 2;
  var observed: int := observe(g, writeAndReturn(5));
  assert observed == 255
};
#end

/-! A stale hidden-global capture would incorrectly prove this assertion. -/

#guard_msgs (drop info) in
#eval testLaurelVerification <|
#strata
program Laurel;
var g: int := 0
procedure writeAndReturn(v: int) returns (r: int)
  opaque
  ensures g == v
  ensures r == v
{
  g := v;
  return v
};
procedure readAfter(x: int) returns (r: int) {
  return g + x
};
procedure wrongArgumentOrder() opaque {
  g := 0;
  var observed: int := readAfter(writeAndReturn(5));
  assert observed == 5
//^^^^^^^^^^^^^^^^^^^^ error: assertion does not hold
};
#end

/-! Constrained globals preserve range contracts through global lowering. -/

#guard_msgs (drop info) in
#eval testLaurelVerification <|
#strata
program Laurel;
constrained nat = x: int where x >= 0 witness 0
var count: nat := 0
//         ^^^ error: postcondition does not hold
procedure readCount() returns (r: int) {
  return count
};
procedure constrainedGlobal() opaque {
  assert readCount() >= 0;
  count := 3;
  assert count == 3;
  count := -1
//^^^^^^^^^^^ error: assertion does not hold
};
#end



/-! Constrained global contracts cover instance methods and their callers. -/

#guard_msgs (drop info) in
#eval testLaurelVerification <|
#strata
program Laurel;
constrained nat = x: int where x >= 0 witness 0
var count: nat := 0
//         ^^^ error: postcondition does not hold
composite ConstrainedCounter {
  procedure read(self: ConstrainedCounter) returns (r: int) {
    assert count >= 0;
    return count
  };
  procedure writeInvalid(self: ConstrainedCounter) opaque {
    count := -1
//  ^^^^^^^^^^^ error: assertion does not hold
  };
}
procedure checkInstanceConstraint(c: ConstrainedCounter) opaque {
  var observed: int := c#read();
  assert observed >= 0
};
#end
/-! ## Lifted instance methods thread file-scope global reads and writes. -/

#guard_msgs (drop info) in
#eval testLaurelVerification <|
#strata
program Laurel;
var g: int := 0
composite GlobalCell {
  procedure set(self: GlobalCell, v: int)
    opaque
    ensures g == v
  {
    g := v
  };
  procedure get(self: GlobalCell) returns (r: int) {
    return g
  };
}
procedure checkInstance(c: GlobalCell) opaque {
  c#set(9);
  var observed: int := c#get();
  assert observed == 9
};
#end

/-! ## Non-mutating arguments remain supported for global-dependent inout calls. -/

#guard_msgs (drop info) in
#eval testLaurelVerification <|
#strata
program Laurel;
var g: int := 0
procedure readMutate(x: int, y: int) returns (x: int, r: int)
  opaque
  ensures x == old(x) + g + y
  ensures r == x
{
  x := x + g + y;
  r := x
};
procedure checkInout() opaque {
  g := 3;
  var x: int := 1;
  var r: int;
  assign x, r := readMutate(x, 0);
  assert x == 4 && r == 4
};
#end

/-! ## Global and heap state threading compose positionally -/

#guard_msgs (drop info) in
#eval testLaurelVerification <|
#strata
program Laurel;
var g: int := 0
composite StateCell {
  var value: int
}
procedure mutateGlobalAndHeap(c: StateCell) returns (r: int)
  opaque
  ensures g == 7
  ensures c#value == 8
  ensures r == 9
  modifies c
{
  g := 7;
  c#value := 8;
  r := 9
};
procedure checkGlobalAndHeap(c: StateCell)
  opaque
  modifies c
{
  g := 0;
  c#value := 0;
  var r: int := mutateGlobalAndHeap(c);
  assert g == 7;
  assert c#value == 8;
  assert r == 9
};
#end

/-! ## Effectful heap arguments run before hidden heap state is sampled. -/

#guard_msgs (drop info) in
#eval testLaurelVerification <|
#strata
program Laurel;
composite OrderedCell {
  var value: int
}
var orderedGlobal: int := 0
procedure writeHeap(c: OrderedCell) returns (r: int)
  opaque
  ensures c#value == 5
  ensures r == 2
  modifies c
{
  c#value := 5;
  r := 2
};
procedure readGlobalAndHeap(c: OrderedCell, x: int) returns (r: int) {
  return orderedGlobal + c#value + x
};
procedure checkHeapArgumentOrder(c: OrderedCell)
  opaque
  modifies c
{
  orderedGlobal := 1;
  c#value := 0;
  var observed: int := readGlobalAndHeap(c, writeHeap(c));
  assert observed == 8
};
#end

/-! ## A field write through a composite-valued global composes a hidden global
    input with heap state. The global reference itself is read-only while its
    field is updated through the heap. -/

#guard_msgs (drop info) in
#eval testLaurelVerification <|
#strata
program Laurel;
composite GlobalCell {
  var value: int
}
var globalCell: GlobalCell := new GlobalCell
procedure setGlobalField()
  opaque
  ensures globalCell#value == 11
  modifies globalCell
{
  globalCell#value := 11
};
procedure checkGlobalField()
  opaque
  modifies globalCell
{
  globalCell#value := 0;
  setGlobalField();
  assert globalCell#value == 11
};
#end

/-! ## Explicit inout, hidden global input, heap writeback, and an ordinary
    result retain their positional correspondence through both hidden-state
    parameterization passes. -/

#guard_msgs (drop info) in
#eval testLaurelVerification <|
#strata
program Laurel;
var mixedGlobal: int := 0
composite MixedState {
  var value: int
}
procedure mutateAll(state: MixedState, x: int) returns (x: int, r: int)
  opaque
  ensures x == old(x) + mixedGlobal
  ensures state#value == x + 2
  ensures r == state#value + 1
  modifies state
{
  x := x + mixedGlobal;
  state#value := x + 2;
  r := state#value + 1
};
procedure checkMixedOutputs(state: MixedState)
  opaque
  modifies state
{
  mixedGlobal := 3;
  state#value := 0;
  var x: int := 1;
  var r: int;
  assign x, r := mutateAll(state, x);
  assert x == 4;
  assert mixedGlobal == 3;
  assert state#value == 6;
  assert r == 7
};
#end

/-! ## A global write performed before an exceptional exit is returned beside
    the lowered `Result` and is visible in the caller's catch handler. This
    exercises exception lowering before global parameterization. -/

#guard_msgs (drop info) in
#eval testLaurelVerification <|
#strata
program Laurel;
composite GlobalError {}
var exceptionalGlobal: int := 0
procedure writeThenThrow()
  throws (thrown: GlobalError)
  opaque
  throwsOn true {
    ensures exceptionalGlobal == 5
  }
{
  exceptionalGlobal := 5;
  var err: GlobalError := new GlobalError;
  throw err
};
procedure catchGlobalWrite() opaque {
  exceptionalGlobal := 0;
  try {
    writeThenThrow()
  } catch err when err is GlobalError {
    assert exceptionalGlobal == 5
  };
  assert exceptionalGlobal == 5
};
#end
