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

/-! ## `old(global)` in a postcondition names the pre-call value. -/

#guard_msgs (drop info) in
#eval testLaurelVerification <|
#strata
program Laurel;
var count: int := 0
procedure bump()
  opaque
  ensures count == old(count) + 1
{
  count := count + 1
};
procedure caller() opaque {
  count := 5;
  bump();
  assert count == 6
};
#end

/-! ## Conditional preservation without the explicit input `maybe` needs. -/

#guard_msgs (drop info) in
#eval testLaurelVerification <|
#strata
program Laurel;
var g: int := 0
procedure maybeOld(c: bool)
  opaque
  ensures c ==> g == 99
  ensures !c ==> g == old(g)
{
  if c then {
    g := 99
  } else {
    assert true
  }
};
procedure keepsValueOld() opaque {
  g := 5;
  maybeOld(false);
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
var globalCell: GlobalCell := <??>
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

/-! ## `old(global)` in a `throwsOn` case postcondition. -/

#guard_msgs (drop info) in
#eval testLaurelVerification <|
#strata
program Laurel;
composite BumpError {}
var thrownCount: int := 0
procedure bumpThenThrow()
  throws (thrown: BumpError)
  opaque
  throwsOn true {
    ensures thrownCount == old(thrownCount) + 1
  }
{
  thrownCount := thrownCount + 1;
  var err: BumpError := new BumpError;
  throw err
};
procedure catchBumpedGlobal() opaque {
  thrownCount := 7;
  try {
    bumpThenThrow()
  } catch err when err is BumpError {
    assert thrownCount == 8
  };
  assert thrownCount == 8
};
#end

/-! ## `old(g)` in a `throwsOn` guard; exhaustiveness fails if `old` is dropped. -/

#guard_msgs (drop info) in
#eval testLaurelVerification <|
#strata
program Laurel;
composite GuardError {}
var g: int := 0
procedure throwsWhenStartedAtZero()
  throws (e: GuardError)
  requires g == 0
  opaque
  throwsOn old(g) == 0 {
    ensures g == 1
  }
{
  g := 1;
  var err: GuardError := new GuardError;
  throw err
};
#end

/-! ## `old(g)` in a `modifies when` guard; the assert is unprovable if `old`
    is dropped (the wildcard erases the unguarded frame). -/

#guard_msgs (drop info) in
#eval testLaurelVerification <|
#strata
program Laurel;
composite Cell {
  var value: int
}
var g: int := 0
procedure touchGuarded(c: Cell)
  opaque
  modifies *
  modifies c when old(g) == 0
{
  g := 1;
  c#value := 5
};
procedure observeGuardedFrame() opaque {
  var c: Cell := new Cell;
  var d: Cell := new Cell;
  g := 0;
  d#value := 7;
  touchGuarded(c);
  assert d#value == 7
};
#end

/-! ## The pre-state guard binds: writing outside its targets fails the frame. -/

#guard_msgs (drop info) in
#eval testLaurelVerification <|
#strata
program Laurel;
composite Cell {
  var value: int
}
var g: int := 0
procedure breaksGuardedFrame(c: Cell, d: Cell)
//        ^^^^^^^^^^^^^^^^^^ error: modifies clause does not hold
  requires g == 0
  opaque
  modifies *
  modifies c when old(g) == 0
{
  g := 1;
  d#value := 5
};
#end

/-! ## `old` over a composite global's field (heap-`old` path). -/

#guard_msgs (drop info) in
#eval testLaurelVerification <|
#strata
program Laurel;
composite Counter {
  var value: int
}
var counter: Counter := <??>
procedure bumpField()
  opaque
  ensures counter#value == old(counter#value) + 1
  modifies counter
{
  counter#value := counter#value + 1
};
procedure callerField()
  opaque
  modifies counter
{
  counter#value := 5;
  bumpField();
  assert counter#value == 6
};
#end

/-! ## `old(g)` where `g` is written only through a callee. -/

#guard_msgs (drop info) in
#eval testLaurelVerification <|
#strata
program Laurel;
var g: int := 0
procedure inc()
  opaque
  ensures g == old(g) + 1
{
  g := g + 1
};
procedure incViaCall()
  opaque
  ensures g == old(g) + 1
{
  inc()
};
procedure callerVia() opaque {
  g := 10;
  incViaCall();
  assert g == 11
};
#end

/-! ## Known gap: unwritten global makes `old(g)` a silent no-op (`g == g`),
    with no warning when the procedure writes the heap for other reasons. -/

#guard_msgs (drop info) in
#eval testLaurelVerification <|
#strata
program Laurel;
composite Cell {
  var value: int
}
var g: int := 0
procedure readsOnly(c: Cell)
  opaque
  ensures g == old(g)
  modifies c
{
  c#value := 1
};
#end

/-! ## `new` in a global's initializer is rejected

Allocation is a statement, not an expression: `new C` expands into a block that
reads `Heap..nextReference!($heap)` and then assigns `$heap := increment($heap)`. A
file-scope initializer has no statement position to sequence that in and no `$heap`
to sequence it against -- the initializer only reaches one when the globals pass
emits it into an entry procedure's prologue, which happens after `new` is lowered.

Diagnosed rather than left alone because the failure is otherwise silent: the type
flattening at the end of the type-hierarchy pass rewrites the field's declared type
to `Composite` while the initializer still says `new C`, and nothing objects until
something re-resolves the program.

The initializer is optional, so a composite-valued global is still declarable as
`var cell: DiagCell` -- an arbitrary reference, which is what a verification root
quantifies over anyway (see the composite-valued global cases above). -/

#guard_msgs (drop info) in
#eval testLaurelVerification <|
#strata
program Laurel;
composite DiagCell {
  var value: int
}
var diagCell: DiagCell := new DiagCell
//                        ^^^^^^^^^^^^ error: the initializer of file-scope global 'diagCell' must be effect-free (no assignments or declarations, no allocation with 'new', and no calls to heap-reading or heap-writing procedures)
procedure readsIt()
  opaque
{
  assert diagCell#value == diagCell#value
};
#end

/-! ## An entry procedure may use the heap

An `entry` procedure receives its globals as body locals rather than parameters. That
is a problem only for the heap, which is the one global arriving with generated contract
clauses attached: `ModifiesClauses` and `HeapParameterization` produce two-state clauses
naming `$heap` (a frame over `readField(old($heap), …) == readField($heap, …)`, and a
monotonic-pointer `free ensures`), and `ContractPass` extracts every condition into a
helper procedure parameterized by the signature, which a body local can never reach.

`HeapParameterization` therefore skips those clauses for an entry procedure, and
Resolution requires a heap-touching one to declare `modifies *` -- the wildcard is what
stops `ModifiesClauses` building a frame. Without that, the clauses referred to nothing:
`Resolution failed: '$heap' is not defined`, reported as an internal error.

`e` below is the shape that exercises it: an entry procedure that allocates (which is
itself a heap write, see `HeapAnalysis`) and then reads back what it wrote. -/

#guard_msgs (drop info) in
#eval testLaurelVerification <|
#strata
program Laurel;
composite EntryHeapCell { var v: int }
procedure e()
  entry
  opaque
  modifies *
{
  var c: EntryHeapCell := new EntryHeapCell;
  c#v := 1;
  assert c#v == 1
};
#end
