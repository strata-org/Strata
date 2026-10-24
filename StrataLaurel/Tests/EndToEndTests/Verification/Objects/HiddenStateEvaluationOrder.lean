/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import StrataLaurel.Tests.Util.TestLaurel

open StrataTest.Util
open Strata

/-! A heap-writing call as an argument to a heap-reading call: `peek` samples
    the heap after `bump` ran, so it sees 1 while receiving bump's return 0. -/

#guard_msgs (drop info) in
#eval testLaurelVerification <|
#strata
program Laurel;
composite Counter {
  var value: int
}
procedure bump(c: Counter) returns (r: int)
  opaque
  ensures c#value == old(c#value) + 1
  ensures r == old(c#value)
  modifies c
{
  c#value := c#value + 1;
  return c#value - 1
};
procedure peek(c: Counter, x: int) returns (r: int)
  opaque
  ensures r == c#value * 10 + x;
procedure evaluationOrder(c: Counter)
  opaque
  modifies c
{
  c#value := 0;
  var got: int := peek(c, bump(c));
  assert got == 10;
  assert c#value == 1
};
#end

/-! An effectful cast target is captured once, then reused for the type check and
    result. Evaluating `makeBase` twice would increment `counter#value` twice. -/

#guard_msgs (drop info) in
#eval testLaurelVerification <|
#strata
program Laurel;
composite Base {
}
composite Counter {
  var value: int
}
procedure makeBase(counter: Counter) returns (r: Base)
  opaque
  ensures counter#value == old(counter#value) + 1
  ensures r is Base
  modifies counter
{
  counter#value := counter#value + 1;
  return new Base
};
procedure castOnce(counter: Counter)
  opaque
  modifies counter
{
  counter#value := 0;
  var result: Base := makeBase(counter) as Base;
  assert result is Base;
  assert counter#value == 1
};
#end

/-! The same capture-once guarantee on a HEAP-NEUTRAL procedure. `castOnceNeutral`
    neither reads nor writes the heap, so its body is lowered by `lowerAsTypeNodesOnly`
    rather than the heap-threading `heapTransformExpr` — a distinct `AsType` lowering
    path. The cast target `{ x := x - 1; cc }` is a compound with a local side effect
    (this pass runs before imperative lifting), which must still run EXACTLY ONCE: `x`
    goes 2 → 1, so the postcondition-free body's `assert x == 1` holds. If the target
    were embedded twice `x` would reach 0. The `is Child` guard discharges the cast's
    own `is`-check cleanly, isolating the evaluation-count property. -/

#guard_msgs (drop info) in
#eval testLaurelVerification <|
#strata
program Laurel;
composite Parent { var p: int }
composite Child extends Parent { var q: int }
procedure castOnceNeutral(cc: Parent)
  opaque
{
  var x: int := 2;
  if (cc is Child) then {
    var d: Child := { x := x - 1; cc } as Child;
    assert x == 1
  }
};
#end

/-! The must-fail twin pins the evaluation COUNT, not just that some value flows through:
    with a single evaluation `x == 0` is false and is correctly reported. Embedding the cast
    target twice would run it twice, driving `x` to 0 and spuriously verifying this false
    assertion — that is the property this twin guards. -/

#guard_msgs (drop info) in
#eval testLaurelVerification <|
#strata
program Laurel;
composite Parent { var p: int }
composite Child extends Parent { var q: int }
procedure castOnceNeutralFalse(cc: Parent)
  opaque
{
  var x: int := 2;
  if (cc is Child) then {
    var d: Child := { x := x - 1; cc } as Child;
    assert x == 0
//  ^^^^^^^^^^^^^ error: assertion does not hold
  }
};
#end

/-! The capture-once lowering also reaches a heap-neutral TRANSPARENT body (no `opaque`).
    Unlike the opaque cases above (whose implementation lowers via `translateStmt`), a
    transparent body is ALSO emitted as a pure `$asFunction` twin — translated by
    `translateExpr` in pure context — so the fresh `.Declare` the capture introduces must
    survive that pure translation. `tagOf`'s cast target `c as Parent` is pure, so `tagOf`
    returns its argument `n` unchanged and the caller's `tagOf(c, 7) == 7` verifies; this
    would fail to translate at all if the capture temp were rejected in the function twin. -/

#guard_msgs (drop info) in
#eval testLaurelVerification <|
#strata
program Laurel;
composite Parent { var p: int }
composite Child extends Parent { var q: int }
procedure tagOf(c: Child, n: int) returns (r: int)
{
  var a: Parent := (c as Parent);
  return n
};
procedure caller(c: Child)
  opaque
{
  assert tagOf(c, 7) == 7
};
#end

/-! Must-fail twin for the transparent-body cast: a wrong expectation is still reported,
    confirming the function twin carries the real return value through the lowered cast. -/

#guard_msgs (drop info) in
#eval testLaurelVerification <|
#strata
program Laurel;
composite Parent { var p: int }
composite Child extends Parent { var q: int }
procedure tagOf(c: Child, n: int) returns (r: int)
{
  var a: Parent := (c as Parent);
  return n
};
procedure caller(c: Child)
  opaque
{
  assert tagOf(c, 7) == 8
//^^^^^^^^^^^^^^^^^^^^^^^ error: assertion does not hold
};
#end

/-! An `as`-cast in an out-of-body SPEC field of a HEAP-NEUTRAL procedure (here a
    precondition) is lowered by the same `mapProcedureSpecificationsM` routing the
    heap-active branch uses — so it reaches the encoder rather than being skipped and
    hard-failing at `LaurelToCoreSchemaPass`'s `AsType` arm. The cast `(c as Parent)#p`
    is pure, so its lowered `is`-check is discharged; the assumed precondition then makes
    the body's `assert` hold. (A cast in a contract-CONDITION position remains limited by
    the pipeline-wide "asserts in contracts" gap — see the note in `HeapParameterization`;
    a precondition read like this one lowers cleanly.) -/

#guard_msgs (drop info) in
#eval testLaurelVerification <|
#strata
program Laurel;
composite Parent { var p: int }
composite Child extends Parent { var q: int }
procedure usePre(c: Child)
  requires ((c as Parent)#p == 5)
  opaque
{
  assert (c as Parent)#p == 5
};
#end

/-! Must-fail twin: the precondition is genuinely ASSUMED (not dropped) — asserting a
    value it contradicts fails via a solver verdict, so the valid case above is not
    vacuous. -/

#guard_msgs (drop info) in
#eval testLaurelVerification <|
#strata
program Laurel;
composite Parent { var p: int }
composite Child extends Parent { var q: int }
procedure usePre(c: Child)
  requires ((c as Parent)#p == 5)
  opaque
{
  assert (c as Parent)#p == 6
//^^^^^^^^^^^^^^^^^^^^^^^^^^^ error: assertion does not hold
};
#end

/-! A field store evaluates its receiver, then its value, and samples the heap after
    both: `flip(p, q)#b := false` keeps the write `flip` makes to `q`, and the store to
    `a#r#b` goes to the box `a#r` held before `setR` replaced it. A field read samples
    the heap after its receiver: `{ setB(p); p }#b` reads the `true` that `setB` wrote.
    An update operator evaluates its receiver once: `{ i := i + 1; x }#g += 2` adds 1 to
    `i`. -/
#guard_msgs (drop info) in
#eval testLaurelVerification <|
#strata
program Laurel;
composite Box {
  var b: bool
  var g: int
}
composite A {
  var r: Box
}
procedure flip(p: Box, q: Box) returns (o: Box)
  opaque
  ensures q#b && o == p
  modifies q
{
  q#b := true;
  return p
};
procedure setR(a: A, c: Box) returns (o: bool)
  opaque
  ensures a#r == c && o
  modifies a
{
  a#r := c;
  return true
};
procedure storeKeepsTheReceiversWrite()
  opaque
{
  var p: Box := new Box;
  var q: Box := new Box;
  q#b := false;
  flip(p, q)#b := false;
  assert q#b
};
procedure storeEvaluatesTheReceiverBeforeTheValue()
  opaque
{
  var a: A := new A;
  var b0: Box := new Box;
  var c: Box := new Box;
  a#r := b0;
  b0#b := true;
  c#b := true;
  a#r#b := setR(a, c) && false;
  assert !b0#b && c#b
};
procedure setB(q: Box)
  opaque
  ensures q#b
  modifies q
{
  q#b := true
};
procedure readSamplesTheHeapAfterItsReceiver()
  opaque
{
  var p: Box := new Box;
  p#b := false;
  var r: bool := { setB(p); p }#b;
  assert r
};
procedure updateOperatorEvaluatesTheReceiverOnce()
  opaque
{
  var i: int := 0;
  var x: Box := new Box;
  x#g := 0;
  { i := i + 1; x }#g += 2;
  { i := i + 1; x }#g++;
  assert i == 2 && x#g == 3
};
#end

/-! A loop condition reads through its receiver's current object each time it is tested, also
    where the receiver has an effect: the loop below ends, so the assertion after it is reported.
    This guards that a receiver in a loop's condition is not bound once before the loop. -/
#guard_msgs (drop info) in
#eval testLaurelVerification <|
#strata
program Laurel;
composite Box {
  var g: int
}
procedure assignInAReceiverInALoopCondition()
  opaque
{
  var a: Box := new Box;
  var c: Box := new Box;
  a#g := 1;
  c#g := 0;
  var i: int := 0;
  var x: Box := a;
  while ({ i := i + 1; x }#g > 0)
    invariant x == a || x == c
  {
    x := c
  };
  assert false
//^^^^^^^^^^^^ error: assertion could not be proved
};
#end

/-! A store in a loop's condition stays outside its receiver when the stored value names a local
    the receiver declares: here the value's `k` is the global, which a store moved into the `if`'s
    branch would read as the branch's `k`. -/
#eval testLaurelVerification <|
#strata
program Laurel;
var k: int := 5
composite P {
  var f: int
}
procedure conditionStoreKeepsAValueThatNamesItsReceiversLocal(p: P, b: bool)
  opaque
  modifies p
{
  while (((if b then { var k: int := 1; p } else p)#f := k) < 0) {
  };
  assert p#f == k;
  assert p#f == 1
//^^^^^^^^^^^^^^^ error: assertion could not be proved
};
#end

/-! In a loop's condition a read through a call follows the store in the call's argument, on an
    unconstrained field too: the condition reads 5, so the body runs. -/
#eval testLaurelVerification <|
#strata
program Laurel;
composite P {
  var f: int
}
procedure pick(q: P) returns (r: P)
{
  r := q
};
procedure conditionReadsThroughACallAfterItsArgumentStores(p: P)
  opaque
  modifies p
{
  p#f := 3;
  while (pick({ p#f := 5; p })#f == 5) {
    assert 1 == 2
//  ^^^^^^^^^^^^^ error: assertion could not be proved
  }
};
#end
