/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import StrataTest.Util.TestLaurel

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
#eval testLaurelExecution {} <|
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
#eval testLaurelExecution {} <|
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
//  ^^^^^^^^^^^^^ error: assertion could not be proved
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
#eval testLaurelExecution {} <|
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
#eval testLaurelExecution {} <|
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
#eval testLaurelExecution {} <|
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
#eval testLaurelExecution {} <|
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
