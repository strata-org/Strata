/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

/-
Test: constrained types as composite fields. Verifies that heap
parameterization resolves constrained types to their base type for boxing,
and that constraint checks are asserted on field writes.

Constraints are also recovered when *reading* a constrained field
(`readCountRecoversConstraint`); the loop-invariant case is pinned by
`ConstrainedFieldInvariant`.
-/

import StrataLaurel.Tests.Util.TestLaurel

open StrataTest.Util
open Strata

#eval testLaurelVerification <|
#strata
program Laurel;

constrained nat = x: int where x >= 0 witness 0

composite Counter {
  var count: nat
}

procedure setCount(c: Counter)
  opaque
  ensures c#count >= 0
  modifies c
{
  c#count := 1
};

// Error: assigning -1 to a nat field violates the constraint
procedure setCountInvalid(c: Counter)
  opaque
  modifies c
{
  c#count := -1
//^^^^^^^^^^^^^ error: assertion could not be proved
};

// SOUNDNESS REGRESSION (Fabio Madge, PR #1364):
// The field-write constraint check must assert on a read-back of the field,
// not on the RHS `value`. The RHS is already emitted as the field-write
// statement, so asserting the constraint on `value` re-emits it and runs any
// side effect in the RHS twice. With the buggy version, `x := x + 1` inside
// the stored value ran twice (x: 0 -> 2) for the legal write below; the
// read-back fix evaluates the RHS exactly once (x: 0 -> 1). Verifying that
// `x == 1` (and not 2) after the write confirms the RHS is evaluated once.
// This passes non-vacuously: `x` is a plain local int, so its value is tracked
// precisely (no heap read involved), and were the double-evaluation bug
// reintroduced this assertion would fail.
procedure fieldWriteEvaluatesRhsOnce(c: Counter)
  opaque
  modifies c
{
  var x: int := 0;
  c#count := (x := x + 1) + 1;
  assert x == 1
};

// Reading a constrained-typed field RECOVERS its constraint. The declared type is
// lowered to its base (`HeapParameterization` boxes it as `BoxInt`) and
// `ConstrainedTypeElim` restates the predicate as an assumed fact at each read, so a
// legitimately constructed `nat` field can be relied upon as `>= 0`.
//
// Assumed, not asserted, and resting on the DECLARED type -- the standing assumption
// an uninitialized constrained local gets -- not on checked writes: `elimNode` asserts
// only on `.Assign` targets, and a freshly allocated composite's fields are never
// assigned, yet a read of one still satisfies the constraint. `IncrDecr` and
// `CompoundAssign` do not bypass that check: both lower to `.Assign` before this pass,
// so `c#count -= 5` on a `nat` field fails its range assert like a plain write.
procedure readCountRecoversConstraint(c: Counter)
  opaque
{
  var x: int := c#count;
  assert x >= 0
};

// The same recovery on the OUTPUT path, which is the case the pass exists for: the
// `return` is an assignment to the constrained output `r`, so its range obligation is
// asserted at the return, and again by the generated `ensures`. Non-vacuous independently of `readCountRecoversConstraint`:
// this procedure fails if the read assume is removed from `elimNode`, so the obligation
// is emitted and is discharged by the assume.
procedure readAndReturn(c: Counter) returns (r: nat)
  opaque
{
  return c#count
};

// NEGATIVE CONTROL for the procedure above. `readAndReturn` proves an `ensures` from an
// assumed fact, so on its own it cannot distinguish "the obligation is discharged" from
// "no obligation was emitted" -- a change that dropped the constrained-output `ensures`
// entirely would leave it green. Here the returned value is out of range for `nat` on a
// path the assume cannot rescue, so the obligation must exist and must fail. Together
// the two procedures pin both directions of the output check.
//
// Both checks fail: the `return` reaches `elimProc` as an assignment to `r`, checked
// there, and the generated `ensures` is checked on the output type.
procedure readAndReturnOutOfRange(c: Counter) returns (r: nat)
//                                                        ^^^ error: postcondition could not be proved
  opaque
{
  return c#count - 1
//^^^^^^^^^^^^^^^^^^ error: assertion could not be proved
};
#end

/-! Two composites whose names overlap once a separator is inserted: `A_b` with field `c`
    and `A` with field `b_c`. -/
#eval testLaurelVerification <|
#strata
program Laurel;
constrained nat = x: int where x >= 0 witness 0
composite A_b { var c: nat }
composite A { var b_c: nat }
procedure readsBothFields(x: A_b, y: A)
  opaque
{
  assert x#c >= 0;
  assert y#b_c >= 0
};
#end

#eval testLaurelVerification
    (options := { verifyOptions := { Core.VerifyOptions.quiet with solver := "z3" } }) <|
#strata
program Laurel;

constrained nat = x: int where x >= 0 witness 0

composite Counter {
  var count: nat
}

procedure getCount(c: Counter) : nat
{
  return c#count
};

procedure readQuantifiedField(c: Counter, d: Counter)
  requires forall(o: Counter) => o#count > 3
  opaque
{
  assert d#count > 3
};
#end

/-! A constrained field's receiver is evaluated once, read or stored: `{ i := i + 1; c }#count`
    increments `i` once either way. ConstrainedTypeElim reads a store used as a value back from the
    object stored to, also where the store replaces its own receiver (`x#r#r := v` stores into `x`
    when `x#r` is `x`, which guards that a store's own target counts as a change), and a store is
    checked on that object. A receiver that declares a local is not repeated: the store through one is checked,
    and the read through one in a transparent body holds. -/
#eval testLaurelVerification <|
#strata
program Laurel;

constrained nat = x: int where x >= 0 witness 0

composite Counter {
  var count: nat
}

composite Node {
  var r: Node
}

procedure readEvaluatesAnEffectfulReceiverOnce(c: Counter)
  opaque
{
  var i: int := 0;
  var r: int := { i := i + 1; c }#count;
  assert i == 1 && r >= 0
};

procedure storeEvaluatesAnEffectfulReceiverOnce(c: Counter)
  opaque
  modifies c
{
  var i: int := 0;
  { i := i + 1; c }#count := 9;
  assert i == 1
};

procedure storeThatReplacesItsReceiverIsTheValueStored()
  opaque
{
  var x: Node := new Node;
  var v: Node := new Node;
  var w: Node := new Node;
  x#r := x;
  v#r := w;
  var res: Node := x#r#r := v;
  assert res == v && x#r == v
};

procedure readThroughADeclaringReceiverInATransparentBody(c: Counter) returns (r: int)
{
  r := { var t: Counter := c; t }#count
};

procedure callsTheTransparentBody(c: Counter)
  opaque
{
  assert readThroughADeclaringReceiverInATransparentBody(c) == c#count
};

procedure storeThroughADeclaringReceiverIsChecked(c: Counter)
  opaque
  modifies c
{
  { var t: Counter := c; t }#count := -1
//^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ error: assertion could not be proved
};
#end

/-! A read through a receiver of a constrained composite type checks nothing about the receiver,
    whose constraint a store into the object may have broken, also where the receiver is bound:
    this guards that a bound receiver's local is typed at the field's owner, `Box`, rather than at
    `CB`. -/
#eval testLaurelVerification <|
#strata
program Laurel;

composite Box {
  var v: int
}

constrained CB = b: Box where b#v >= 0 witness <??>
//                                             ^^^^ error: assertion does not hold

procedure readThroughABrokenConstraint(c: CB)
  opaque
  modifies *
{
  c#v := 0 - 5;
  var i: int := 0;
  var r: int := { i := i + 1; c }#v;
  assert i == 1 && r == 0 - 5
};
#end

/-! In a loop's condition, where receivers stay unbound, an access follows its receiver's
    statements, also through an `if`, a one-argument call or a cast: `{ i := i + 1; c }#count`
    counts once in a read, a store or an update operator, and `{ var t: Counter := c; t }#count`
    declares `t` once. Invariants, also a `goto` loop's, are bound like the body, so an invariant
    can read through a call or a cast. -/
#eval testLaurelVerification <|
#strata
program Laurel;

constrained nat = x: int where x >= 0 witness 0

composite Counter {
  var count: nat
}

procedure conditionStoresThroughItsReceiverOnce(c: Counter)
  opaque
  modifies c
{
  var i: int := 0;
  while (({ i := i + 1; c }#count := 1) > 5) {
  };
  assert i == 1;
  while (({ i := i + 1; c }#count += 1) > 5) {
  };
  assert i == 2;
  while (({ var u: Counter := c; u }#count := { var m: int := 3; m }) > 5) {
  };
  assert c#count == 3;
  while (({ var t: Counter := c; t }#count := 0 - 1) > 5) {
//        ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ error: assertion could not be proved
  }
};

procedure conditionIncrementsThroughItsReceiverOnce(c: Counter)
  opaque
  modifies c
{
  c#count := 3;
  var i: int := 0;
  while (({ i := i + 1; c }#count++) > 5) {
  };
  assert i == 1 && c#count == 4;
  assert i != 1
//^^^^^^^^^^^^^ error: assertion could not be proved
};

procedure conditionEvaluatesAnIfReceiverOnce(c: Counter, b: bool)
  opaque
  modifies c
{
  c#count := 3;
  var i: int := 0;
  while ((if b then { i := i + 1; c } else { i := i + 1; c })#count > 5) {
  };
  assert i == 1;
  assert i != 1
//^^^^^^^^^^^^^ error: assertion could not be proved
};

procedure pick(c: Counter) returns (r: Counter)
{
  r := c
};

procedure conditionEvaluatesACallOrCastReceiverOnce(c: Counter)
  opaque
  modifies c
{
  c#count := 3;
  var i: int := 0;
  while (pick({ i := i + 1; c })#count > 5) {
  };
  assert i == 1;
  while (pick({ c#count := c#count + 1; c })#count > 5) {
  };
  assert c#count == 4;
  while (({ i := i + 1; c } as Counter)#count > 5) {
  };
  assert i == 2;
  while (pick({ var u: Counter := c; u })#count > 5) {
  };
  assert i != 2
//^^^^^^^^^^^^^ error: assertion could not be proved
};

procedure conditionAndInvariantThroughADeclaringReceiver(c: Counter)
  opaque
  modifies c
{
  c#count := 3;
  var j: int := 0;
  while ({ var t: Counter := c; t }#count > j)
    invariant { var t: Counter := c; t }#count == 3
  {
    j := j + 1
  };
  assert c#count == 3;
  assert c#count != 3
//^^^^^^^^^^^^^^^^^^^ error: assertion could not be proved
};

procedure invariantsReadThroughACallOrACast(c: Counter)
  opaque
  modifies c
{
  c#count := 0;
  var n: int := 0;
  while (n < 3)
    invariant pick(c)#count == 0 && (c as Counter)#count == 0 && 0 <= n && n <= 3
  {
    n := n + 1
  };
  {
    if (n >= 6) then { exit loop };
    n := n + 1;
    goto loop
  } loop
    invariant pick(c)#count == 0 && (c as Counter)#count == 0 && 3 <= n && n <= 6;
  while (n < 9)
    invariant pick(c)#count == 1
//            ^^^^^^^^^^^^^^^^^^ error: assertion could not be proved
  {
    n := n + 1
  }
};

procedure gotoLoopEvaluatesItsReceiversOnce(c: Counter)
  opaque
  modifies c
{
  c#count := 0;
  var i: int := 0;
  var n: int := 0;
  {
    if (n >= 3) then { exit loop };
    var r: int := { i := i + 1; c }#count;
    n := n + 1;
    goto loop
  } loop
    invariant { var t: Counter := c; t }#count == 0 && 0 <= n && n <= 3 && i == n;
  assert i == 3;
  assert i != 3
//^^^^^^^^^^^^^ error: assertion could not be proved
};
#end
