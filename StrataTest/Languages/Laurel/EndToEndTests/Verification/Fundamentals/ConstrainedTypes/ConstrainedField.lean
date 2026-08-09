/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

/-
Test: constrained types as composite fields. Verifies that heap
parameterization resolves constrained types to their base type for boxing,
and that constraint checks are asserted on field writes.

Constraints are also recovered when *reading* a constrained field
(`readCountRecoversConstraint`); the remaining loop-invariant case is pinned by
`ConstrainedFieldInvariantGap`.
-/

import StrataTest.Util.TestLaurel

open StrataTest.Util
open Strata

#eval testLaurelVerification
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

// The same recovery on the OUTPUT path, which is the case the pass exists for: a
// constrained output's range obligation is an `ensures` (added by `elimProc`), not the
// local `assert` above, so the read's assume has to be visible to the postcondition
// check rather than only to a statement in the body. Non-vacuous independently of
// `readCountRecoversConstraint`: this procedure fails if the read assume is removed from
// `elimNode`, so the ensures obligation is emitted and is discharged by the assume.
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
// the two procedures pin both directions of the ensures path.
//
// The caret sits on the OUTPUT TYPE, not on the `return`: `elimProc` generates the range
// check as an `ensures` whose source is the constrained output's type, so that is where
// the failure is reported (measured: 58-61 on the signature line).
procedure readAndReturnOutOfRange(c: Counter) returns (r: nat)
//                                                        ^^^ error: postcondition could not be proved
  opaque
{
  return c#count - 1
};
#end
