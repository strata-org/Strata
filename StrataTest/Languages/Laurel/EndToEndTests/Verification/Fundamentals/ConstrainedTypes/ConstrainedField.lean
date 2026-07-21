/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

/-
Test: constrained types as composite fields. Verifies that heap
parameterization resolves constrained types to their base type for boxing,
and that constraint checks are asserted on field writes.

Also documents a known completeness gap: constraints are NOT recovered when
*reading* a constrained field (see `readCountCompletenessGap`). To be fixed
in a follow-up PR by assuming the constraint on field reads and maintaining
it across havoc/modifies.
-/

import StrataTest.Util.TestLaurel

open StrataTest.Util
open Strata

#eval testLaurel
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

// KNOWN COMPLETENESS GAP (to be fixed in a follow-up PR):
// Reading a constrained-typed field does NOT recover its constraint. Because
// HeapParameterization boxes the field as its unconstrained base type (BoxInt),
// and there is no `assume constraint` inserted on field reads, a legitimately
// constructed `nat` field cannot be relied upon as `>= 0` after a read through
// a heap parameter. The assertion below is true in principle but currently
// unprovable. (Note: the same pattern on a *local* `nat` variable verifies
// fine, because uninitialized constrained locals get an `assume constraint`.)
procedure readCountCompletenessGap(c: Counter)
  opaque
{
  var x: int := c#count;
  assert x >= 0
//^^^^^^^^^^^^^ error: assertion could not be proved
};
#end
