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
