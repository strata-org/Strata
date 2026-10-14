/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import StrataLaurel.Tests.Util.TestLaurel
open StrataTest.Util
open Strata

/-! A constrained field read recovers its range in a LOOP INVARIANT.

    `ConstrainedTypeElim` restates a constrained field's range at each read as a
    value-block `{ assume T$constraint(read); read }`, which covers body and
    postcondition positions. A loop invariant must stay a proposition -- Core
    invariants cannot carry statements, and `LiftImperativeExpressions` deliberately
    refuses to hoist out of a spec position under a binder -- so the block cannot work
    there.

    What makes the invariant below provable is the per-field axiom the same pass
    emits, `forall (o: T) { o#f } => T$constraint(o#f)`, as an `invokeOn` trigger plus
    `ensures` on a generated `$fieldConstraint_T_f`. Being a proposition it holds in
    every position the value-block cannot reach -- a loop invariant here, and across a
    call, which is what lets a transparent procedure's output constraint be checked at
    all.

    The negative twin is what makes this non-vacuous: the axiom supplies the field's
    declared range and nothing beyond it, so a strictly stronger claim must still
    fail. -/
#eval testLaurelVerification <|
#strata
program Laurel;
constrained natInv = x: int where x >= 0 witness 0
composite CtrInv {
  var n: natInv
}
procedure invariantReadGap(c: CtrInv)
  opaque
{
  var i: int := 0;
  while (i < 1)
    invariant c#n >= 0
  {
    i := i + 1
  };
  assert i >= 0
};

// Must-fail twin: `natInv` bounds `n` below, not above.
procedure invariantReadNoUpperBound(c: CtrInv)
  opaque
{
  var i: int := 0;
  while (i < 1)
    invariant c#n <= 100
//            ^^^^^^^^^^ error: assertion could not be proved
  {
    i := i + 1
  };
  assert i >= 0
};
#end
