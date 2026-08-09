/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import StrataTest.Util.TestLaurel
open StrataTest.Util
open Strata

/-! A constrained field read inside a LOOP INVARIANT does not recover its range.

    `ConstrainedTypeElim` restates a constrained field's range at each read as a
    value-block `{ assume T$constraint(read); read }`, covering body and postcondition
    positions. A loop invariant must stay a proposition -- Core invariants cannot
    carry statements, and `LiftImperativeExpressions` deliberately refuses to hoist
    out of a spec position under a binder -- so the block cannot work there.

    COMPLETENESS gap only, failing loudly: the assertion below is true in principle
    (`n` is a `nat`) but unprovable, so a clear diagnostic, never a false green.
    Verified not an internal error.

    Closing it wants a heap-quantified axiom per constrained field --
    `forall (o: T) { o#f } => T$constraint(o#f)` -- which covers every position at
    once, rewrites no user-authored expression, and being a proposition holds where
    the value-block cannot. -/
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
//            ^^^^^^^^ error: assertion does not hold
  {
    i := i + 1
  };
  assert i >= 0
};
#end
