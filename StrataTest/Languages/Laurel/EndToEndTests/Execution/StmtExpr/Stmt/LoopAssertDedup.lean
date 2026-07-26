/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import StrataTest.Util.TestLaurel

open StrataTest.Util
open Strata

/-! ## An assert re-hit across iterations is reported once

The failing `assert false` lives at the top of the helper `alwaysFails`, which
the loop in `runsItThrice` calls on each of the three iterations.

* The **interpreter** runs the loop concretely, so it enters `alwaysFails` three
  times and records three *identical* assertion failures (same label, range, and
  message). Carrying those failures back out of each call exercises the callee →
  caller `assertFailures` propagation in `Command.runCall`; collapsing the
  identical diagnostics exercises the exact-duplicate deduplication in
  `runLaurelInterpretCore`. Without the dedup the interpret path would surface
  three diagnostics at one range and fail `checkAgainstAnnotations`.
* The **verifier** checks `alwaysFails` once (the `assert false` is top-level and
  always-false-and-reachable, so it is worded `does not hold`, not
  `could not be proved`); the call site inside the loop is abstracted by the
  callee's contract and not re-checked.

Both paths therefore land on the single annotation below.

The failing assert is deliberately in a *called* procedure rather than directly
in the loop body: an assert inside a loop body is checked at the havoc'd loop
head, where the verifier cannot establish concrete reachability and falls back to
`could not be proved`, which the interpret path's `does not hold` can never match
(see the wording note on `testLaurelMultiple`). -/

#eval testLaurelMultiple <|
#strata
program Laurel;
procedure alwaysFails()
  opaque
{
    assert false
//  ^^^^^^^^^^^^ error: assertion does not hold
};

procedure runsItThrice()
  entry
  opaque
{
    var i: int := 0;
    while(i < 3)
      invariant i >= 0
    {
        alwaysFails();
        i := i + 1
    }
};
#end
