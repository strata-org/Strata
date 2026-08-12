/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
import StrataTest.Util.TestLaurel

open StrataTest.Util
open Strata

/-! ## `ignoreAssumes` path exercised under concrete execution

`assume false` is a no-op during interpretation (`ignoreAssumes := true`), so
execution proceeds past it and the subsequent `assert true` succeeds. If
`ignoreAssumes` regressed, the interpret path would throw
`assume (…) condition is false` as a non-assertion error and the build would
fail.

Both blocks run through `Core.Program.interpretEntries`, the same entry point the
`laurelInterpret` CLI command uses, so these also pin the CLI's behaviour. -/

#guard_msgs (drop info) in
#eval testLaurelMultiple <|
#strata
program Laurel;
procedure ignoresAssume() entry opaque {
  assume false;
  assert true
};
#end

/-! ### An ignored assume must not swallow later assertion failures

The block above uses a hand-written `assume`. This one covers the case the
`laurelInterpret` CLI actually hits: an assume the *translator* inserts. Under
`.Execute` mode a callee's `requires` is assumed at the top of its own body, so
calling `mustNotBeCalled` puts an `assume false` on the interpreter's path even
though the Laurel source contains no `assume` at all.

Both failures below must be reported. That pins two things at once: the inserted
assume is skipped rather than halting the run, and skipping it does not make the
rest of the caller vacuous — the `assert` after the call is still evaluated and
still fails. Were `ignoreAssumes` to regress, the interpreter would stop inside
`mustNotBeCalled` and the second annotation would never fire. -/

#eval testLaurelMultiple <|
#strata
program Laurel;
procedure mustNotBeCalled()
  requires false
  opaque
{
};

procedure assumeDoesNotMaskAsserts()
  entry
  opaque
{
  mustNotBeCalled();
//^^^^^^^^^^^^^^^^^ error: precondition does not hold
  assert 1 == 2
//^^^^^^^^^^^^^ error: assertion does not hold
};
#end
