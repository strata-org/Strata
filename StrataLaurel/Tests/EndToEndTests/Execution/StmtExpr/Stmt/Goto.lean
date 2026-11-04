/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
import StrataLaurel.Tests.Util.TestLaurel

open StrataTest.Util
open Strata

/-! # `goto`: jumping back to the start of a labelled block

A `goto L` re-enters the enclosing block labelled `L`, re-checking its
invariants, which makes the block a loop. `exit L` still leaves it. -/

#eval testLaurelExecution {} <|
#strata
program Laurel;
procedure postTested()
  entry
  opaque
{
    var i: int := 0;
    {
        i := i + 1;
        if (i < 3) then { goto again }
    } again
      invariant 0 <= i && i <= 2;
    assert i == 3
};

procedure preTested()
  entry
  opaque
{
    var n: int := 4;
    var i: int := 0;
    {
        if (i >= n) then { exit loop };
        i := i + 1;
        goto loop
    } loop
      invariant 0 <= i && i <= n;
    assert i == n
};

procedure nested()
  entry
  opaque
{
    var i: int := 0;
    var j: int := 0;
    {
        j := 0;
        {
            if (j >= 2) then { exit inner };
            j := j + 1;
            goto inner
        } inner
          invariant 0 <= j && j <= 2;
        i := i + 1;
        if (i < 3) then { goto outer }
    } outer
      invariant 0 <= i && i <= 2;
    assert i == 3;
    assert j == 2
};

procedure gotoOuterFromInner()
  entry
  opaque
{
    var i: int := 0;
    {
        {
            i := i + 1;
            if (i < 5) then { goto outer }
        } inner
    } outer
      invariant 0 <= i && i <= 4;
    assert i == 5
};
#end

/-! The invariants are checked on every jump back, not only on entry. The
verifier cannot prove the invariant is preserved; the Laurel interpreter sees it
fail on the first jump back. -/

-- Verification only: the Laurel interpreter's verdict differs (below), and the Core interpreter does not check loop invariants.
#eval testLaurelExecution { skipCoreInterpreter := true, skipLaurelInterpreter := true } <|
#strata
program Laurel;
procedure brokenOnJumpBack()
  opaque
{
    var i: int := 0;
    {
        i := i + 2;
        if (i < 4) then { goto again }
    } again
      invariant i <= 1
//              ^^^^^^ error: assertion could not be proved
};

procedure runAll()
  entry
  opaque
{
    brokenOnJumpBack()
};
#end

-- No Core interpreter: it does not check loop invariants, so the annotated invariant failure never fires.
#eval testLaurelExecution { skipVerification := true, skipCoreInterpreter := true } <|
#strata
program Laurel;
procedure brokenOnJumpBack()
  opaque
{
    var i: int := 0;
    {
        i := i + 2;
        if (i < 4) then { goto again }
    } again
      invariant i <= 1
//              ^^^^^^ error: assertion does not hold
};

procedure runAll()
  entry
  opaque
{
    brokenOnJumpBack()
};
#end

/-! A block with invariants that no `goto` targets checks them once, on entry. -/

#eval testLaurelExecution {} <|
#strata
program Laurel;
procedure checkedOnEntry()
  opaque
{
    var i: int := 1;
    {
        i := i + 1
    } once
      invariant i == 0
//              ^^^^^^ error: assertion does not hold
};

procedure runAll()
  entry
  opaque
{
    checkedOnEntry()
};
#end

/-! A `goto` that leaves a `try` runs its `finally` on the way back.

Execution only: loop elimination havocs the `$thrown` flag `EliminateExceptions`
introduces, so the verifier cannot prove that no exception escapes the `try`.
That is not specific to `goto` — a `while` around the same `try` fails the same
way. -/

#eval testLaurelExecution { skipVerification := true } <|
#strata
program Laurel;
procedure throughFinally()
  entry
  opaque
{
    var i: int := 0;
    var cleanups: int := 0;
    {
        try {
            i := i + 1;
            if (i < 3) then { goto again }
        } finally {
            cleanups := cleanups + 1
        }
    } again
      invariant 0 <= i && i <= 3 && cleanups == i;
    assert cleanups == 3
};
#end

/-! A runaway backward jump stops on the Laurel interpreter's step budget. -/

-- Laurel interpreter only: the Core interpreter reports divergence as "failed to terminate".
/-- error: out of fuel
-/
#guard_msgs in
#eval testLaurelExecution { skipVerification := true, skipCoreInterpreter := true } <|
#strata
program Laurel;
procedure spin()
  entry
  opaque
{
  var i: int := 0;
  {
    i := i + 1;
    goto forever
  } forever
};
#end
