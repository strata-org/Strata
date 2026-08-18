/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import StrataTest.Util.TestLaurel

open StrataTest.Util
open Strata

/-
`try` / `finally` + `throw`: the `finally` arm and the unwinding rules, with no
calls involved. Handler *selection* is `TryCatchThrow.lean`; the smoke test for
the whole shape is `TryCatchThrow.lean`.

These tests assert *observable outcomes* of the lowered control flow rather than
just that the construct lowers:
  * `finally` runs on every way out of the `try` — fall-through, a caught
    exception, an early `return`, and an `exit` to an enclosing label — and on each
    arm it crosses when the arms nest;
  * abrupt completion of a `finally` *supersedes* the completion pending from the
    body (Java JLS §14.20.2), so a `return` in a `finally` swallows an in-flight
    `throw` and a `throw` in a `finally` discards a pending `return`;
  * a swallowed throw needs no `throws` declaration, since nothing escapes.

The `return` and `exit` cases are the reason the lowering carries `$returning` and
`$exiting_<label>` alongside `$thrown`: each is a pending completion that has to
survive the arms it unwinds through.

Exceptions are constructed *before* the `try` (a `new` inside a `try` body hits a
known lifting-pass gap), and all throws are direct so the verifier knows each
value's runtime type and can discharge the `is`-guards precisely.

Using `testLaurelExecution` but skiping the Core interpreter test path: a thrown
exception is a composite value and the interpret path does not support the heap yet.
Where a construct can be exercised without the heap it is run both ways instead; see
`TryCatchThrow.lean`.
-/

-- `finally` runs on both the normal (no-throw) and the caught-exception paths.
-- `doThrow` is a symbolic input, so the verifier checks both.
#eval testLaurelExecution {} <|
#strata
program Laurel;
composite Exception {}
procedure finallyAlwaysRuns(doThrow: bool)
  returns (r: int)
  opaque
{
  var e: Exception := new Exception;
  var ran: int := 0;
  try {
    if doThrow then {
      throw e
    };
    r := 1
  } catch c {
    r := 2
  } finally {
    ran := 99
  };
  assert ran == 99
};
#end
-- `finally` runs on an early `return` out of the try body: the return
-- unwinds through the `try`, so `finally` sets `ran := 99` before the procedure
-- exits, and the statement after the `try` is skipped.
#eval testLaurelExecution {} <|
#strata
program Laurel;
procedure earlyReturnRunsFinally()
  returns (ran: int)
  opaque
  ensures ran == 99
{
  ran := 0;
  try {
    return
  } finally {
    ran := 99
  };
  ran := 7
};
#end

-- A `return` in the try body skips the `catch` (no exception is in flight) but
-- still runs `finally`: the handler's `r := 1` does not fire; `finally` sets
-- `r := 5`.
#eval testLaurelExecution {} <|
#strata
program Laurel;
procedure returnSkipsCatchRunsFinally()
  returns (r: int)
  opaque
  ensures r == 5
{
  r := 0;
  try {
    return
  } catch c {
    r := 1
  } finally {
    r := 5
  }
};
#end

-- Nested try/finally: a `return` in the innermost body runs both `finally` arms
-- on the way out (inner then outer), so `log` ends at 3.
#eval testLaurelExecution {} <|
#strata
program Laurel;
procedure nestedReturnRunsAllFinally()
  returns (log: int)
  opaque
  ensures log == 3
{
  log := 0;
  try {
    try {
      return
    } finally {
      log := log + 1
    }
  } finally {
    log := log + 2
  }
};
#end
-- `finally` also runs on a `return` from inside a `catch` handler (the
-- two-label case): the caught `throw` runs the handler, whose `return` unwinds
-- through `finally` (`r := 5`) before leaving the procedure.
#eval testLaurelExecution {} <|
#strata
program Laurel;
composite MyError {}
procedure returnInCatchRunsFinally()
  returns (r: int)
  opaque
  ensures r == 5
{
  var e: MyError := new MyError;
  r := 0;
  try {
    throw e
  } catch c when c is MyError {
    return
  } finally {
    r := 5
  }
};
#end

-- A `return` from a `catch` handler runs both the inner and outer `finally`
-- arms (nested), so `log` ends at 3.
#eval testLaurelExecution {} <|
#strata
program Laurel;
composite MyError {}
procedure returnInCatchNestedFinally()
  returns (log: int)
  opaque
  ensures log == 3
{
  var e: MyError := new MyError;
  log := 0;
  try {
    try {
      throw e
    } catch c when c is MyError {
      return
    } finally {
      log := log + 1
    }
  } finally {
    log := log + 2
  }
};
#end

-- Abrupt completion of a `finally` supersedes a pending completion from the try
-- body (Java JLS §14.20.2 / C#). Here a `return` in the `finally` swallows the
-- in-flight `throw`: the procedure completes normally, so — despite declaring
-- `throws MyError` — it provably never lets an exception escape (`throwsOn false`)
-- and returns the value set before the `try`. Without the supersede the stale
-- `$thrown` would build a `Bad` result and violate `throwsOn false`.
#eval testLaurelExecution {} <|
#strata
program Laurel;
composite MyError {}
procedure returnInFinallySwallowsThrow()
  returns (y: int)
  throws (e: MyError)
  opaque
  ensures y == 7
// A case with a `false` guard forces nothing, so its only effect is the
// exhaustiveness claim `isBad ==> false`: this procedure never throws.
  throwsOn false {
  }
{
  var e: MyError := new MyError;
  y := 7;
  try {
    throw e
  } finally {
    return
  }
};
#end

-- The escape check must agree with the supersede rule: because the `finally`'s
-- `return` provably swallows the in-flight `throw`, nothing escapes and the
-- procedure needs no `throws` clause at all. (The analysis discards a pending
-- body/handler completion when the `finally` arm definitely completes abruptly;
-- without that it reported a spurious "may let an exception ... escape" here and
-- rejected this legal program.)
#eval testLaurelExecution {} <|
#strata
program Laurel;
composite MyError {}
procedure swallowedNeedsNoThrowsDecl()
  returns (y: int)
  opaque
  ensures y == 7
{
  var e: MyError := new MyError;
  y := 7;
  try {
    throw e
  } finally {
    return
  }
};
#end

-- The dual: a `throw` in the `finally` discards a pending `return`. The inner
-- `return` is superseded by the `finally`'s `throw`, which propagates to the
-- outer `catch` (y := 1); execution then continues past the outer `try` (y := 3).
-- Without the supersede the stale `$returning` would exit the procedure early
-- (returning y == 1), violating `ensures y == 3`.
#eval testLaurelExecution {} <|
#strata
program Laurel;
composite MyError {}
procedure throwInFinallyDiscardsReturn()
  returns (y: int)
  opaque
  ensures y == 3
{
  var e: MyError := new MyError;
  y := 0;
  try {
    try {
      return
    } finally {
      throw e
    }
  } catch c {
    y := 1
  };
  y := 3;
  return
};
#end

-- An `exit` that leaves a `try` runs its `finally` arm on the way out, just as a
-- `return` does: the `exit out` below still sets `r` to 1 before leaving the block.
#eval testLaurelExecution {} <|
#strata
program Laurel;
procedure exitRunsFinally()
  returns (r: int)
  opaque
  ensures r == 1
{
  r := 0;
  {
    try {
      exit out
    } finally {
      r := 1
    }
  } out;
  assert r == 1
};
#end

-- An `exit` crossing two `try`/`finally` boundaries runs both arms, innermost
-- first, then lands at its label (the `return` analogue is
-- `nestedReturnRunsAllFinally`). `log` ends at 3, and the statement between the
-- inner and outer `try` is skipped.
#eval testLaurelExecution {} <|
#strata
program Laurel;
procedure exitRunsAllFinally()
  returns (log: int)
  opaque
  ensures log == 3
{
  log := 0;
  {
    try {
      try {
        exit out
      } finally {
        log := log + 1
      };
      log := 100
    } finally {
      log := log + 2
    }
  } out;
  assert log == 3
};
#end

-- An `exit` whose target label is opened *inside* the `try` does not leave it, so
-- it needs no unwinding: control resumes after the labeled block, the rest of the
-- body runs, and `finally` runs once at the end as usual (r == 2 + 10).
#eval testLaurelExecution {} <|
#strata
program Laurel;
procedure exitInsideTryNeedsNoUnwind()
  returns (r: int)
  opaque
  ensures r == 12
{
  r := 0;
  try {
    {
      exit skip
    } skip;
    r := 2
  } finally {
    r := r + 10
  }
};
#end

-- An `exit` out of a `catch` handler also runs the `finally` (the two-label case,
-- mirroring `returnInCatchRunsFinally`): the caught `throw` runs the handler,
-- whose `exit` unwinds through `finally` (r := 5) before leaving the block.
#eval testLaurelExecution {} <|
#strata
program Laurel;
composite MyError {}
procedure exitFromCatchRunsFinally()
  returns (r: int)
  opaque
  ensures r == 5
{
  var e: MyError := new MyError;
  r := 0;
  {
    try {
      throw e
    } catch c when c is MyError {
      exit out
    } finally {
      r := 5
    }
  } out;
  assert r == 5
};
#end

-- Abrupt completion by `exit` supersedes a pending completion, like `return` and
-- `throw` do (post-27 rule): the `finally`'s `exit` discards the in-flight
-- `throw`, so the procedure completes normally past the labeled block and needs
-- no `throws` clause — the escape check agrees, because an `exit` that *leaves*
-- the `finally` arm counts as definite abrupt completion there.
#eval testLaurelExecution {} <|
#strata
program Laurel;
composite MyError {}
procedure exitInFinallySwallowsThrow()
  returns (y: int)
  opaque
  ensures y == 4
{
  var e: MyError := new MyError;
  y := 7;
  {
    try {
      throw e
    } finally {
      exit out
    }
  } out;
  y := 4
};
#end

-- An `exit` in a `finally` arm whose target is *inside* that arm is an ordinary
-- jump: it does not complete the arm abruptly, so a pending `throw` survives it
-- and still propagates to the enclosing handler (y == 1).
#eval testLaurelExecution {} <|
#strata
program Laurel;
composite MyError {}
procedure exitWithinFinallyKeepsThrow()
  returns (y: int)
  opaque
  ensures y == 1
{
  var e: MyError := new MyError;
  y := 0;
  try {
    try {
      throw e
    } finally {
      {
        exit inner
      } inner
    }
  } catch c {
    y := 1
  }
};
#end

-- `try` with only a `finally` arm (no catch).
#eval testLaurelExecution {} <|
#strata
program Laurel;
procedure tryFinally() opaque {
  try {
    assert true
  } finally {
    assert true
  }
};
#end

-- An `exit` out of a *loop* body, leaving the `try` on the way: the `finally` runs
-- before control reaches the label. `r == 1` holds on both paths and that is the
-- point — if the loop body runs, the `exit` unwinds through the arm; if the encoding
-- lets the loop fall through instead, the arm still runs on the normal edge. Either
-- way the arm is not skipped, which is what an `exit` crossing a lowered loop *and* a
-- try region could plausibly break.
#eval testLaurelExecution {} <|
#strata
program Laurel;
procedure exitFromLoopRunsFinally()
  returns (r: int)
  opaque
  ensures r == 1
{
  r := 0;
  {
    try {
      var i: int := 0;
      while(i < 3)
        invariant i >= 0
      {
        exit out
      }
    } finally {
      r := 1
    }
  } out;
  assert r == 1
};
#end
