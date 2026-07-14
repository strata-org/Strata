/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import StrataTest.Util.TestLaurel

open StrataTest.Util
open Strata

/-
Behavioral coverage of the E3/E5 handler semantics (see
`docs/design/laurel_extensions.md`, extensions E3 and E5). Unlike `TryCatch` /
`ExceptionScenarios` — which mostly pin parsing, typing, and that the construct
lowers — these tests assert *observable outcomes* of the lowered control flow:
a caught `throw` skips the rest of the body and resumes after the handler,
`finally` runs on every fall-through path, and predicate dispatch is
first-match-wins (including when guards overlap).

Exceptions are constructed *before* the `try` (a `new` inside a `try` body hits
a known lifting-pass gap), and all throws are direct so the verifier knows each
value's runtime type and can discharge the `is`-guards precisely.
-/

-- A caught `throw` skips the rest of the try body; the handler runs and control
-- resumes after the `try`, so the handler's assignment is what is observed. The
-- guard `c is MyError` is satisfied by the thrown value, so the clause fires.
#eval testLaurel <|
#strata
program Laurel;
composite MyError extends BaseException {}
procedure caughtResumes()
  returns (r: int)
  opaque
{
  var e: MyError := new MyError;
  r := 0;
  try {
    throw e;
    r := 1
  } catch c when c is MyError {
    r := 2
  };
  assert r == 2
};
#end

-- `finally` runs on both the normal (no-throw) and the caught-exception paths.
-- `doThrow` is a symbolic input, so the verifier checks both.
#eval testLaurel <|
#strata
program Laurel;
procedure finallyAlwaysRuns(doThrow: bool)
  returns (r: int)
  opaque
{
  var e: BaseException := new BaseException;
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

-- Predicate dispatch skips a non-matching earlier clause and takes the matching
-- later one: an `ErrorB` value is not caught by `is ErrorA` but is by `is ErrorB`.
#eval testLaurel <|
#strata
program Laurel;
composite ErrorA extends BaseException {}
composite ErrorB extends BaseException {}
procedure dispatchSkipsNonMatching()
  returns (r: int)
  opaque
{
  var b: ErrorB := new ErrorB;
  r := 0;
  try {
    throw b
  } catch c when c is ErrorA {
    r := 1
  } catch c when c is ErrorB {
    r := 2
  };
  assert r == 2
};
#end

-- First-match-wins with overlapping guards: a `ChildError` matches both the
-- earlier `is ParentError` clause and the later `is ChildError` clause; the
-- earlier one wins (r == 1, not 2).
#eval testLaurel <|
#strata
program Laurel;
composite ParentError extends BaseException {}
composite ChildError extends ParentError {}
procedure firstMatchWinsOnOverlap()
  returns (r: int)
  opaque
{
  var ce: ChildError := new ChildError;
  r := 0;
  try {
    throw ce
  } catch c when c is ParentError {
    r := 1
  } catch c when c is ChildError {
    r := 2
  };
  assert r == 1
};
#end
-- `finally` runs on an early `return` out of the try body (F18): the return
-- unwinds through the `try`, so `finally` sets `ran := 99` before the procedure
-- exits, and the statement after the `try` is skipped.
#eval testLaurel <|
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
#eval testLaurel <|
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
#eval testLaurel <|
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
#eval testLaurel <|
#strata
program Laurel;
composite MyError extends BaseException {}
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
#eval testLaurel <|
#strata
program Laurel;
composite MyError extends BaseException {}
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
-- A `catch` handler dereferences a field of the (cast) exception binding and
-- checks a *condition* on it: the caught `IndexError` records the offending
-- index, and on the handler path (reached only via the out-of-bounds throw) that
-- recorded index is provably out of bounds.
#eval testLaurel <|
#strata
program Laurel;
composite Exception extends BaseException {}
composite IndexError extends Exception {
  badIndex: int
}
procedure catchReadsField(alen: int, i: int)
  returns (r: int)
  opaque
  ensures r >= 0
{
  r := 0;
  var ei: IndexError := new IndexError;
  ei#badIndex := i;
  try {
    if (i < 0) || (i >= alen) then {
      throw ei
    };
    r := i
  } catch c when c is IndexError {
    assert ((c as IndexError)#badIndex < 0) || ((c as IndexError)#badIndex >= alen);
    r := 0
  }
};
#end

-- Nested `catch`: a handler's binding must survive a throw that occurs *inside*
-- that handler and is caught by a nested `try`/`catch`. The outer handler binds
-- `a` (an `Outer` carrying tag == 1); inside it a nested `try` throws `Inner`,
-- which is caught. Afterwards the outer handler reads `a` again — it must still
-- refer to the original `Outer` (tag == 1), not the inner exception. This
-- exercises the per-handler snapshot of the caught value (a single shared `$exc`
-- is overwritten by the inner throw).
#eval testLaurel <|
#strata
program Laurel;
composite Outer extends BaseException {
  tag: int
}
composite Inner extends BaseException {}
procedure nestedCatchKeepsBinding()
  returns (r: int)
  opaque
  ensures r == 1
{
  var outerExn: Outer := new Outer;
  outerExn#tag := 1;
  var innerExn: Inner := new Inner;
  r := 0;
  try {
    throw outerExn
  } catch a when a is Outer {
    try {
      throw innerExn
    } catch b when b is Inner {
      r := 0
    };
    assert (a as Outer)#tag == 1;
    r := (a as Outer)#tag
  }
};
#end
