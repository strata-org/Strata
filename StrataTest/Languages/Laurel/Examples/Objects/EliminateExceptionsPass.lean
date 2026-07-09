/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import StrataTest.Util.TestLaurel

open StrataTest.Util
open Strata
open Strata.Laurel

/-
Golden test for the `EliminateExceptions` pass (E7), in the style of
`StrataTest/Transform/PrecondElim`: each case's *before* is an authored
`#strata` program (a `def`), and the *after* is the pass's output, pinned by
`#guard_msgs`. The pass is re-run on every build and its formatted output is
compared against the pinned expectation, so a regression fails the test.

## How this runs the pass

`runPass` resolves the surface program and runs *only* the
`EliminateExceptions` pass on it (`resolve` + `eliminateExceptionsTransform`),
not the full pipeline. Running it directly on the surface program keeps the
output clean: heap parameterization has not run, so exception values are not yet
heap `Composite` references, there is no `$heap` threading or `modifies`-clause
noise, and a `catch … is T` guard shows as the surface `$exc is T` rather than
the lowered type-tag test. This isolates the pass's own rewrite — the same
reason the `Transform/*` tests run a single transform on a hand-written program.

The pass's interaction with heap parameterization (notably threading the inout
`$heap` through a throwing call) is therefore *not* exercised here; that path is
covered by the full-pipeline verifying tests (`TryHeapCalls`,
`ThrowsPostconditions`, `TryCatchBehavior`, …). Output is trimmed to the
procedures (the shared prelude/datatype declarations are unchanged by the pass).
-/

/-- Strip trailing spaces from a line (the pretty-printer emits e.g. `return `
    with a trailing space; keeping it would break the golden and trip the repo's
    trailing-whitespace lint). -/
private def rstrip (l : String) : String :=
  String.ofList (l.toList.reverse.dropWhile (· == ' ')).reverse

/-- Format a program, keeping only the procedures (dropping the unchanged
    prelude/datatype preamble), right-trimming lines and trailing blanks. -/
private def fmtProcs (p : Program) : Std.Format :=
  let s := (Std.format p).pretty
  let kept := ((s.splitOn "\n").dropWhile (fun l => !l.startsWith "procedure ")).map rstrip
  Std.format ("\n".intercalate (kept.reverse.dropWhile (·.isEmpty)).reverse)

/-- Parse a `#strata` program into a Laurel program (pure; panics on a parse
    error, which cannot happen for the well-formed literals below). -/
private def parseLaurel (t : StrataDDM.Program) : Program :=
  match Laurel.TransM.run (Strata.Uri.file "<#strata>") (Laurel.parseProgram t) with
  | .ok p => p
  | .error e => panic! s!"parse failed: {e}" -- nopanic:ok

/-- Resolve the surface program (with the preludes prepended, as the pipeline
    does) and run *only* the `EliminateExceptions` pass on it. -/
private def runPass (b : StrataDDM.SourcedProgram) : Program :=
  let program := parseLaurel b.program
  let program := { program with
    staticProcedures := coreDefinitionsForLaurel.staticProcedures ++ program.staticProcedures,
    types := coreDefinitionsForLaurel.types ++ program.types }
  let program :=
    if (referencedNames program).contains baseExceptionTypeName then
      { program with types := exceptionDefinitionsForLaurel.types ++ program.types }
    else program
  let result := resolve program
  (eliminateExceptionsTransform result.model result.program).1

/-! ### 1. `onThrow` contract on a bodiless (contract-only) thrower

The `throws` clause makes the result a `Result`, and `onThrow` becomes an
ordinary postcondition `Result..isBad($result) ==> …`. -/

def onThrowContract : StrataDDM.SourcedProgram :=
#strata
program Laurel;
composite NegativeInputException extends BaseException {}
procedure parsePositive(input: int)
  returns (result: int)
  throws NegativeInputException
  onThrow (e) input < 0;
#end

/--
info: procedure parsePositive(input: int)
  returns ($result: (Result<int, Composite>))
  opaque
  ensures Result..isBad($result) ==> input < 0;
-/
#guard_msgs in
#eval (fmtProcs (runPass onThrowContract))

/-! ### 2. `when C throws (e) P` behavior case (bodiless)

Becomes `C ==> (Result..isBad($result) ∧ P[e := err])`. -/

def whenThrows : StrataDDM.SourcedProgram :=
#strata
program Laurel;
composite ArithmeticException extends BaseException {}
procedure divide(a: int, b: int)
  returns (result: int)
  throws ArithmeticException
  when b == 0 throws (e) e is ArithmeticException;
#end

/--
info: procedure divide(a: int, b: int)
  returns ($result: (Result<int, Composite>))
  opaque
  ensures b == 0 ==> Result..isBad($result) & Result..err($result) is ArithmeticException;
-/
#guard_msgs in
#eval (fmtProcs (runPass whenThrows))

/-! ### 3. A call to a throwing procedure inside `try`/`catch`

Bind and unwrap its `Result`, propagate on `Bad`, and a guarded catch clause. -/

def callAndCatch : StrataDDM.SourcedProgram :=
#strata
program Laurel;
composite NotFoundException extends BaseException {}
procedure fetchRecord(id: int) returns (result: int) throws NotFoundException;
procedure loadUser(id: int)
  returns (result: int)
  opaque
{
  try {
    result := fetchRecord(id)
  } catch caught when caught is NotFoundException {
    result := 0
  }
};
#end

/--
info: procedure fetchRecord(id: int)
  returns ($result: (Result<int, Composite>))
  opaque;

procedure loadUser(id: int): int
  opaque
{
  var $thrown: bool := false;
  var $exc: Composite;
  var $returning: bool := false;
  {
    {
      {
        {
          {
            var $callres_1: (Result<int, Composite>) := fetchRecord(id);
            if Result..isBad($callres_1) then {
              $exc := Result..err($callres_1);
              $thrown := true;
              exit $try_0
            };
            result := Result..value($callres_1)
          }
        }$try_0;
        if $thrown & $exc is NotFoundException then {
          $thrown := false;
          {
            result := 0
          }
        }
      }$tryfin_0;
      if $thrown then {
        exit $exnexit
      };
      if $returning then {
        exit $exnexit
      }
    }
  }$exnexit
};
-/
#guard_msgs in
#eval (fmtProcs (runPass callAndCatch))

/-! ### 4. `finally` runs on `return` (F18)

`return` sets `$returning`, jumps to `$tryfin`, `finally` runs, then the
re-dispatch continues the exit. -/

def finallyOnReturn : StrataDDM.SourcedProgram :=
#strata
program Laurel;
procedure closeAndReturn()
  returns (status: int)
  opaque
{
  status := 0;
  try {
    return
  } finally {
    status := 5
  }
};
#end

/--
info: procedure closeAndReturn()
  returns (status: int)
  opaque
{
  var $thrown: bool := false;
  var $exc: Composite;
  var $returning: bool := false;
  {
    {
      status := 0;
      {
        {
          {
            $returning := true;
            exit $tryfin_0
          }
        }$try_0
      }$tryfin_0;
      {
        status := 5
      };
      if $thrown then {
        exit $exnexit
      };
      if $returning then {
        exit $exnexit
      }
    }
  }$exnexit
};
-/
#guard_msgs in
#eval (fmtProcs (runPass finallyOnReturn))

/-! ### 5. Re-throw from inside a `catch`, with `finally` (the two-label case)

The handler's `throw` targets `$tryfin` (skipping the rest of the catch chain
but still running `finally`); the caught exception is re-thrown (`$exc := $exc`),
no allocation. -/

def rethrowFromCatch : StrataDDM.SourcedProgram :=
#strata
program Laurel;
composite NetworkError extends BaseException {}
procedure attempt(x: int) returns (r: int) throws NetworkError;
procedure retry(x: int)
  returns (r: int)
  throws NetworkError
  opaque
{
  try {
    r := attempt(x)
  } catch caught when caught is NetworkError {
    throw caught
  } finally {
    r := 7
  }
};
#end

/--
info: procedure attempt(x: int)
  returns ($result: (Result<int, Composite>))
  opaque;

procedure retry(x: int)
  returns ($result: (Result<int, Composite>))
  opaque
{
  var $thrown: bool := false;
  var $exc: Composite;
  var $returning: bool := false;
  var r: int;
  {
    {
      {
        {
          {
            var $callres_1: (Result<int, Composite>) := attempt(x);
            if Result..isBad($callres_1) then {
              $exc := Result..err($callres_1);
              $thrown := true;
              exit $try_0
            };
            r := Result..value($callres_1)
          }
        }$try_0;
        if $thrown & $exc is NetworkError then {
          $thrown := false;
          {
            $exc := $exc;
            $thrown := true;
            exit $tryfin_0
          }
        }
      }$tryfin_0;
      {
        r := 7
      };
      if $thrown then {
        exit $exnexit
      };
      if $returning then {
        exit $exnexit
      }
    }
  }$exnexit;
  if $thrown then {
    $result := Bad($exc)
  } else {
    $result := Good(r)
  }
};
-/
#guard_msgs in
#eval (fmtProcs (runPass rethrowFromCatch))

/-! ### 6. Nested `try`/`finally`

A `return` in the inner body unwinds through both `finally` arms (inner then
outer) via the chained re-dispatch (`if $returning then exit $tryfin_0`). -/

def nestedFinally : StrataDDM.SourcedProgram :=
#strata
program Laurel;
procedure nested()
  returns (log: int)
  opaque
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

/--
info: procedure nested()
  returns (log: int)
  opaque
{
  var $thrown: bool := false;
  var $exc: Composite;
  var $returning: bool := false;
  {
    {
      log := 0;
      {
        {
          {
            {
              {
                {
                  $returning := true;
                  exit $tryfin_1
                }
              }$try_1
            }$tryfin_1;
            {
              log := log + 1
            };
            if $thrown then {
              exit $try_0
            };
            if $returning then {
              exit $tryfin_0
            }
          }
        }$try_0
      }$tryfin_0;
      {
        log := log + 2
      };
      if $thrown then {
        exit $exnexit
      };
      if $returning then {
        exit $exnexit
      }
    }
  }$exnexit
};
-/
#guard_msgs in
#eval (fmtProcs (runPass nestedFinally))

/-! ### 7. Multi-clause `catch` + `finally`

First-match-wins is a sequence of else-less guarded `if`s (each match clears
`$thrown`), then `finally`. -/

def multiCatch : StrataDDM.SourcedProgram :=
#strata
program Laurel;
composite SyntaxError extends BaseException {}
composite IoError extends BaseException {}
procedure parseStrict(input: int) returns (result: int) throws SyntaxError;
procedure parseDocument(input: int)
  returns (result: int)
  opaque
{
  try {
    result := parseStrict(input)
  } catch caught when caught is SyntaxError {
    result := -1
  } catch caught when caught is IoError {
    result := -2
  } finally {
    result := result + 100
  }
};
#end

/--
info: procedure parseStrict(input: int)
  returns ($result: (Result<int, Composite>))
  opaque;

procedure parseDocument(input: int): int
  opaque
{
  var $thrown: bool := false;
  var $exc: Composite;
  var $returning: bool := false;
  {
    {
      {
        {
          {
            var $callres_1: (Result<int, Composite>) := parseStrict(input);
            if Result..isBad($callres_1) then {
              $exc := Result..err($callres_1);
              $thrown := true;
              exit $try_0
            };
            result := Result..value($callres_1)
          }
        }$try_0;
        if $thrown & $exc is SyntaxError then {
          $thrown := false;
          {
            result := -1
          }
        };
        if $thrown & $exc is IoError then {
          $thrown := false;
          {
            result := -2
          }
        }
      }$tryfin_0;
      {
        result := result + 100
      };
      if $thrown then {
        exit $exnexit
      };
      if $returning then {
        exit $exnexit
      }
    }
  }$exnexit
};
-/
#guard_msgs in
#eval (fmtProcs (runPass multiCatch))
