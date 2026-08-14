/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import StrataTest.Util.TestLaurel

open StrataTest.Util
open Strata
open Strata.Laurel

/-
Golden test for the `EliminateExceptions` pass, in the style of
`StrataTest/Transform/PrecondElim`: each case's *before* is an authored
`#strata` program (a `def`), and the *after* is the pass's output, pinned by
`#guard_msgs`. The pass is re-run on every build and its formatted output is
compared against the pinned expectation, so a regression fails the test.

## How this runs the pass

`runPass` resolves the surface program and runs *only* the
`EliminateExceptions` pass on it (`resolve` + `eliminateExceptionsTransform`),
not the full pipeline. This isolates the pass's own rewrite — the same reason the
`Transform/*` tests run a single transform on a hand-written program.

Note this input is exactly what the pass sees in the real pipeline: elimination
runs *before* heap parameterization (so `$exc_<i>` can be typed at each `try`'s
least-common-ancestor exception type), so exception values are genuinely not heap
`Composite` references here and a `catch … is T` guard genuinely is the surface
`$exc_<i> is T` rather than a lowered type-tag test. The output below is
therefore the pass's real output, not a simplified stand-in.

What is *not* exercised here is what the later passes do to that output — heap
parameterization threading the inout `$heap` through a throwing call,
`ModifiesClauses` building the `isGood`/`isBad`-guarded frames, and
`TypeHierarchy` lowering the `is`-guards. Those are covered by the full-pipeline
verifying tests (`ThrowsOnClause`, `TryCatchThrow`, `TryFinallyThrow`, …).
Output is trimmed to the procedures (the shared prelude/datatype declarations are
unchanged by the pass).
-/

/-- Strip trailing spaces from a line (the pretty-printer emits e.g. `return `
    with a trailing space; keeping it would break the golden and trip the repo's
    trailing-whitespace lint). -/
private def rstrip (l : String) : String :=
  String.ofList (l.toList.reverse.dropWhile (· == ' ')).reverse

/-- Format a program, keeping only the procedures (dropping the unchanged
    prelude/datatype preamble), right-trimming lines and trailing blanks. -/
private def fmtProcs (p : Program) : Std.Format :=
  -- Drop every always-on prelude procedure, keeping only the ones the snippet
  -- declares, so the golden stays focused on what this pass rewrites. Filtering by
  -- name rather than by `isExternal`: the built-in operator wrappers (`$add`,
  -- `$implies`, …) are *transparent* procedures delegating to type-specific
  -- externals, so they are not external themselves.
  let builtinNames := coreDefinitionsForLaurel.staticProcedures.map (·.name.text)
  let p := { p with staticProcedures :=
    p.staticProcedures.filter (fun proc => !builtinNames.contains proc.name.text) }
  let s := (Std.format p).pretty
  let kept := ((s.splitOn "\n").dropWhile (fun l => !l.startsWith "procedure ")).map rstrip
  Std.format ("\n".intercalate (kept.reverse.dropWhile (·.isEmpty)).reverse)

/-- Parse a `#strata` program into a Laurel program (pure; panics on a parse
    error, which cannot happen for the well-formed literals below). -/
private def parseLaurel (t : StrataDDM.Program) : Program :=
  match Laurel.TransM.run (Strata.Uri.file "<#strata>") (Laurel.parseProgram t) with
  | .ok p => p
  | .error e => panic! s!"parse failed: {e}" -- nopanic:ok

/-- Resolve the surface program (with the always-on prelude prepended, as the
    pipeline does) and run *only* the `EliminateExceptions` pass on it. The
    `Result` datatype is not part of that prelude — the pass injects it itself for
    programs that use exceptions — so it does not need prepending here. -/
private def runPass (b : StrataDDM.SourcedProgram) : Program :=
  let program := parseLaurel b.program
  let program := { program with
    staticProcedures := coreDefinitionsForLaurel.staticProcedures ++ program.staticProcedures,
    types := coreDefinitionsForLaurel.types ++ program.types }
  let result := resolve program
  (eliminateExceptionsTransform result.model result.program).1

/-! ### 1. A `throwsOn` case on a bodiless (contract-only) thrower

The `throws` clause makes the result a `Result`. A case with no postconditions emits
just its forcing claim, `C ==> Result..isBad($result)`, and the declared exception type
is preserved as `Result..isBad($result) ==> Result..err($result) is …`. Both are `free`
(assumed, not checked) because there is no body to check them against.

The `throwsOn` block still appears in the output: this pass clears each case's
postconditions but deliberately leaves its guard and frame targets for
`ModifiesClauses`, which runs after heap parameterization and turns them into the
per-case frames and the exhaustiveness claim. -/

private def throwsOnContract : StrataDDM.SourcedProgram :=
#strata
program Laurel;
composite NegativeInputException {}
procedure parsePositive(input: int)
  returns (result: int)
  throws (e: NegativeInputException)
  opaque
  throwsOn input < 0 {
  };
#end

/--
info: procedure parsePositive(input: int): (Result<int, NegativeInputException>)
  opaque
  free ensures Result..isBad($result) ==> Result..err($result) is NegativeInputException
  free ensures input < 0 ==> Result..isBad($result)( summary "throwsOn case forces a throw")
  free ensures Result..isBad($result) ==> input < 0( summary "throwsOn cases cover every throwing path")
  modifies  when Result..isGood($result);
-/
#guard_msgs in
#eval (fmtProcs (runPass throwsOnContract))

/-! ### 2. A `throwsOn` case with a postcondition (bodiless)

The case splits into its forcing claim `C ==> Result..isBad($result)` and one
postcondition per `ensures`, each guarded by `C ∧ Result..isBad($result)`. The first
`ensures` is neither: it is derived from the declared `throws` type, so the type
survives lowering as `Result..isBad($result) ==> Result..err($result) is …`. -/

private def throwsOnCaseSplit : StrataDDM.SourcedProgram :=
#strata
program Laurel;
composite ArithmeticException {}
procedure divide(a: int, b: int)
  returns (result: int)
  throws (e: ArithmeticException)
  opaque
  throwsOn b == 0 {
    ensures e is ArithmeticException
  };
#end

/--
info: procedure divide(a: int, b: int): (Result<int, ArithmeticException>)
  opaque
  free ensures Result..isBad($result) ==> Result..err($result) is ArithmeticException
  free ensures b == 0 ==> Result..isBad($result)( summary "throwsOn case forces a throw")
  free ensures b == 0 & Result..isBad($result) ==> Result..err($result) is ArithmeticException
  free ensures Result..isBad($result) ==> b == 0( summary "throwsOn cases cover every throwing path")
  modifies  when Result..isGood($result);
-/
#guard_msgs in
#eval (fmtProcs (runPass throwsOnCaseSplit))

/-! ### 3. A call to a throwing procedure inside `try`/`catch`

Bind and unwrap its `Result`, propagate on `Bad`, and a guarded catch clause. -/

private def callAndCatch : StrataDDM.SourcedProgram :=
#strata
program Laurel;
composite NotFoundException {}
procedure fetchRecord(id: int) returns (result: int) throws (e: NotFoundException);
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
info: procedure fetchRecord(id: int): (Result<int, NotFoundException>)
  opaque
  free ensures Result..isBad($result) ==> Result..err($result) is NotFoundException;

procedure loadUser(id: int)
  returns (result: int)
  opaque
{
  var $thrown: bool := false;
  var $returning: bool := false;
  {
    {
      var $exc_0: NotFoundException;
      {
        {
          {
            var $callres_1: (Result<int, NotFoundException>) := fetchRecord(id);
            if Result..isBad($callres_1)
              then {
                $exc_0 := Result..err($callres_1);
                $thrown := true;
                exit $try_0
              };
            result := Result..value($callres_1)
          }
        }$try_0;
        if $thrown & $exc_0 is NotFoundException
          then {
            $thrown := false;
            {
              result := 0
            }
          }
      }$tryfin_0;
      if $thrown
        then {
          exit $exnexit
        };
      if $returning
        then {
          exit $exnexit
        }
    }
  }$exnexit
};
-/
#guard_msgs in
#eval (fmtProcs (runPass callAndCatch))

/-! ### 4. `finally` runs on `return`

`return` sets `$returning`, jumps to `$tryfin`, `finally` runs, then the
re-dispatch continues the exit. -/

private def finallyOnReturn : StrataDDM.SourcedProgram :=
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
      var $fin_thrown_1: bool := $thrown;
      var $fin_returning_1: bool := $returning;
      $thrown := false;
      $returning := false;
      {
        status := 5
      };
      $thrown := $fin_thrown_1;
      $returning := $fin_returning_1;
      if $thrown
        then {
          exit $exnexit
        };
      if $returning
        then {
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
but still running `finally`). Because the handler references its binding
(`throw caught`), the caught value is first snapshotted into a fresh per-handler
local (`$exc_caught_2`, typed at the try's LCA `NetworkError`) so a nested throw
could not clobber it; the re-throw then restores it (`$exc_0 := $exc_caught_2`),
no allocation. On the way out, the try's `$exc_0` is copied into the
procedure-level `$exc` (both `NetworkError` here, so a plain copy) before
`exit $exnexit`. -/

private def rethrowFromCatch : StrataDDM.SourcedProgram :=
#strata
program Laurel;
composite NetworkError {}
procedure attempt(x: int) returns (r: int) throws (e: NetworkError);
procedure retry(x: int)
  returns (r: int)
  throws (e: NetworkError)
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
info: procedure attempt(x: int): (Result<int, NetworkError>)
  opaque
  free ensures Result..isBad($result) ==> Result..err($result) is NetworkError;

procedure retry(x: int): (Result<int, NetworkError>)
  opaque
  ensures Result..isBad($result) ==> Result..err($result) is NetworkError
  modifies  when Result..isGood($result)
{
  var $thrown: bool := false;
  var $exc: NetworkError;
  var $returning: bool := false;
  var r: int;
  {
    {
      var $exc_0: NetworkError;
      {
        {
          {
            var $callres_1: (Result<int, NetworkError>) := attempt(x);
            if Result..isBad($callres_1)
              then {
                $exc_0 := Result..err($callres_1);
                $thrown := true;
                exit $try_0
              };
            r := Result..value($callres_1)
          }
        }$try_0;
        if $thrown & $exc_0 is NetworkError
          then {
            $thrown := false;
            var $exc_caught_2: NetworkError := $exc_0;
            {
              $exc_0 := $exc_caught_2;
              $thrown := true;
              exit $tryfin_0
            }
          }
      }$tryfin_0;
      var $fin_thrown_3: bool := $thrown;
      var $fin_returning_3: bool := $returning;
      var $fin_exc_3: NetworkError := $exc_0;
      $thrown := false;
      $returning := false;
      {
        r := 7
      };
      $thrown := $fin_thrown_3;
      $returning := $fin_returning_3;
      $exc_0 := $fin_exc_3;
      if $thrown
        then {
          $exc := $exc_0;
          exit $exnexit
        };
      if $returning
        then {
          exit $exnexit
        }
    }
  }$exnexit;
  if $thrown
    then {
      $result := Bad($exc)
    }
    else {
      $result := Good(r)
    }
};
-/
#guard_msgs in
#eval (fmtProcs (runPass rethrowFromCatch))

/-! ### 6. Nested `try`/`finally`

A `return` in the inner body unwinds through both `finally` arms (inner then
outer) via the chained re-dispatch (`if $returning then exit $tryfin_0`). -/

private def nestedFinally : StrataDDM.SourcedProgram :=
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
            var $fin_thrown_2: bool := $thrown;
            var $fin_returning_2: bool := $returning;
            $thrown := false;
            $returning := false;
            {
              log := log + 1
            };
            $thrown := $fin_thrown_2;
            $returning := $fin_returning_2;
            if $thrown
              then {
                exit $try_0
              };
            if $returning
              then {
                exit $tryfin_0
              }
          }
        }$try_0
      }$tryfin_0;
      var $fin_thrown_3: bool := $thrown;
      var $fin_returning_3: bool := $returning;
      $thrown := false;
      $returning := false;
      {
        log := log + 2
      };
      $thrown := $fin_thrown_3;
      $returning := $fin_returning_3;
      if $thrown
        then {
          exit $exnexit
        };
      if $returning
        then {
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

private def multiCatch : StrataDDM.SourcedProgram :=
#strata
program Laurel;
composite SyntaxError {}
composite IoError {}
procedure parseStrict(input: int) returns (result: int) throws (e: SyntaxError);
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
info: procedure parseStrict(input: int): (Result<int, SyntaxError>)
  opaque
  free ensures Result..isBad($result) ==> Result..err($result) is SyntaxError;

procedure parseDocument(input: int)
  returns (result: int)
  opaque
{
  var $thrown: bool := false;
  var $returning: bool := false;
  {
    {
      var $exc_0: SyntaxError;
      {
        {
          {
            var $callres_1: (Result<int, SyntaxError>) := parseStrict(input);
            if Result..isBad($callres_1)
              then {
                $exc_0 := Result..err($callres_1);
                $thrown := true;
                exit $try_0
              };
            result := Result..value($callres_1)
          }
        }$try_0;
        if $thrown & $exc_0 is SyntaxError
          then {
            $thrown := false;
            {
              result := -1
            }
          };
        if $thrown & $exc_0 is IoError
          then {
            $thrown := false;
            {
              result := -2
            }
          }
      }$tryfin_0;
      var $fin_thrown_2: bool := $thrown;
      var $fin_returning_2: bool := $returning;
      var $fin_exc_2: SyntaxError := $exc_0;
      $thrown := false;
      $returning := false;
      {
        result := result + 100
      };
      $thrown := $fin_thrown_2;
      $returning := $fin_returning_2;
      $exc_0 := $fin_exc_2;
      if $thrown
        then {
          exit $exnexit
        };
      if $returning
        then {
          exit $exnexit
        }
    }
  }$exnexit
};
-/
#guard_msgs in
#eval (fmtProcs (runPass multiCatch))

/-! ### 9. An `exit` that leaves a `try`/`finally`

`exit` is an unwinding edge just like `return`: the jump cannot go straight to its
label, because the `finally` arm between it and that label has to run first. So it
is flagged into `$exiting_out` and routed to `$tryfin_0`, and the re-dispatch after
the arm delivers it — clearing the flag as it goes, so a later completion of an
enclosing `try` cannot mistake the spent flag for a fresh pending jump. The flag
joins `$thrown`/`$returning` in the arm's snapshot/clear/restore, so an abrupt
`finally` supersedes a pending `exit` too. An `exit` whose label is opened inside
the `try` crosses no arm and is left exactly as written. -/

private def exitCrossesFinally : StrataDDM.SourcedProgram :=
#strata
program Laurel;
procedure releaseAndBreak()
  returns (r: int)
  opaque
{
  r := 0;
  {
    try {
      exit out
    } finally {
      r := 1
    }
  } out
};
#end

/--
info: procedure releaseAndBreak()
  returns (r: int)
  opaque
{
  var $thrown: bool := false;
  var $returning: bool := false;
  var $exiting_out: bool := false;
  {
    {
      r := 0;
      {
        {
          {
            {
              $exiting_out := true;
              exit $tryfin_0
            }
          }$try_0
        }$tryfin_0;
        var $fin_thrown_1: bool := $thrown;
        var $fin_returning_1: bool := $returning;
        var $fin_exiting_out_1: bool := $exiting_out;
        $thrown := false;
        $returning := false;
        $exiting_out := false;
        {
          r := 1
        };
        $thrown := $fin_thrown_1;
        $returning := $fin_returning_1;
        $exiting_out := $fin_exiting_out_1;
        if $thrown
          then {
            exit $exnexit
          };
        if $returning
          then {
            exit $exnexit
          };
        if $exiting_out
          then {
            $exiting_out := false;
            exit out
          }
      }out
    }
  }$exnexit
};
-/
#guard_msgs in
#eval (fmtProcs (runPass exitCrossesFinally))

/-! ### 10. A void-returning throwing procedure

Every case above has a value output, so the `Result`'s `Val` is that output's
type. A procedure that declares `throws` but returns nothing still has to produce
*some* `Good` payload, because `Result` is a two-parameter datatype: the lowering
uses `bool` as the placeholder `Val` and `Good(true)` as the payload, so the
result type is `Result<bool, Err>` and the Good branch carries no user value.

Unlike case 1, the derived `isBad ==> err is Err` prints as a plain
`ensures`, not `free ensures`: this procedure has a body, so the claim is checked
against it rather than assumed. -/

private def voidThrows : StrataDDM.SourcedProgram :=
#strata
program Laurel;
composite Err {}
procedure doOrThrow(fail: bool)
  throws (e: Err)
  opaque
{
  var e: Err := new Err;
  if fail then {
    throw e
  }
};
#end

/--
info: procedure doOrThrow(fail: bool): (Result<bool, Err>)
  opaque
  ensures Result..isBad($result) ==> Result..err($result) is Err
  modifies  when Result..isGood($result)
{
  var $thrown: bool := false;
  var $exc: Err;
  var $returning: bool := false;
  {
    {
      var e: Err := new Err;
      if fail
        then {
          {
            $exc := e;
            $thrown := true;
            exit $exnexit
          }
        }
    }
  }$exnexit;
  if $thrown
    then {
      $result := Bad($exc)
    }
    else {
      $result := Good(true)
    }
};
-/
#guard_msgs in
#eval (fmtProcs (runPass voidThrows))

/-! ### 11. Propagating out of a `try` whose LCA is wider than the enclosing `$exc`

Case 5 copies an inner `try`'s exception outward when both sides carry the same
type. Here the inner `try` catches two sibling types, so its `$exc_0` is typed at
their join (`Exception`), while the procedure declares the narrower
`throws ParseError`. Only `ParseError` can actually escape (the handler absorbs
`OtherError`), so the propagation edge is a *downcast*: the pass emits an
`assume` of the type test followed by `as`, which discharges the cast's runtime
check. The `assume` is sound precisely because resolution's escape analysis
already proved the residual reaching that edge is a subtype of the declared
`throws` type. -/

private def widenedPropagation : StrataDDM.SourcedProgram :=
#strata
program Laurel;
composite Exception {}
composite ParseError extends Exception {}
composite OtherError extends Exception {}
procedure propagateNarrow(pick: bool)
  throws (e: ParseError)
  opaque
{
  var p: ParseError := new ParseError;
  var o: OtherError := new OtherError;
  try {
    if pick then {
      throw p
    } else {
      throw o
    }
  } catch e when e is OtherError {
    assert true
  }
};
#end

/--
info: procedure propagateNarrow(pick: bool): (Result<bool, ParseError>)
  opaque
  ensures Result..isBad($result) ==> Result..err($result) is ParseError
  modifies  when Result..isGood($result)
{
  var $thrown: bool := false;
  var $exc: ParseError;
  var $returning: bool := false;
  {
    {
      var p: ParseError := new ParseError;
      var o: OtherError := new OtherError;
      var $exc_0: Exception;
      {
        {
          {
            if pick
              then {
                {
                  $exc_0 := p;
                  $thrown := true;
                  exit $try_0
                }
              }
              else {
                {
                  $exc_0 := o;
                  $thrown := true;
                  exit $try_0
                }
              }
          }
        }$try_0;
        if $thrown & $exc_0 is OtherError
          then {
            $thrown := false;
            {
              assert true
            }
          }
      }$tryfin_0;
      if $thrown
        then {
          assume $exc_0 is ParseError;
          $exc := $exc_0 as ParseError;
          exit $exnexit
        };
      if $returning
        then {
          exit $exnexit
        }
    }
  }$exnexit;
  if $thrown
    then {
      $result := Bad($exc)
    }
    else {
      $result := Good(true)
    }
};
-/
#guard_msgs in
#eval (fmtProcs (runPass widenedPropagation))
