/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import StrataTest.Util.TestLaurel

open StrataTest.Util
open Strata
open Strata.Laurel

/-
Reviewability test for the `EliminateExceptions` pass (E7).

The exceptional channel — `throw`, `try`/`catch`/`finally`, and the
`throws`/`onThrow`/`when-throws` procedure contract — is lowered to ordinary
Laurel by a single Laurel-to-Laurel pass (`EliminateExceptions`) rather than
inside the final Core translator. Each `#eval` below runs the pipeline on a
small program and prints the Laurel *before* and *after* that pass, so the
transformation is reviewable as Laurel-to-Laurel.

The cases build up from minimal to complex, each isolating one feature:

  1. a bare `throw` in a `throws` procedure     — signature → `Result`, `$thrown`/`$exc`, `Bad`/`Good`
  2. `onThrow` contract                         — exceptional postcondition over `$result`
  3. a local `try`/`catch`                      — labeled blocks + guarded catch chain
  4. a call to a throwing procedure             — bind/unwrap `Result`, propagate on `Bad`
  5. `finally` + `return` (F18)                 — `$returning` + re-dispatch runs `finally`
  6. multi-clause `catch` + `finally`           — first-match-wins chain (each match clears `$thrown`)

Notes:
  - The pass runs after heap parameterization, so the snapshots are the
    heap-parameterized form (exceptions are heap `Composite` references, `is`
    tests are already lowered).
  - The shared prelude and datatype declarations (`Heap`/`Composite`/`Result`/…)
    are identical before and after, so the printout is trimmed to the
    procedures — the only declarations the pass rewrites.
  - Each case also asserts that the surface exceptional keywords
    (`throw`/`catch`/`onThrow`/`throws`) are gone afterward, replaced by the
    `$thrown`/`$exc`/`Result` encoding.
-/

/-- Substring containment. -/
private def containsSub (haystack needle : String) : Bool :=
  (haystack.splitOn needle).length > 1

/-- Drop the (unchanged) prelude/datatype preamble, keeping only the procedures
    — the declarations the pass actually rewrites. -/
private def procsOnly (s : String) : String :=
  "\n".intercalate ((s.splitOn "\n").dropWhile (fun l => !l.startsWith "procedure "))

/-- Run the pipeline on `prog`, printing the procedures before and after the
    `EliminateExceptions` pass, then assert the surface exceptional keywords are
    gone afterward. -/
private def showCase (title : String) (prog : StrataDDM.Program) : IO Unit := do
  let laurel ← translateLaurel prog
  IO.FS.withTempDir fun dir => do
    let pfx := (dir / "step").toString
    let _ ← translateWithLaurel { keepAllFilesPrefix := some pfx } laurel
    let entries ← dir.readDir
    let readSuffix (suffix : String) : IO String := do
      match entries.find? (fun e => e.fileName.endsWith suffix) with
      | some e => IO.FS.readFile e.path
      | none => throw (IO.userError s!"expected an emitted file ending in '{suffix}'")
    -- `EliminateExceptions` is the last Laurel pass; the pass just before it is
    -- `ConstrainedTypeElim`, whose emitted program is its input ("before").
    let before ← readSuffix ".ConstrainedTypeElim.laurel.st"
    let after ← readSuffix ".EliminateExceptions.laurel.st"
    IO.println s!"══════════════════════════════════════════════════════════"
    IO.println s!"CASE {title}"
    IO.println s!"══════════════════════════════════════════════════════════"
    IO.println "----- BEFORE (procedures) -----"
    IO.println (procsOnly before)
    IO.println "----- AFTER (procedures) -----"
    IO.println (procsOnly after)
    for kw in ["throw ", "catch", "onThrow", "throws"] do
      if containsSub after kw then
        throw (IO.userError s!"CASE {title}: 'after' program should not contain '{kw}'")

-- 1. Minimal: a bare `throw` in a `throws` procedure (void return). Shows the
--    signature rewrite to `Result<bool, Composite>` (bool placeholder for void),
--    the `$thrown`/`$exc` locals, and the `Bad`/`Good` construction.
--
--    Java equivalent:
--      void validate() throws ValidationException {
--        ValidationException error = new ValidationException();
--        throw error;
--      }
#eval showCase "1 — minimal throw (void return)" <| StrataDDM.SourcedProgram.program <|
#strata
program Laurel;
composite ValidationException extends BaseException {}
procedure validate()
  throws ValidationException
  opaque
{
  var error: ValidationException := new ValidationException;
  throw error
};
#end

-- 2. `onThrow` contract: the exceptional postcondition becomes an ordinary
--    `ensures Result..isBad($result) ==> …` over the result.
--
--    Java equivalent:
--      int parsePositive(int input) throws NegativeInputException {
--        if (input < 0) throw new NegativeInputException();
--        return input;
--      }
--      // contract: if it throws, then input < 0 held.
#eval showCase "2 — onThrow contract + value output" <| StrataDDM.SourcedProgram.program <|
#strata
program Laurel;
composite NegativeInputException extends BaseException {}
procedure parsePositive(input: int)
  returns (result: int)
  throws NegativeInputException
  onThrow (e) input < 0
  opaque
{
  if input < 0 then {
    var error: NegativeInputException := new NegativeInputException;
    throw error
  };
  result := input
};
#end

-- 3. A local `try`/`catch`: the procedure catches its own throw, so it stays
--    non-throwing. Shows the two-label `$try`/`$tryfin` blocks and the guarded
--    catch chain (a match clears `$thrown`).
--
--    Java equivalent:
--      int loadSetting() {
--        ConfigError error = new ConfigError();
--        int value = 0;
--        try { throw error; }
--        catch (ConfigError caught) { value = 2; }
--        return value;
--      }
#eval showCase "3 — local try/catch" <| StrataDDM.SourcedProgram.program <|
#strata
program Laurel;
composite ConfigError extends BaseException {}
procedure loadSetting()
  returns (value: int)
  opaque
{
  var error: ConfigError := new ConfigError;
  value := 0;
  try {
    throw error;
    value := 1
  } catch caught when caught is ConfigError {
    value := 2
  }
};
#end

-- 4. A call to a throwing procedure that is propagated (the caller also declares
--    `throws`). Shows the multi-target `[$heap, $callres] := fetchRecord(…)` bind,
--    the `Result..isBad` propagation, and the `Result..value` unwrap.
--
--    Java equivalent:
--      int fetchRecord(int id) throws NotFoundException {
--        if (id < 0) throw new NotFoundException();
--        return id;
--      }
--      int loadUser(int id) throws NotFoundException {   // doesn't catch → propagates
--        return fetchRecord(id);
--      }
#eval showCase "4 — call a thrower + propagate" <| StrataDDM.SourcedProgram.program <|
#strata
program Laurel;
composite NotFoundException extends BaseException {}
procedure fetchRecord(id: int) returns (result: int) throws NotFoundException opaque {
  if id < 0 then {
    var error: NotFoundException := new NotFoundException;
    throw error
  };
  result := id
};
procedure loadUser(id: int) returns (result: int) throws NotFoundException opaque {
  result := fetchRecord(id)
};
#end

-- 5. `finally` + `return` (F18): the `return` unwinds through the `try`, so the
--    `$returning` flag and the post-`finally` re-dispatch make `finally` run
--    before the procedure exits.
--
--    Java equivalent:
--      int closeAndReturn() {
--        int status = 0;
--        try { return status; }
--        finally { status = 5; }   // runs on the way out
--      }
#eval showCase "5 — finally runs on return (F18)" <| StrataDDM.SourcedProgram.program <|
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

-- 6. More complex: two throws dispatched by a multi-clause `catch` (first-match
--    wins) with a `finally`. Shows the sequential guarded catch chain plus the
--    re-dispatch after `finally`.
--
--    Java equivalent:
--      int parseDocument(int input) {
--        SyntaxError syntaxError = new SyntaxError();
--        IoError ioError = new IoError();
--        int result = 0;
--        try {
--          if (input < 0)  throw syntaxError;
--          if (input == 0) throw ioError;
--          result = input;
--        } catch (SyntaxError caught) { result = -1; }
--          catch (IoError caught)     { result = -2; }
--          finally                    { result = result + 100; }
--        return result;
--      }
#eval showCase "6 — multi-clause catch + finally" <| StrataDDM.SourcedProgram.program <|
#strata
program Laurel;
composite SyntaxError extends BaseException {}
composite IoError extends BaseException {}
procedure parseDocument(input: int)
  returns (result: int)
  opaque
{
  var syntaxError: SyntaxError := new SyntaxError;
  var ioError: IoError := new IoError;
  result := 0;
  try {
    if input < 0 then {
      throw syntaxError
    };
    if input == 0 then {
      throw ioError
    };
    result := input
  } catch caught when caught is SyntaxError {
    result := -1
  } catch caught when caught is IoError {
    result := -2
  } finally {
    result := result + 100
  }
};
#end

-- 7. `when C throws (e) P` behavior case: the trigger + exceptional
--    postcondition becomes `C ==> (Result..isBad($result) ∧ P[e := err])` — so a
--    caller can conclude a throw *will* happen when `C` holds.
--
--    Java equivalent:
--      int divide(int a, int b) throws ArithmeticException {
--        if (b == 0) throw new ArithmeticException();
--        return a / b;
--      }
--      // behavior case: when b == 0, divide throws an ArithmeticException.
#eval showCase "7 — when C throws (e) P behavior case" <| StrataDDM.SourcedProgram.program <|
#strata
program Laurel;
composite ArithmeticException extends BaseException {}
procedure divide(a: int, b: int)
  returns (result: int)
  throws ArithmeticException
  when b == 0 throws (e) e is ArithmeticException
  opaque
{
  if b == 0 then {
    var error: ArithmeticException := new ArithmeticException;
    throw error
  };
  result := a / b
};
#end

-- 8. Re-throw from inside a `catch`, with a `finally` (the two-label case): the
--    handler's `throw` targets `$tryfin` (skipping the rest of the catch chain
--    but still running `finally`), then the re-dispatch propagates it out.
--
--    Java equivalent:
--      int retry() throws NetworkError {
--        NetworkError error = new NetworkError();
--        int r = 0;
--        try { throw error; }
--        catch (NetworkError caught) { throw caught; }   // re-throw
--        finally { r = 7; }
--      }
#eval showCase "8 — re-throw from catch + finally" <| StrataDDM.SourcedProgram.program <|
#strata
program Laurel;
composite NetworkError extends BaseException {}
procedure retry()
  returns (r: int)
  throws NetworkError
  opaque
{
  var error: NetworkError := new NetworkError;
  r := 0;
  try {
    throw error
  } catch caught when caught is NetworkError {
    throw caught
  } finally {
    r := 7
  }
};
#end

-- 9. Nested `try`/`finally`: a `return` in the innermost body unwinds through
--    both `finally` arms (inner then outer). Shows the nested `$try`/`$tryfin`
--    blocks and the re-dispatch chaining `$returning` outward.
--
--    Java equivalent:
--      int nested() {
--        int log = 0;
--        try {
--          try { return log; }
--          finally { log = log + 1; }
--        } finally { log = log + 2; }
--      }
#eval showCase "9 — nested try/finally (return unwinds both)" <| StrataDDM.SourcedProgram.program <|
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
