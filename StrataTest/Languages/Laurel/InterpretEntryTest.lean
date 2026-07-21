/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Laurel
import Strata.Languages.Core.ProgramEval
import StrataDDM.Integration.Lean.HashCommands

open Strata
open Std (ToFormat Format format)

/-! ## Entry-point marker for concrete interpretation (`laurelInterpret`)

The `laurelInterpret` CLI command picks the procedure(s) to run from the
producer's `entry` markers rather than by a hard-coded name: a Laurel procedure
written with an `entry` clause sets `isInterpretEntry`, the Laurel→Core translator
carries that into Core metadata, and `Core.Program.entryProcedures` reads it
back.

These tests exercise that path end-to-end at the Lean level (Laurel text → Core
→ `entryProcedures` → `runEntry`), since the CLI command itself consumes a Laurel
Ion file and there is no text→Ion CLI step to drive a shell test. The helper
mirrors `laurelInterpretCommand`: translate to Core, then run every marked
entry and report its result. -/

namespace StrataTest.Laurel.InterpretEntry

/-- Names of the procedures the producer marked `entry`, in declaration order. -/
private def markedEntryNames (core : Core.Program) : List String :=
  (Core.Program.entryProcedures core).map (·.header.name.name)

/-- Mirror of `laurelInterpretCommand`: translate a Laurel program to Core
    and run every procedure marked `entry`, reporting the entries that were
    selected and the outcome of each run. Prints, in order:
      * `entries: [..]` — the names selected purely from the markers, proving
        the marker (not a by-name `__main__`/`main` lookup) drove selection.
      * one line per entry: `ok` or the runtime error (e.g. a failed `assert`).
    Contracts run as runtime assertions, matching the interpret command. -/
private def runMarkedEntries (laurel : Laurel.Program) (fuel : Nat := 10000) :
    IO Unit := do
  let core ← match ← Strata.laurelToCore laurel with
    | .ok core => pure core
    | .error e => IO.println s!"translation failed: {e}"; return
  let core ← match Core.typeCheck Core.VerifyOptions.quiet core with
    | .ok prog => pure prog
    | .error e => IO.println s!"type error: {e.message}"; return
  IO.println s!"entries: {markedEntryNames core}"
  match core.run with
  | .error diag => IO.println s!"setup failed: {diag}"
  | .ok E =>
    match Core.Program.entryProcedures core with
    | [] => IO.println "no entry marked"
    | entries =>
      for p in entries do
        let name := p.header.name.name
        -- Report a stable outcome. Assertion labels are assigned from a global
        -- counter during translation, so we report `assert failed` rather than
        -- the volatile label; the command itself maps these back to source
        -- ranges instead of printing the raw label.
        match (Core.Program.runEntry E p fuel).error with
        | none => IO.println s!"{name}: ok"
        | some (.AssertFail ..) => IO.println s!"{name}: assert failed"
        | some e => IO.println s!"{name}: {format (Imperative.EvalError.toFormat e)}"

/-- Parse a Laurel `#strata` program for use with `runMarkedEntries`. -/
private def parse (pgm : StrataDDM.Program) : IO Laurel.Program :=
  match Laurel.TransM.run (Strata.Uri.file "<#strata>") (Laurel.parseProgram pgm) with
  | .ok p => pure p
  | .error e => throw (IO.userError s!"parse error: {e}")

/-! ### A single marked entry is selected and run -/

private def markedPgm : StrataDDM.Program :=
#strata
program Laurel;
procedure helper()
  opaque
{
  assert false
};
procedure runMe()
  entry
  opaque
{
  var x: int := 2;
  assert x + x == 4
};
#end

-- Only `runMe` is marked, so `helper`'s `assert false` is never reached: the
-- marker selects the entry, not a by-name lookup or a run-everything default.
/-- info: entries: [runMe]
runMe: ok
-/
#guard_msgs in
#eval do runMarkedEntries (← parse markedPgm)

/-! ### A failing assertion in the marked entry surfaces as a runtime error -/

private def failingPgm : StrataDDM.Program :=
#strata
program Laurel;
procedure runMe()
  entry
  opaque
{
  var x: int := 5;
  assert x == 10
};
#end

/-- info: entries: [runMe]
runMe: assert failed
-/
#guard_msgs in
#eval do runMarkedEntries (← parse failingPgm)

/-! ### Multiple marked entries all run, in declaration order -/

private def multiPgm : StrataDDM.Program :=
#strata
program Laurel;
procedure first()
  entry
  opaque
{
  assert 1 + 1 == 2
};
procedure notMarked()
  opaque
{
  assert false
};
procedure second()
  entry
  opaque
{
  assert 2 * 3 == 6
};
#end

/-- info: entries: [first, second]
first: ok
second: ok
-/
#guard_msgs in
#eval do runMarkedEntries (← parse multiPgm)

/-! ### No marker → no entry selected

Mirrors the command's "no entry point found" guard: `entryProcedures` is empty
when nothing is marked, even though a `main` procedure exists. -/

private def unmarkedPgm : StrataDDM.Program :=
#strata
program Laurel;
procedure main()
  opaque
{
  assert true
};
#end

/-- info: entries: []
no entry marked
-/
#guard_msgs in
#eval do runMarkedEntries (← parse unmarkedPgm)

/-! ### Transparent body with no assertions still survives as an entry

Regression: a transparent, no-assert body (e.g. plain `{ return 5 }`) hits the
`.Transparent` branch of `needsProcTwin` and — absent this test — would be
folded into a function-only twin during the transparency pass, dropping the
`Core.Decl.proc` arm that carries the `entryPoint` metadata. The entry marker
must be enough on its own to keep the procedure alive as a proc. -/

private def transparentEntryPgm : StrataDDM.Program :=
#strata
program Laurel;
procedure runMe(): int
  entry
{
  return 5
};
#end

/-- info: entries: [runMe]
runMe: ok
-/
#guard_msgs in
#eval do runMarkedEntries (← parse transparentEntryPgm)

/-! ### An `entry`-marked procedure with inputs is rejected at parse time

`runEntry` invokes an entry procedure with no arguments, so a marker on a
procedure that takes inputs would silently run it with unbound inputs. Reject
the combination here rather than papering over it downstream. -/

private def entryWithInputsPgm : StrataDDM.Program :=
#strata
program Laurel;
procedure takesInput(x: int)
  entry
  opaque
{
  assert x == x
};
#end

/-- info: parse error: entry procedure 'takesInput' cannot take inputs: an entry point is invoked with no arguments
-/
#guard_msgs in
#eval do
  match Laurel.TransM.run (Strata.Uri.file "<#strata>") (Laurel.parseProgram entryWithInputsPgm) with
  | .ok _ => IO.println "parse ok (unexpected)"
  | .error e => IO.println s!"parse error: {e}"

/-! ### Transitional shim: the pre-`entry` 8-argument procedure shape still parses

The `procedure` operator gained a positional `entry` argument (8 → 9 args).
A post-CR binary must still consume Ion artifacts produced by an older
grammar, so `parseProcedure` accepts the legacy 8-argument shape and treats
the missing entry clause as absent. `#strata` always emits the current 9-arg
form, so we synthesize the legacy shape by dropping the entry arg from a parsed
procedure op. -/

private def entryProc : StrataDDM.Program :=
#strata
program Laurel;
procedure runMe()
  entry
  opaque
{
  assert true
};
#end

/-- Extract the inner `Laurel.procedure` operation from the single
    `procedureCommand` in a parsed program. -/
private def procedureOp (prog : StrataDDM.Program) : Option StrataDDM.Operation := do
  let cmd ← prog.commands[0]?
  match (cmd.args[0]? : Option StrataDDM.Arg) with
  | some (.op procOp) => some procOp
  | _ => none

/-- Drop the positional `entry` argument (index 6) from a 9-arg procedure op,
    reproducing the legacy 8-argument shape an older producer would emit. -/
private def dropEntryArg (op : StrataDDM.Operation) : StrataDDM.Operation :=
  { op with args := op.args.take 6 ++ op.args.extract 7 op.args.size }

-- The legacy 8-arg shape parses without error and yields `isInterpretEntry := false`
-- (no entry clause present), rather than the old "expects 9 arguments" failure.
/-- info: 8-arg parse ok, isInterpretEntry = false
-/
#guard_msgs in
#eval do
  let some op := procedureOp entryProc | IO.println "no procedure op"
  let legacy := dropEntryArg op
  match Laurel.TransM.run (Strata.Uri.file "<#strata>") (Laurel.parseProcedure (.op legacy)) with
  | .ok proc => IO.println s!"{legacy.args.size}-arg parse ok, isInterpretEntry = {proc.isInterpretEntry}"
  | .error e => IO.println s!"parse error: {e}"

end StrataTest.Laurel.InterpretEntry
