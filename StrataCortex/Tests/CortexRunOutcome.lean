/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
meta import StrataCortex.Implementation.Cli
meta import StrataCortex.Tests.Util.TestCortex

/-!
# How a run on the Cortex interpreter ends, and how it exits

A run of a program's entry procedures passes, fails a check, stops, or ends on an interpreter error. A stop, an
assertion or precondition that is the literal `false` with a summary `<kind>: <detail>` or one of the interpreter's
bounds running out, has no verdict. The worst entry decides how the run ends, an interpreter error before a failed
check and a failed check before a stop. `Cortex.Cli.runExitCode` is the code `cortexWireInterpretBinary` exits with.
-/

open Strata Cortex.Wire
open Cortex.TestCortex

namespace Cortex.RunOutcomeTest

meta def fails (n : Nat) : Wire.Cmd := .assert "bad" (.eq (.int 1) (.int 2)) none (at_ n)
meta def stops (n : Nat) : Wire.Cmd := .assert "s" (.bool false) (some "no-model: a call the frontend has no model of") (at_ n)
/-- Reads a field of a variable that holds no reference: an interpreter error. -/
meta def errs (n : Nat) : List Wire.Cmd :=
  [.init "x" (.named "Box") none (at_ n), .init "t" .int none (at_ n), .readField "t" (.var "x") "Box" "v" (at_ n)]

/-- A procedure without a body whose precondition stops the run at the call. -/
meta def noModel : Wire.Procedure :=
  { name := "noModel", inputs := [], outputs := [{ name := "r", ty := .int }], throws := none, entry := false,
    source := at_ 90, body := none,
    requires := [{ cond := .bool false, summary := some "no-model: noModel" }] }

/-- A procedure without a body whose stop comes first among its preconditions. -/
meta def guarded : Wire.Procedure :=
  { name := "guarded", inputs := [{ name := "x", ty := .int }], outputs := [], throws := none, entry := false,
    source := at_ 91, body := none,
    requires := [{ cond := .bool false, summary := some "no-model: guarded" },
                 { cond := .op "Int.Le" [.int 1, .var "x"], summary := some "x is positive" }] }

/-- An entry procedure at `n` whose block jumps to itself, at `jump`: it runs until its fuel runs out. -/
meta def spins (name : String) (n : Nat) (jump : FileRange := at_ n) : Wire.Procedure :=
  { name, inputs := [], outputs := [], throws := none, requires := [], entry := true, source := at_ n,
    body := some { entry := "b0", handlers := [],
                   blocks := [{ label := "b0", cmds := [], transfer := .goto "b0" jump }] } }

/-- A procedure at `n` that calls itself, at `n + 1`: it nests calls until the call depth runs out. -/
meta def recurses (n : Nat) : Wire.Procedure := proc "r" (at_ n) [.call [] "r" [] (at_ (n + 1))] (entry := false)

meta def program (procedures : List Wire.Procedure) : Wire.Program :=
  { composites := [{ name := "Box", extending := [], fields := [{ name := "v", ty := .int }] }], constrained := [],
    procedures }

meta def describe : RunOutcome → String
  | .passed => "passes"
  | .failed => "fails"
  | .stopped => "stops"
  | .error => "errs"

meta def run (label : String) (procedures : List Wire.Procedure) (fuel : Nat := 1000)
    (globals : List Wire.Global := []) : IO Unit :=
  match Cortex.interpretWire { program procedures with globals } fuel with
  | .error e => IO.println s!"{label}: error: {e}"
  | .ok o =>
    IO.println s!"{label}: {describe o.outcome}, exit {Cortex.Cli.runExitCode o}: \
      {o.diagnostics.toList.map fun m => s!"{m.fileRange.range.start.byteIdx}: {m.message}"}\
      {if o.errors.isEmpty then "" else s!", errors {o.errors.toList}"}"

/--
info: passes: passes, exit 0: []
stops: stops, exit 4: [3: the run stops here: no-model: a call the frontend has no model of]
stops at a call: stops, exit 4: [11: the run stops here: no-model: noModel]
stops at a call after its other preconditions: fails, exit 2: [27: x is positive does not hold, 27: the run stops here: no-model: guarded]
fails, then stops: fails, exit 2: [4: assertion does not hold, 5: the run stops here: no-model: a call the frontend has no model of]
fails in one entry, errs in another: errs, exit 3: [13: assertion does not hold, 14: the interpreter fails here: an expression did not evaluate], errors [(b, an expression did not evaluate)]
stops in one entry, errs in another: errs, exit 3: [30: the run stops here: no-model: a call the frontend has no model of, 31: the interpreter fails here: an expression did not evaluate], errors [(b, an expression did not evaluate)]
stops nowhere: errs, exit 3: [], errors [(e, no-model: nowhere, at a stop with no source location)]
false without a kind: fails, exit 2: [21: assertion does not hold, 22: unreachable does not hold]
out of fuel: stops, exit 4: [15: the run stops here: resource-limit: out of fuel]
out of fuel where nothing has a location: stops, exit 4: [28: the run stops here: resource-limit: out of fuel]
out of fuel in the prologue: stops, exit 4: [25: the run stops here: resource-limit: out of fuel]
out of call depth: stops, exit 4: [33: the run stops here: resource-limit: the call-depth limit was exceeded]
-/
#guard_msgs in
#eval do
  run "passes" [entry "e" 1 [.assert "ok" (.eq (.int 1) (.int 1)) none (at_ 1)]]
  run "stops" [entry "e" 3 [stops 3, fails 3]]
  run "stops at a call" [noModel,
    entry "e" 10 [.init "y" .int none (at_ 11), .call ["y"] "noModel" [] (at_ 11), fails 11]]
  run "stops at a call after its other preconditions" [guarded, entry "e" 26 [.call [] "guarded" [.int 0] (at_ 27)]]
  run "fails, then stops" [entry "e" 4 [fails 4, stops 5]]
  run "fails in one entry, errs in another" [entry "a" 13 [fails 13], entry "b" 14 (errs 14)]
  run "stops in one entry, errs in another" [entry "a" 30 [stops 30], entry "b" 31 (errs 31)]
  run "stops nowhere" [entry "e" 12 [.assert "s" (.bool false) (some "no-model: nowhere") noLoc]]
  run "false without a kind" [entry "e" 20
    [.assert "p" (.bool false) none (at_ 21), .assert "u" (.bool false) (some "unreachable") (at_ 22)]]
  run "out of fuel" [spins "e" 15]
  run "out of fuel where nothing has a location" [spins "e" 28 (jump := noLoc)]
  -- A global's initializer, which has no location, runs in a prologue before the entry's first command.
  run "out of fuel in the prologue" [entry "e" 24 [fails 25]] (fuel := 1)
    (globals := [{ name := "g", ty := .int, init := some (.int 0), source := noLoc }])
  run "out of call depth" [recurses 32, entry "e" 34 [.call [] "r" [] (at_ 35)]] (fuel := 2000)

end Cortex.RunOutcomeTest
