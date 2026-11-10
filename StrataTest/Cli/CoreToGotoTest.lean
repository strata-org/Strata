/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

meta import Strata.Cli.CoreCommands

/-! # `coreToGoto`

The command writes `<name>.symtab.json` and `<name>.goto.json` for a `.core.st`
file, naming the outputs after the file unless `--program-name` is given. The
test runs it on a one-procedure program in a temporary directory and checks the
files it wrote and that the GOTO functions include the procedure. -/

meta section

open Strata.Cli

private def simpleProgram : String :=
"program Core;
procedure simple (x : int) {
  var y : int := x;
  assert [y_eq_x]: y == x;
};
"

/-- Run `coreToGoto` on `simpleProgram` with the extra `flags` in a fresh
    directory, and return the names of the files it wrote and whether the GOTO
    JSON mentions the procedure. -/
private def runCoreToGoto (flags : List (String × String)) : IO (List String × Bool) := do
  IO.FS.withTempDir fun dir => do
    let file := dir / "simple.core.st"
    IO.FS.writeFile file simpleProgram
    let pflags := (("output-dir", dir.toString) :: flags).foldl
      (fun acc (k, v) => ParsedFlags.insert acc k (some v)) {}
    let some cmd := commandMap["coreToGoto"]? | throw (IO.userError "no coreToGoto command")
    runParsedCommand cmd #[file.toString] pflags
    let written := (← dir.readDir).map (·.fileName) |>.toList.filter (·.endsWith ".json")
    let gotoFiles := written.filter (·.endsWith ".goto.json")
    let mentions ← gotoFiles.anyM fun (f : String) => do
      return ((← IO.FS.readFile (dir / (f : String))).splitOn "simple").length > 1
    return (written.mergeSort (· < ·), mentions)

-- The command prints the paths it wrote, which name the temporary directory, so
-- its output is dropped and the results are checked instead.
#guard_msgs (drop info) in
#eval do
  let r ← runCoreToGoto []
  unless r == (["simple.goto.json", "simple.symtab.json"], true) do
    throw (IO.userError s!"unexpected result {repr r}")

#guard_msgs (drop info) in
#eval do
  let r ← runCoreToGoto [("program-name", "renamed")]
  unless r == (["renamed.goto.json", "renamed.symtab.json"], true) do
    throw (IO.userError s!"unexpected result {repr r}")

end
