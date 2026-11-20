/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Core.LeanExport
public import Lean.Meta.Check

/-! # Shared helpers of the Lean export tests -/

public section

namespace Core.LeanExport.Tests

open Lean Strata.SMT.LeanExport in
/-- `prepareClosed`, with Lean's own check that the result is a well-typed proposition. The
check needs a Lean environment, which these tests have and the export does not. -/
def prepare (context : Core.SMT.Context)
    (assumptions : List Strata.SMT.Term) (goal : Strata.SMT.Term)
    (definitions : List Core.VarDefinition)
    (declarations : List Core.VarDeclaration) : MetaM PreparedQuery := do
  let query ← ofExcept (prepareClosed context assumptions goal definitions declarations)
  Meta.check query.validity
  unless ← Meta.isProp query.validity do throwError "Prepared query is not a proposition"
  return query

def has (text pattern : String) : Bool := (text.splitOn pattern).length > 1

/-- The number of occurrences of `pattern` in `text`. -/
def occurrences (text pattern : String) : Nat := (text.splitOn pattern).length - 1

/-- A configuration that writes to `directory`, and the events it reports, in order. -/
def recording (directory : System.FilePath) (scope : Scope := .undecided) :
    IO (ExportConfig × IO.Ref (Array Event)) := do
  let events ← IO.mkRef (#[] : Array Event)
  return ({ directory, scope, observe := fun event => events.modify (·.push event) }, events)

/-- The `.lean` files of a directory, by name; none when the directory does not exist. Any
other entry is an error, the log of the command-line flags aside: the export leaves nothing
beside its files, no staged file either. -/
def leanFiles (dir : System.FilePath) : IO (Array System.FilePath) := do
  unless ← dir.pathExists do return #[]
  let entries := (← dir.readDir).filter (·.fileName != "export.log")
  if let some stray := entries.find? (!·.fileName.endsWith ".lean") then
    throw <| IO.userError s!"{dir} holds `{stray.fileName}`, which is no exported file"
  return (entries.map (·.path)).qsort (·.toString < ·.toString)

/-- Unsets the module search paths and the sysroot that `lake` sets for the processes it
starts, so that a process given this environment finds no module of this build. -/
def noLeanEnvironment : Array (String × Option String) :=
  #[("LEAN_PATH", none), ("LEAN_SRC_PATH", none), ("LEAN_SYSROOT", none)]

/-- `IO.Process.output` with a deadline. The process runs in a process group of its own; when
it has not ended after `seconds`, the group is stopped and this is an error. -/
def outputWithin (args : IO.Process.SpawnArgs) (seconds : Nat := 600) :
    IO IO.Process.Output := do
  let child ← IO.Process.spawn
    { args with stdout := .piped, stderr := .piped, stdin := .null, setsid := true }
  let stdout ← IO.asTask child.stdout.readToEnd .dedicated
  let stderr ← IO.asTask child.stderr.readToEnd .dedicated
  let deadline := (← IO.monoMsNow) + seconds * 1000
  repeat
    if let some exitCode ← child.tryWait then
      return { exitCode, stdout := ← IO.ofExcept stdout.get, stderr := ← IO.ofExcept stderr.get }
    if (← IO.monoMsNow) ≥ deadline then break
    IO.sleep 50
  child.kill
  discard child.wait
  throw <| IO.userError s!"{args.cmd} has not ended after {seconds} s; it was stopped"

/-- Run Lean on an exported file, in the file's directory and without the search paths of
this build: the file imports nothing, compiles, and Lean reports the open proof and nothing
else. -/
def compilesAlone (file : System.FilePath) : IO Unit := do
  if ((← IO.FS.readFile file).splitOn "\n").any (·.startsWith "import") then
    throw <| IO.userError s!"{file} has an import"
  let name := file.fileName.getD ""
  let output ← outputWithin {
    cmd := ((← Lean.findSysroot) / "bin" / "lean").toString, args := #[name], cwd := file.parent,
    env := noLeanEnvironment }
  -- A message starts with the file and the position, then its severity.
  let messages := ((output.stdout ++ output.stderr).splitOn "\n").filter (!·.isEmpty)
  unless output.exitCode == 0 && messages.length == 1 && messages.all (fun message =>
      message.startsWith s!"{name}:" &&
      message.endsWith ": warning: declaration uses `sorry`") do
    throw <| IO.userError s!"{file} does not compile on its own with the open proof as the \
      only message: {messages.take 20}"

end Core.LeanExport.Tests
