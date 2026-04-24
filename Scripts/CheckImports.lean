/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
import Strata
import Lean.Environment
import Lean.Util.Path

open Lean System

/-- Recursively find all `.lean` files under `dir` and return their module names
    relative to the workspace root. E.g., `Strata/Foo/Bar.lean` → `Strata.Foo.Bar`. -/
partial def findLeanModules (root dir : FilePath) : IO (Array Name) := do
  let mut modules := #[]
  for entry in ← dir.readDir do
    if ← entry.path.isDir then
      modules := modules ++ (← findLeanModules root entry.path)
    else if entry.path.extension == some "lean" then
      let relPath := entry.path.toString.dropPrefix root.toString |>.toString
        |>.dropPrefix "/"
      let modStr := relPath.dropSuffix ".lean" |>.replace "/" "."
      modules := modules.push modStr.toName
  return modules

/-- Parse `-- noimport: Strata.Foo.Bar` lines from a file. -/
def parseNoimportComments (path : FilePath) : IO (Array Name) := do
  let contents ← IO.FS.readFile path
  let mut allowlist := #[]
  for line in contents.splitOn "\n" do
    let trimmed := line.trimAscii
    if trimmed.startsWith "-- noimport:" then
      let modStr := trimmed.dropPrefix "-- noimport:" |>.toString |>.trimAscii
      let modName := modStr.takeWhile (· ≠ ' ') |>.takeWhile (· ≠ '-')
        |>.trimAsciiEnd
      if !modName.isEmpty then
        allowlist := allowlist.push modName.toName
  return allowlist

def main : IO UInt32 := do
  initSearchPath (← findSysroot)
  let env ← do
    let opts := Options.empty
    let imports := #[{ module := `Strata : Import }]
    let trustLevel := 0
    Lean.importModules imports opts trustLevel

  let importedModules : Std.HashSet Name :=
    env.allImportedModuleNames.foldl (init := {}) fun s n =>
      if n.getRoot == `Strata then s.insert n else s

  let strataDir : FilePath := "Strata"
  let onDiskModules ← findLeanModules "." strataDir

  let allowlist ← parseNoimportComments "Strata.lean"
  let allowlistSet : Std.HashSet Name :=
    allowlist.foldl (init := {}) fun s n => s.insert n

  let mut missing := #[]
  for m in onDiskModules do
    if !importedModules.contains m && !allowlistSet.contains m then
      missing := missing.push m

  missing := missing.qsort (·.toString < ·.toString)

  if missing.isEmpty then
    IO.println s!"✓ All {onDiskModules.size} Strata modules are transitively imported."
    return 0
  else
    IO.eprintln s!"✗ {missing.size} Strata module(s) not transitively imported by Strata.lean:"
    for m in missing do
      IO.eprintln s!"  {m}"
    IO.eprintln ""
    IO.eprintln "To fix: add an import for each module (directly or transitively),"
    IO.eprintln "or add '-- noimport: <module>' to Strata.lean to exclude it."
    return 1
