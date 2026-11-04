/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
import Strata
import Lean.Environment
import Lean.Util.Path
import Lean.Elab.ParseImportsFast

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

/-- The module imported, directly or transitively, by every checked module. -/
def initModule : Name := `Strata.Init

/-- Source directories whose modules must load `initModule`. -/
def initCheckedDirs : Array FilePath := #["Strata", "StrataLaurel"]

/-- The source file of module `m`, relative to the workspace root. -/
def modulePath (m : Name) : FilePath :=
  System.mkFilePath (m.components.map toString) |>.addExtension "lean"

/-- Walk `imports` the way Lean's importer (in `importModulesCore` from `Lean/Environment`)
    decides which modules have their data loaded: a module's direct imports are always loaded,
    but beyond that only `public import`s (or the imports of an `import all`ed module) propagate.
    In a non-module file everything is loaded. Records `(module, importAll)`
    pairs; modules not in `headers` (other packages) are not descended into. -/
partial def visitImports (headers : Std.HashMap Name ModuleHeader) (alwaysAll : Bool)
    (imports : Array Import) (importAll : Bool) :
    StateM (Std.HashSet (Name × Bool)) Unit := do
  for i in imports do
    unless i.isExported || importAll do continue
    let importAll := alwaysAll || importAll && i.importAll
    if (← get).contains (i.module, importAll) then continue
    modify (·.insert (i.module, importAll))
    if let some h := headers[i.module]? then
      visitImports headers alwaysAll h.imports importAll

/-- The modules whose data is loaded when elaborating a file with `header`. -/
def loadedModules (headers : Std.HashMap Name ModuleHeader) (header : ModuleHeader) :
    Std.HashSet Name :=
  let visit := visitImports headers (!header.isModule) header.imports true
  (visit.run {}).2.fold (init := {}) fun s (m, _) => s.insert m

/-- Check that every module in `initCheckedDirs` loads `initModule`, so that
    the linters it imports run everywhere. Mathlib enforces the same property
    for `Mathlib.Init` in `scripts/lint-style.lean`. -/
def checkInitImports : IO UInt32 := do
  let mut modules := #[]
  for dir in initCheckedDirs do
    modules := modules ++ (← findLeanModules "." dir)
  let mut headers : Std.HashMap Name ModuleHeader := {}
  for m in modules do
    let path := modulePath m
    headers := headers.insert m (← parseImports' (← IO.FS.readFile path) path.toString)

  -- `Strata.Init` and its own dependencies cannot import it.
  let some initHeader := headers[initModule]?
    | IO.eprintln s!"✗ {modulePath initModule} not found."; return 1
  let exempt := (loadedModules headers initHeader).insert initModule

  let mut missing := #[]
  for m in modules do
    if exempt.contains m then continue
    let some header := headers[m]? | continue
    unless (loadedModules headers header).contains initModule do
      missing := missing.push m
  missing := missing.qsort (·.toString < ·.toString)

  if missing.isEmpty then
    let checked := modules.filter (!exempt.contains ·) |>.size
    IO.println s!"✓ All {checked} checked modules load {initModule}."
    return 0
  else
    IO.eprintln s!"✗ {missing.size} module(s) do not load {initModule}:"
    for m in missing do
      IO.eprintln s!"  {m}"
    IO.eprintln ""
    IO.eprintln s!"To fix: add `public import {initModule}`, or make one of the module's"
    IO.eprintln s!"Strata imports a `public import` of a module that loads {initModule}."
    return 1

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
  else
    IO.eprintln s!"✗ {missing.size} Strata module(s) not transitively imported by Strata.lean:"
    for m in missing do
      IO.eprintln s!"  {m}"
    IO.eprintln ""
    IO.eprintln "To fix: add an import for each module (directly or transitively),"
    IO.eprintln "or add '-- noimport: <module>' to Strata.lean to exclude it."
  let initResult ← checkInitImports
  return if missing.isEmpty then initResult else 1
