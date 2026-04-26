/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Lean
import Lean.Compiler.InitAttr

/-! # Lake Build + Skim

Runs `lake build`, then identifies modules whose elaboration may have performed
IO and deletes their build artifacts so the next build re-elaborates them.

## Usage

  lake exe skim [--dry-run] [-- <lake-build-args>...]

## Detection strategy

Two complementary checks:

1. **`.olean` inspection**: Load each module's environment and check for `[init]`
   attributed declarations. This precisely detects `initialize`/`builtin_initialize`.

2. **Text scan**: Grep source files for `#eval`, `#guard_msgs`, `#guard`, `run_cmd`,
   `run_elab`, `run_meta`. These execute code during elaboration but don't leave
   `[init]` markers in the environment.
-/

open Lean

namespace Skim

partial def findLeanFiles (root : System.FilePath) : IO (Array System.FilePath) := do
  let mut result := #[]
  if ← root.isDir then
    for entry in ← root.readDir do
      result := result ++ (← findLeanFiles entry.path)
  else if root.extension == some "lean" then
    result := result.push root
  return result

/-- Convert `Strata/DL/Lambda/LExpr.lean` → `Strata.DL.Lambda.LExpr` -/
def sourceToModule (path : System.FilePath) : Name :=
  let s := path.toString.replace "//" "/"
  let s := if s.endsWith ".lean" then (s.dropEnd 5).toString else s
  s.splitOn "/" |>.foldl (· ++ Name.mkSimple ·) .anonymous

/-- Text patterns for commands that execute code but don't leave `[init]` markers. -/
private def evalPatterns : Array String := #[
  "#eval!", "#eval ", "#eval\n",
  "#guard_msgs", "#guard ",
  "run_cmd", "run_elab", "run_meta"
]

def hasEvalText (contents : String) : Bool :=
  contents.splitOn "\n" |>.any fun line =>
    let trimmed := line.trimAsciiStart.toString
    evalPatterns.any (trimmed.startsWith ·)

/-- Check if a module has `[init]` declarations by loading its `.olean`. -/
def hasInitDecls (modName : Name) : IO Bool := do
  let env ← importModules #[{ module := modName }] {}
  let header := env.header
  let modIdx := header.moduleNames.size - 1
  if h : modIdx < header.moduleData.size then
    let modData := header.moduleData[modIdx]
    return modData.constNames.any (hasInitAttr env)
  return false

def deleteArtifacts (lakeBuild : System.FilePath) (leanFile : System.FilePath)
    (dryRun : Bool) : IO Nat := do
  let raw := leanFile.toString.replace "//" "/"
  let stem := (if raw.endsWith ".lean" then raw.dropEnd 5 else raw).toString
  let mut deleted := 0
  for dir in #["lib/lean", "ir"] do
    let base := (lakeBuild / dir / stem).toString
    let parent : System.FilePath := (lakeBuild / dir / stem).parent.getD "."
    if ← parent.isDir then
      for entry in ← parent.readDir do
        if entry.path.toString.startsWith (base ++ ".") then
          if dryRun then
            IO.println s!"  would delete: {entry.path}"
          else
            IO.FS.removeFile entry.path
          deleted := deleted + 1
  return deleted

end Skim

def main (args : List String) : IO UInt32 := do
  let dryRun := args.contains "--dry-run"
  let cwd ← IO.currentDir
  let lakeBuild := cwd / ".lake" / "build"

  unless ← (cwd / "lakefile.toml").pathExists do
    IO.eprintln "Error: must be run from the project root"
    return 1

  -- Step 1: Run lake build
  let lakeArgs := args.filter (· != "--dry-run")
  IO.println "Running lake build..."
  let buildResult ← IO.Process.output {
    cmd := "lake", args := #["build"] ++ lakeArgs.toArray, cwd := cwd
  }
  IO.print buildResult.stdout
  if buildResult.stderr != "" then IO.eprint buildResult.stderr
  if buildResult.exitCode != 0 then
    IO.eprintln "lake build failed"
    return buildResult.exitCode

  -- Step 2: Collect source files
  IO.println "Scanning for impure modules..."
  let mut allFiles := #[]
  for dir in #["Strata", "StrataTest"] do
    let path : System.FilePath := dir
    if ← path.isDir then
      allFiles := allFiles ++ (← Skim.findLeanFiles path)
  for extra in #["StrataMain.lean"] do
    let path : System.FilePath := extra
    if ← path.pathExists then allFiles := allFiles.push path

  -- Step 3: Check each module
  let mut impureCount := 0
  let mut totalDeleted := 0
  for file in allFiles do
    let contents ← IO.FS.readFile file
    let modName := Skim.sourceToModule file
    -- Check 1: text scan for #eval, #guard_msgs, etc.
    let hasEval := Skim.hasEvalText contents
    -- Check 2: olean inspection for [init] declarations
    let hasInit ← try
      Skim.hasInitDecls modName
    catch _ =>
      -- Can't load olean (not built?) — skip olean check, rely on text scan
      pure false
    if hasEval || hasInit then
      impureCount := impureCount + 1
      let deleted ← Skim.deleteArtifacts lakeBuild file dryRun
      totalDeleted := totalDeleted + deleted

  if dryRun then
    IO.println s!"\nDry run: {impureCount} impure modules, {totalDeleted} artifacts would be deleted."
  else
    IO.println s!"Skimmed {impureCount} impure modules ({totalDeleted} artifacts deleted)."
  return 0
