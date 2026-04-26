/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Util.PurityTracker

/-! # Lake Build + Skim

Runs `lake build`, then uses the linter-based purity tracker to identify
modules whose elaboration may have performed IO, and deletes their build
artifacts so the next build re-elaborates them.

**This is the recommended way to build.** Running `purityCheck` standalone
can give incorrect results if the build cache is stale or missing.

## Usage

  lake exe skim [--dry-run]
-/

open Strata.PurityTracker

namespace Skim

partial def findLeanFiles (root : System.FilePath) : IO (Array System.FilePath) := do
  let mut result := #[]
  if ← root.isDir then
    for entry in ← root.readDir do
      result := result ++ (← findLeanFiles entry.path)
  else if root.extension == some "lean" then
    result := result.push root
  return result

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

  -- Step 1: Run lake build (ensures all .olean files are up to date)
  IO.println "Building..."
  let buildResult ← IO.Process.output {
    cmd := "lake", args := #["build"], cwd := cwd
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

  -- Step 3: Check each module using the linter-based purity tracker.
  -- This re-elaborates each file against the freshly-built .olean imports,
  -- so the linter sees every command with the correct syntax extensions.
  let mut impureCount := 0
  let mut totalDeleted := 0
  for file in allFiles do
    let contents ← IO.FS.readFile file
    let impureCmds ← checkFile contents file.toString
    if !impureCmds.isEmpty then
      impureCount := impureCount + 1
      let deleted ← Skim.deleteArtifacts lakeBuild file dryRun
      totalDeleted := totalDeleted + deleted

  if dryRun then
    IO.println s!"\nDry run: {impureCount} impure modules, {totalDeleted} artifacts would be deleted."
  else
    IO.println s!"Skimmed {impureCount} impure modules ({totalDeleted} artifacts deleted)."
  return 0
