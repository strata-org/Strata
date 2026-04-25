/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Tools.PurityCheck

/-! # Lake Cache Skimmer

Deletes cached `.lake/build/` artifacts for all modules whose elaboration
might perform I/O, so that `lake build` re-elaborates them from scratch.

## Usage

  lake exe skim [--dry-run]
-/

namespace Skim

/-- Recursively collect all `.lean` files under a directory. -/
partial def findLeanFiles (root : System.FilePath) : IO (Array System.FilePath) := do
  let mut result := #[]
  if ← root.isDir then
    for entry in ← root.readDir do
      result := result ++ (← findLeanFiles entry.path)
  else if root.extension == some "lean" then
    result := result.push root
  return result

/-- Given a `.lean` source path, delete all matching build artifacts. -/
def deleteArtifacts (lakeBuild : System.FilePath) (leanFile : System.FilePath)
    (dryRun : Bool) : IO Nat := do
  -- Strata//Foo/Bar.lean → Strata/Foo/Bar
  let raw := leanFile.toString.replace "//" "/"
  let stem := (if raw.endsWith ".lean" then raw.dropEnd 5 else raw).toString
  let mut deleted := 0
  for dir in #["lib/lean", "ir"] do
    let base := (lakeBuild / dir / stem).toString
    let parent : System.FilePath := (lakeBuild / dir / stem).parent.getD "."
    if ← parent.isDir then
      for entry in ← parent.readDir do
        let entryStr := entry.path.toString
        if entryStr.startsWith (base ++ ".") then
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
    IO.eprintln "Error: must be run from the project root (where lakefile.toml is)"
    return 1

  unless ← lakeBuild.isDir do
    IO.eprintln "No .lake/build/ directory found — nothing to skim."
    return 0

  IO.println "Scanning for impure modules..."
  let mut allFiles := #[]
  for dir in #["Strata", "StrataTest"] do
    let path : System.FilePath := dir
    if ← path.isDir then
      allFiles := allFiles ++ (← Skim.findLeanFiles path)
  let mainFile : System.FilePath := "StrataMain.lean"
  if ← mainFile.pathExists then
    allFiles := allFiles.push mainFile

  let mut impureCount := 0
  let mut totalDeleted := 0
  for file in allFiles do
    let contents ← IO.FS.readFile file
    let reasons ← checkFilePurity contents file.toString
    unless reasons.isEmpty do
      impureCount := impureCount + 1
      let deleted ← Skim.deleteArtifacts lakeBuild file dryRun
      totalDeleted := totalDeleted + deleted

  if dryRun then
    IO.println s!"\nDry run: {impureCount} impure modules, {totalDeleted} artifacts would be deleted."
  else
    IO.println s!"Skimmed {impureCount} impure modules ({totalDeleted} artifacts deleted)."
  return 0
