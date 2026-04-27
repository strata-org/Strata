/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

/-! # Lake Build + Skim

Runs `lake build`, then reads `.impure` marker files written by the
PurityPlugin during elaboration, and deletes build artifacts for impure
modules so the next build re-elaborates them.

The PurityPlugin is a Lean compiler plugin configured in lakefile.toml.
It runs automatically during `lake build` — no special setup needed.

## Usage

  lake exe skim [--dry-run]
-/

namespace Skim

partial def findMarkerFiles (root : System.FilePath) : IO (Array System.FilePath) := do
  let mut result := #[]
  if ← root.isDir then
    for entry in ← root.readDir do
      result := result ++ (← findMarkerFiles entry.path)
  else if root.extension == some "impure" then
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

  -- Step 1: Run lake build (plugin creates .impure markers automatically)
  IO.println "Building..."
  let buildResult ← IO.Process.output {
    cmd := "lake", args := #["build"], cwd := cwd
  }
  IO.print buildResult.stdout
  if buildResult.stderr != "" then IO.eprint buildResult.stderr
  if buildResult.exitCode != 0 then
    IO.eprintln "lake build failed"
    return buildResult.exitCode

  -- Step 2: Find .impure marker files and delete corresponding build artifacts
  IO.println "Skimming impure module caches..."
  let mut impureCount := 0
  let mut totalDeleted := 0

  -- Scan source directories for .impure markers
  for dir in #["Strata", "StrataTest"] do
    let path : System.FilePath := dir
    if ← path.isDir then
      let markers ← Skim.findMarkerFiles path
      for marker in markers do
        -- marker is e.g. Strata/DDM/Elab/Env.lean.impure
        -- source is Strata/DDM/Elab/Env.lean
        let source := marker.toString.dropRight 7  -- strip ".impure"
        impureCount := impureCount + 1
        let deleted ← Skim.deleteArtifacts lakeBuild source dryRun
        totalDeleted := totalDeleted + deleted
        -- Clean up the marker file
        unless dryRun do
          IO.FS.removeFile marker

  -- Also check root-level files
  for extra in #["StrataMain.lean"] do
    let marker : System.FilePath := extra ++ ".impure"
    if ← marker.pathExists then
      impureCount := impureCount + 1
      let deleted ← Skim.deleteArtifacts lakeBuild extra dryRun
      totalDeleted := totalDeleted + deleted
      unless dryRun do
        IO.FS.removeFile marker

  if dryRun then
    IO.println s!"\nDry run: {impureCount} impure modules, {totalDeleted} artifacts would be deleted."
  else
    IO.println s!"Skimmed {impureCount} impure modules ({totalDeleted} artifacts deleted)."
  return 0
