/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

open System in
/-- Recursively find all `.lean` files under `dir` and return pairs of
    (filePath, moduleName) where moduleName is relative to `root`.
    E.g., `StrataTestExtra/Languages/Python/VerifyPythonTest.lean` →
    `Languages.Python.VerifyPythonTest`. -/
partial def findTestFiles (root dir : FilePath) : IO (Array (FilePath × String)) := do
  let mut results := #[]
  for entry in ← dir.readDir do
    if ← entry.path.isDir then
      results := results ++ (← findTestFiles root entry.path)
    else if entry.path.extension == some "lean" then
      let relPath := entry.path.toString.dropPrefix root.toString |>.toString
        |>.dropPrefix "/"
      let modStr := relPath.dropSuffix ".lean" |>.replace "/" "."
      results := results.push (entry.path, modStr)
  return results

structure Config where
  includes : Array String
  excludes : Array String

def parseArgs (args : List String) : Except String Config := do
  let mut includes := #[]
  let mut excludes := #[]
  let mut rest := args
  while h : !rest.isEmpty do
    have : rest ≠ [] := by simp_all
    let arg := rest.head this
    rest := rest.tail
    if arg == "--exclude" then
      match rest with
      | [] => throw "--exclude requires an argument"
      | val :: rest' =>
        excludes := excludes.push val
        rest := rest'
    else if arg.startsWith "--" then
      throw s!"unknown flag: {arg}"
    else
      includes := includes.push arg
  return { includes, excludes }

def Config.matches (cfg : Config) (modName : String) : Bool :=
  let included :=
    if cfg.includes.isEmpty then true
    else cfg.includes.any (fun inc => modName.startsWith inc)
  let excluded := cfg.excludes.any (fun exc => modName.startsWith exc)
  included && !excluded

def main (args : List String) : IO UInt32 := do
  let cfg ← match parseArgs args with
    | .ok cfg => pure cfg
    | .error msg =>
      IO.eprintln s!"Error: {msg}"
      IO.eprintln "Usage: lake test [-- [MODULE_PREFIX...] [--exclude PREFIX...]]"
      return 1

  let testDir : System.FilePath := "StrataTestExtra"
  let allTests ← findTestFiles testDir testDir
  let tests := allTests.filter (fun (_, modName) => cfg.matches modName)

  if tests.isEmpty then
    if allTests.isEmpty then
      IO.eprintln "No test files found under StrataTestExtra/"
    else
      IO.eprintln "No tests matched the given filters."
      IO.eprintln "Available tests:"
      for (_, modName) in allTests do
        IO.eprintln s!"  {modName}"
    return 1

  let mut failures := 0
  for (file, modName) in tests do
    IO.println s!"Running {modName} ..."
    let child ← IO.Process.spawn {
      cmd := "lean"
      args := #[file.toString]
      stdout := .inherit
      stderr := .inherit
    }
    let exitCode ← child.wait
    if exitCode == 0 then
      IO.println s!"  PASS: {modName}"
    else
      IO.eprintln s!"  FAIL: {modName} (exit code {exitCode})"
      failures := failures + 1

  if failures > 0 then
    IO.eprintln s!"\n{failures} of {tests.size} test file(s) failed."
    return 1
  else
    IO.println s!"\nAll {tests.size} test file(s) passed."
    return 0
