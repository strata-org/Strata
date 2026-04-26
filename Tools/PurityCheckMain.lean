import Lean
import Strata.Util.PurityTracker
open Strata.PurityTracker

partial def collectLeanFiles (root : System.FilePath) : IO (Array System.FilePath) := do
  let mut result := #[]
  if ← root.isDir then
    for entry in ← root.readDir do
      result := result ++ (← collectLeanFiles entry.path)
  else if root.extension == some "lean" then
    result := result.push root
  return result

def resolveInputs (args : List String) : IO (Array System.FilePath) := do
  let mut files := #[]
  for arg in args do
    let path : System.FilePath := arg
    if ← path.isDir then
      files := files ++ (← collectLeanFiles path)
    else
      files := files.push path
  return files

def main (args : List String) : IO UInt32 := do
  let impureOnly := args.contains "--impure-only"
  let inputs := args.filter (!·.startsWith "--")
  if inputs.isEmpty then
    IO.eprintln "Usage: purityCheck [--impure-only] <path> [path ...]"
    IO.eprintln "  <path> can be a .lean file or a directory (recursively scanned)"
    return 1
  let files ← resolveInputs inputs
  for file in files.toList.mergeSort (·.toString < ·.toString) do
    let contents ← IO.FS.readFile file
    let r ← checkFile contents file.toString
    if r.isEmpty then
      unless impureOnly do
        IO.println s!"PURE:   {file}"
    else
      IO.println s!"IMPURE: {file} — {r.toList}"
  return 0
