/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

private partial def collectFiles (base root : System.FilePath) : IO (Array String) := do
  let mut results := #[]
  for entry in ← System.FilePath.readDir root do
    if ← entry.path.isDir then
      results := results ++ (← collectFiles base entry.path)
    else
      let relPath := entry.path.toString.dropPrefix (base.toString ++ "/") |>.toString
      if relPath.endsWith ".st" || relPath.endsWith ".expected" || relPath.endsWith ".args" then
        results := results.push relPath
  return results

-- Verify that EmbeddedData.lean is up to date with the Examples/ directory.
#eval show IO Unit from do
  let examplesDir : System.FilePath := "Examples"
  let files ← collectFiles examplesDir examplesDir
  let sorted := files.toList.mergeSort (· < ·) |>.toArray

  let dataFile : System.FilePath := "Strata" / "Examples" / "EmbeddedData.lean"
  let content ← IO.FS.readFile dataFile

  let mut missing := #[]
  for file in sorted do
    if !(content.splitOn s!"\"{file}\"").length > 1 then
      missing := missing.push file

  let lineCount := (content.splitOn "include_str").length - 1

  if missing.size > 0 then
    IO.eprintln s!"EmbeddedData.lean is missing {missing.size} files:"
    for f in missing do
      IO.eprintln s!"  {f}"
    throw <| IO.userError "EmbeddedData.lean is out of date. Run 'lake exe GenerateEmbedded' to regenerate."

  if lineCount != sorted.size then
    throw <| IO.userError s!"EmbeddedData.lean has {lineCount} entries but Examples/ has {sorted.size} files. Run 'lake exe GenerateEmbedded' to regenerate."

  IO.println s!"✓ EmbeddedData.lean is up to date ({sorted.size} files)"
