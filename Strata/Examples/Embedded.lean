/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
import Strata.Examples.EmbeddedData

/-- Write all embedded example files to the given directory. -/
public def writeEmbeddedExamples (outputDir : System.FilePath) : IO Unit := do
  for (relPath, content) in embeddedExampleFiles do
    let fullPath := outputDir / relPath
    if let some parent := fullPath.parent then
      IO.FS.createDirAll parent
    IO.FS.writeFile fullPath content
