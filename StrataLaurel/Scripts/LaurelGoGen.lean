/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
import Strata.Go.Gen
import StrataLaurel.Implementation.LaurelAST

/-!
# Laurel Go AST Generator

Generates Go source files for the Laurel AST types using `getIonGoSerializer%`.
The generated Go matches the Ion encoding format used by `getIonDeserializer%`.

Usage:
  lake exe laurelGoGen <go-package-name> <output-dir>

Example:
  lake exe laurelGoGen laurel ../gofrontend/laurel
-/

open Strata.Go

/-- Pre-computed Go files for the Laurel `LaurelProgram` type. -/
private def laurelFiles : GeneratedFiles := getIonGoSerializer% Strata.Laurel.LaurelProgram "___placeholder___"

/-- Remove obsolete generated type files while preserving handwritten files. -/
private def pruneStaleGeneratedFiles (dir : System.FilePath)
    (files : Array (String × String)) : IO Unit := do
  unless ← dir.pathExists do return
  let current := files.map (·.1)
  for entry in ← dir.readDir do
    if !current.contains entry.fileName && entry.fileName.endsWith ".go" then
      if !(← entry.path.isDir) then
        let content ← IO.FS.readFile entry.path
        if content.startsWith (generatedGoFileMarker ++ "\n") then
          IO.FS.removeFile entry.path

def main (args : List String) : IO Unit := do
  match args with
  | [package, outputDir] =>
    unless isValidGoPackageName package do
      IO.eprintln s!"laurelGoGen: '{package}' is not a valid Go package name"
      IO.Process.exit 1
    -- The generator mentions the package name in exactly one place per file, the
    -- leading `package` clause, so renaming it is a single substitution. Keep it
    -- that way: `getIonGoSerializer%` runs at compile time and cannot be
    -- re-elaborated per invocation.
    let files := laurelFiles.files.map fun (name, content) =>
      (name, content.replace "package ___placeholder___" s!"package {package}")
    pruneStaleGeneratedFiles outputDir files
    writeGoFiles outputDir { files }
    IO.println s!"Generated {files.size} Go files in {outputDir}"
  | _ =>
    IO.eprintln "Usage: lake exe laurelGoGen <go-package-name> <output-dir>"
    IO.Process.exit 1
