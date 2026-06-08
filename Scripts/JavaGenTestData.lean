/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
import StrataDDM

/-!
# Java test data generation helper

Usage:
  lake env lean --run Scripts/JavaGenTestData.lean javaGen <dialect-file> <package> <output-dir>
  lake env lean --run Scripts/JavaGenTestData.lean print --include <dir> <file>

This script replaces the StrataCLI commands used by
`StrataTestExtra/Languages/Java/regenerate-testdata.sh`.
-/

open StrataDDM

def javaGen (dialectPath packageName outputDir : String) : IO Unit := do
  let fm ← mkDialectFileMap
  match ← readStrataFile fm dialectPath with
  | .dialect d =>
    match StrataDDM.Java.generateDialect d packageName with
    | .ok files =>
      StrataDDM.Java.writeJavaFiles outputDir packageName files
      IO.println s!"Generated Java files for {d.name} in {outputDir}/{StrataDDM.Java.packageToPath packageName}"
    | .error msg =>
      IO.eprintln s!"Error generating Java: {msg}"
      IO.Process.exit 1
  | .program _ =>
    IO.eprintln "Expected a dialect file, not a program file."
    IO.Process.exit 1

def printFile (includeDirs : List String) (file : String) : IO Unit := do
  let fm ← mkDialectFileMap
  let mut fm := fm
  for dir in includeDirs do
    match ← fm.addSearchPath dir |>.toBaseIO with
    | .error msg =>
      IO.eprintln msg
      IO.Process.exit 1
    | .ok fm' => fm := fm'
  let ld ← fm.getLoaded
  if mem : file ∈ ld.dialects then
    IO.print <| ld.dialects.format file mem
    return
  match ← readStrataFile fm file with
  | .dialect d =>
    let ld ← fm.getLoaded
    let .isTrue mem := (inferInstance : Decidable (d.name ∈ ld.dialects))
      | IO.eprintln "Internal error reading file."
        IO.Process.exit 1
    IO.print <| ld.dialects.format d.name mem
  | .program pgm =>
    IO.print <| toString pgm

private def parseIncludeArgs (args : List String) : List String × List String :=
  go args []
where
  go : List String → List String → List String × List String
    | "--include" :: dir :: rest, includes => go rest (dir :: includes)
    | other, includes => (includes.reverse, other)

def main (args : List String) : IO Unit := do
  match args with
  | "javaGen" :: dialectPath :: packageName :: outputDir :: _ =>
    javaGen dialectPath packageName outputDir
  | "print" :: rest =>
    let (includeDirs, fileArgs) := parseIncludeArgs rest
    match fileArgs with
    | [file] => printFile includeDirs file
    | _ =>
      IO.eprintln "Usage: ... print [--include <dir>]... <file>"
      IO.Process.exit 1
  | _ =>
    IO.eprintln "Usage:"
    IO.eprintln "  lake env lean --run Scripts/JavaGenTestData.lean javaGen <dialect> <package> <output-dir>"
    IO.eprintln "  lake env lean --run Scripts/JavaGenTestData.lean print [--include <dir>]... <file>"
    IO.Process.exit 1
