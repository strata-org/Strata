/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
import Strata.Java.Gen
import Strata.Languages.Cortex.Wire

/-!
# Cortex Java AST Generator

Generates Java source files for the Cortex wire format (`Cortex.Wire.Program`)
using `getIonSerializer%`, matching the Ion encoding `Cortex.Wire.readProgram`
reads.

Usage:
  lake exe cortexJavaGen <package> <output-dir>
-/

open Strata.Java

private def cortexFiles : GeneratedFiles := getIonSerializer% Cortex.Wire.Program "___placeholder___"

def main (args : List String) : IO Unit := do
  match args with
  | [package, outputDir] =>
    let files := cortexFiles.files.map fun (name, content) =>
      (name, content.replace "package ___placeholder___;" s!"package {package};")
    writeJavaFiles outputDir package { files }
    IO.println s!"Generated {files.size} Java files in {outputDir}"
  | _ =>
    IO.eprintln "Usage: lake exe cortexJavaGen <package> <output-dir>"
    IO.Process.exit 1
