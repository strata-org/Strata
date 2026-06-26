/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
import StrataDDM.Integration.Java.Gen
import Strata.Languages.Laurel.LaurelAST

/-!
# Laurel Java AST Generator

Generates Java source files for the Laurel AST types using `getIonSerializer%`.
The generated Java matches the Ion encoding format used by `getIonDeserializer%`.

Usage:
  lake exe laurelJavaGen <package> <output-dir>

Example:
  lake exe laurelJavaGen org.strata.jverify.laurel ../jverify/verifier/src/main/java
-/

open Strata.Java

/-- Pre-computed Java files for the Laurel `Program` type. -/
private def laurelFiles : GeneratedFiles := getIonSerializer% Strata.Laurel.Program "___placeholder___"

def main (args : List String) : IO Unit := do
  match args with
  | [package, outputDir] =>
    let files := laurelFiles.files.map fun (name, content) =>
      (name, content.replace "package ___placeholder___;" s!"package {package};")
    writeJavaFiles outputDir package { files }
    IO.println s!"Generated {files.size} Java files in {outputDir}"
  | _ =>
    IO.eprintln "Usage: lake exe laurelJavaGen <package> <output-dir>"
    IO.Process.exit 1
