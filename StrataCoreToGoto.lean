/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
import Lean.Data.Json

import StrataTest.Backends.CBMC.CoreToCProverGOTO
import Strata.Languages.Core.Verifier
import Strata.Util.IO
import Std.Internal.Parsec

open Strata

def usageMessage : Std.Format :=
  f!"Usage: StrataCoreToGoto [OPTIONS] <file.core.st>{Std.Format.line}\
  {Std.Format.line}\
  Translates a Strata Core program to CProver GOTO JSON files.{Std.Format.line}\
  {Std.Format.line}\
  Options:{Std.Format.line}\
  {Std.Format.line}  \
  --output-dir <dir>    Directory for output files (default: current directory){Std.Format.line}  \
  --program-name <name> Program name for GOTO output (default: derived from filename)"

structure GotoOptions where
  outputDir : String := "."
  programName : Option String := none

def parseOptions (args : List String) : Except Std.Format (GotoOptions × String) :=
  go {} args
  where
    go : GotoOptions → List String → Except Std.Format (GotoOptions × String)
    | opts, "--output-dir" :: dir :: rest => go {opts with outputDir := dir} rest
    | opts, "--program-name" :: name :: rest => go {opts with programName := some name} rest
    | opts, [file] => .ok (opts, file)
    | _, [] => .error "StrataCoreToGoto requires a .core.st file as input"
    | _, args => .error f!"Unknown options: {args}"

def deriveBaseName (file : String) : String :=
  let name := System.FilePath.fileName file |>.getD file
  -- Strip .core.st or .st suffix
  if name.endsWith ".core.st" then (name.dropEnd 8).toString
  else if name.endsWith ".st" then (name.dropEnd 3).toString
  else name

def main (args : List String) : IO UInt32 := do
  match parseOptions args with
  | .ok (opts, file) =>
    unless file.endsWith ".core.st" do
      IO.println "Error: expected a .core.st file"
      IO.println f!"{usageMessage}"
      return 1
    let baseName := deriveBaseName file
    let programName := opts.programName.getD baseName
    let dir := opts.outputDir
    let text ← Strata.Util.readInputSource file
    let inputCtx := Lean.Parser.mkInputContext text (Strata.Util.displayName file)
    let dctx := Elab.LoadedDialects.builtin
    let dctx := dctx.addDialect! Core
    let leanEnv ← Lean.mkEmptyEnvironment 0
    match Strata.Elab.elabProgram dctx leanEnv inputCtx with
    | .ok pgm =>
      let symTabFile := s!"{dir}/{programName}.symtab.json"
      let gotoFile := s!"{dir}/{programName}.goto.json"
      CoreToGOTO.writeToGotoJson (programName := programName)
        (symTabFileName := symTabFile)
        (gotoFileName := gotoFile)
        pgm
      IO.println s!"Written {symTabFile} and {gotoFile}"
      return 0
    | .error errors =>
      for e in errors do
        let msg ← e.toString
        IO.println s!"Error: {msg}"
      return 1
  | .error msg =>
    IO.println f!"{msg}"
    IO.println f!"{usageMessage}"
    return 1
