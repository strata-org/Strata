/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
import Lean.Data.Json

import Strata.Cli.Framework
import Strata.Backends.CBMC.CoreToCBMC
import Strata.Backends.CBMC.GOTO.DefaultSymbols
import Strata.Languages.Core.Verifier
import StrataDDM.Util.IO

open Strata
open StrataDDM.Elab (LoadedDialects)

/-- Parse a flat symbol-table JSON string, add CBMC defaults, and wrap for symtab2gb. -/
private def wrapOutput (s : String) (moduleName : String) : IO String := do
  match Lean.Json.parse s with
  | .ok (.obj m) => return (CProverGOTO.wrapSymtab m (moduleName := moduleName)).pretty
  | _ => throw (.userError "testSymbols did not produce a JSON object")

def main (args : List String) : IO Unit := do
  match args with
  | [file] => do
    let text ← StrataDDM.Util.readInputSource file
    let inputCtx := Lean.Parser.mkInputContext text (StrataDDM.Util.displayName file)
    let dctx := LoadedDialects.builtin.addDialect! Core
    let leanEnv ← Lean.mkEmptyEnvironment 0
    match StrataDDM.Elab.elabProgram dctx leanEnv inputCtx with
    | .ok pgm =>
      if pgm.commands.size != 1 then
        IO.println "Error: expected exactly 1 function"
      else if file.endsWith ".core.st" then
        let baseName := Strata.Cli.deriveBaseName [".st"] file
        let coreProg := (Core.getProgram pgm inputCtx).fst
        match coreProg.decls.head! with
        | .proc f _ => match Core.testSymbols f with
          | .ok s =>
            let wrapped ← wrapOutput s (moduleName := baseName)
            IO.println wrapped
          | .error e => throw (IO.userError e)
        | _ => IO.println "Error: expected Strata Core procedure"
      else
        IO.println "Error: expected a .core.st file"
    | .error errors =>
      for e in errors do
        let msg ← e.toString
        println! s!"Error: {msg}"
  | _ => IO.println "Error: incorrect usage. Usage: StrataToCBMC filename"
