/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
import Lean.Data.Json

import Strata.Backends.CBMC.StrataToCBMC
import Strata.Backends.CBMC.CoreToCBMC
import Strata.Backends.CBMC.GOTO.DefaultSymbols
import Strata.Languages.Core.Verifier
import Strata.Languages.C_Simp.Verify
import Strata.Util.IO
import Std.Internal.Parsec

open Strata

/-- Parse a flat symbol-table JSON string, add CBMC defaults, and wrap for symtab2gb. -/
private def wrapOutput (s : String) (moduleName : String) : IO String := do
  match Lean.Json.parse s with
  | .ok (.obj m) => return (CProverGOTO.wrapSymtab m (moduleName := moduleName)).pretty
  | _ => throw (.userError "testSymbols did not produce a JSON object")

def main (args : List String) : IO Unit := do
  match args with
  | [file] => do
    let text ← Strata.Util.readInputSource file
    let inputCtx := Lean.Parser.mkInputContext text (Strata.Util.displayName file)
    let dctx := Elab.LoadedDialects.builtin
    let dctx := dctx.addDialect! Core
    let dctx := dctx.addDialect! C_Simp
    let leanEnv ← Lean.mkEmptyEnvironment 0
    match Strata.Elab.elabProgram dctx leanEnv inputCtx with
    | .ok pgm =>
      if pgm.commands.size != 1 then
        IO.println "Error: expected exactly 1 function"
      else
        let baseName := System.FilePath.fileName file |>.getD file
        let baseName := if baseName.endsWith ".st" then (baseName.dropEnd 3).toString else baseName
        if file.endsWith ".csimp.st" then
          let csimp_prog := C_Simp.get_program pgm
          match CSimp.testSymbols csimp_prog.funcs.head! with
          | .ok s =>
            let wrapped ← wrapOutput s (moduleName := baseName)
            IO.println wrapped
          | .error e => throw (IO.userError e)
        else if file.endsWith ".core.st" then
          let core_prog := (Core.getProgram pgm inputCtx).fst
          match core_prog.decls.head! with
            | .proc f => match Core.testSymbols f with
              | .ok s =>
                let wrapped ← wrapOutput s (moduleName := baseName)
                IO.println wrapped
              | .error e => throw (IO.userError e)
            | _ => IO.println "Error: expected Strata Core procedure"
        else
          IO.println "Error: Unrecognized file extension"
    | .error errors =>
      for e in errors do
        let msg ← e.toString
        println! s!"Error: {msg}"
  | _ => IO.println "Error: incorrect usage. Usage: StrataToCBMC filename or StrataToCBMC test"
