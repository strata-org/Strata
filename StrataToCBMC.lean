/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
import Lean.Data.Json

import Strata.Backends.CBMC.StrataToCBMC
import Strata.Backends.CBMC.BoogieToCBMC
import Strata.Languages.Boogie.Verifier
import Strata.Languages.C_Simp.Verify
import Std.Internal.Parsec

open Strata



def main (args : List String) : IO Unit := do
  match args with
  | [file] => do
    let text ← IO.FS.readFile file
    let inputCtx := Lean.Parser.mkInputContext text file
    let dctx := Elab.LoadedDialects.builtin
    let dctx := dctx.addDialect! Boogie
    let dctx := dctx.addDialect! C_Simp
    let leanEnv ← Lean.mkEmptyEnvironment 0
    match Strata.Elab.elabProgram dctx leanEnv inputCtx with
    | .ok pgm =>
      if pgm.commands.size != 1 then
        IO.println "Error: expected exactly 1 function"
      else
        if file.endsWith ".csimp.st" then
          let csimp_prog := C_Simp.get_program pgm
          IO.println (CSimp.testSymbols csimp_prog.funcs.head!)
        else if file.endsWith ".boogie.st" then
          let boogie_prog := (Boogie.getProgram pgm).fst
          match boogie_prog.decls.head! with
            | .proc f => IO.println (Boogie.testSymbols f)
            | _ => IO.println "Error: expected boogie procedure"
        else
          IO.println "Error: Unrecognized file extension"
    | .error e => IO.println s!"Error: parsing"
  | _ => IO.println "Error: incorrect usage. Usage: StrataToCBMC filename or StrataToCBMC test"
