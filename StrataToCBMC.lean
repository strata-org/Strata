/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
import Lean.Data.Json

import Strata.Backends.CBMC.StrataToCBMC
import Strata.Backends.CBMC.CoreToCBMC
import Strata.Languages.Core.Verifier
import Strata.Languages.C_Simp.Verify
import Strata.Util.IO
import Std.Internal.Parsec

open Strata



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
        if file.endsWith ".csimp.st" then
          let csimp_prog := C_Simp.get_program pgm
          IO.println (CSimp.testSymbols csimp_prog.funcs.head!)
        else if file.endsWith ".core.st" then
          let core_prog := (Core.getProgram pgm inputCtx).fst
          match core_prog.decls.head! with
            | .proc f => IO.println (Core.testSymbols f)
            | _ => IO.println "Error: expected Strata Core procedure"
        else
          IO.println "Error: Unrecognized file extension"
    | .error errors =>
      for e in errors do
        let msg ← e.toString
        println! s!"Error: {msg}"
  | _ => IO.println "Error: incorrect usage. Usage: StrataToCBMC filename or StrataToCBMC test"
