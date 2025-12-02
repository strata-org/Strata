/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
import Lean.Data.Json

import Strata.Backends.CBMC.StrataToCBMC
import Strata.Backends.CBMC.BoogieToCBMC
import Strata.Languages.Boogie.Verifier
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
          let boogie_prog := (Boogie.getProgram pgm inputCtx).fst
          match boogie_prog.decls.head! with
            | .proc f => IO.println (Boogie.testSymbols f)
            | _ => IO.println "Error: expected boogie procedure"
        else
          IO.println "Error: Unrecognized file extension"
    | .error errors =>
      for e in errors do
        let msg ← e.toString
        println! s!"Error: {msg}"
  | _ => IO.println "Error: incorrect usage. Usage: StrataToCBMC filename or StrataToCBMC test"
