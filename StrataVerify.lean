/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

-- Executable for verifying a Strata program from a file.
import Strata.Languages.Boogie.Verifier
import Strata.Languages.C_Simp.Verify

open Strata

def isSuccessResult : Boogie.Result → Bool
| .unsat => true
| _ => false

def isSuccessVCResult (vcResult : Boogie.VCResult) :=
  isSuccessResult vcResult.result

def main (args : List String) : IO UInt32 := do
  match args with
  | [file] => do
    println! f!"Loading {file}"
    let text ← IO.FS.readFile file
    let inputCtx := Lean.Parser.mkInputContext text file
    let emptyEnv ← Lean.mkEmptyEnvironment 0
    let dctx := Elab.LoadedDialects.builtin
    let dctx := dctx.addDialect! Boogie
    let dctx := dctx.addDialect! C_Simp
    let (env, errors) := Strata.Elab.elabProgram emptyEnv dctx inputCtx
    if errors.isEmpty then
      println! s!"Successfully parsed {file}"
      -- TODO: the `verify` function currently produces a lot of output
      let vcResults ← if file.endsWith ".csimp.st" then
        C_Simp.verify "z3" env Options.quiet
      else
        verify "z3" env Options.quiet
      for vcResult in vcResults do
        println! f!"{vcResult.obligation.label}: {vcResult.result}"
      let success := vcResults.all isSuccessVCResult
      if success then
        println! f!"Proved all {vcResults.size} goals."
        return 0
      else
        let provedGoalCount := (vcResults.filter isSuccessVCResult).size
        let failedGoalCount := (vcResults.filter isSuccessVCResult).size
        println! f!"Finished with {provedGoalCount} goals proved, {failedGoalCount} failed."
        return 1
    else
      for (_, e) in errors do
        let msg ← e.toString
        println! s!"Error: {msg}"
      println! f!"Finished with {errors.size} errors."
      return 1
  | _ => do
    println! f!"Usage: StrataVerify <file.\{boogie, csimp}.st>"
    return 1
