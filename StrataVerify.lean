/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

-- Executable for verifying a Strata program from a file.
import Strata.Languages.Boogie.Verifier
import Strata.Languages.C_Simp.Verify
import Std.Internal.Parsec

open Strata

def isSuccessResult : Boogie.Result → Bool
| .unsat => true
| _ => false

def isSuccessVCResult (vcResult : Boogie.VCResult) :=
  isSuccessResult vcResult.result

def isFailureVCResult (vcResult : Boogie.VCResult) :=
  !isSuccessResult vcResult.result

def parseOptions (args : List String) : Except Std.Format (Options × String) :=
  go Options.quiet args
    where
      go : Options → List String → Except Std.Format (Options × String)
      | opts, "--verbose" :: rest => go {opts with verbose := true} rest
      | opts, "--check" :: rest => go {opts with checkOnly := true} rest
      | opts, "--parse-only" :: rest => go {opts with parseOnly := true} rest
      | opts, "--solver-timeout" :: secondsStr :: rest =>
         let n? := String.toNat? secondsStr
         match n? with
         | .none => .error f!"Invalid number of seconds: {secondsStr}"
         | .some n => go {opts with solverTimeout := n} rest
      | opts, [file] => pure (opts, file)
      | _, [] => .error "StrataVerify requires a file as input"
      | _, args => .error f!"Unknown options: {args}"

def usageMessage : String :=
  "Usage: StrataVerify [--verbose] [--parse-only] [--check] [--solver-timeout <seconds>] <file.{boogie, csimp}.st>"

def main (args : List String) : IO UInt32 := do
  let parseResult := parseOptions args
  match parseResult with
  | .ok (opts, file) => do
    println! f!"Loading {file}"
    let text ← IO.FS.readFile file
    let inputCtx := Lean.Parser.mkInputContext text file
    let dctx := Elab.LoadedDialects.builtin
    let dctx := dctx.addDialect! Boogie
    let dctx := dctx.addDialect! C_Simp
    let leanEnv ← Lean.mkEmptyEnvironment 0
    match Strata.Elab.elabProgram dctx leanEnv inputCtx with
    | .ok pgm =>
      println! s!"Successfully parsed {file}"
      if opts.parseOnly then
          return 0
      let vcResults ← if file.endsWith ".csimp.st" then
        C_Simp.verify "z3" pgm opts
      else
        verify "z3" pgm opts
      for vcResult in vcResults do
        println! f!"{vcResult.obligation.label}: {vcResult.result}"
      let success := vcResults.all isSuccessVCResult
      if success && !opts.checkOnly then
        println! f!"Proved all {vcResults.size} goals."
        return 0
      else if success && opts.checkOnly then
        println! f!"Skipping verification."
        return 0
      else
        let provedGoalCount := (vcResults.filter isSuccessVCResult).size
        let failedGoalCount := (vcResults.filter isFailureVCResult).size
        println! f!"Finished with {provedGoalCount} goals proved, {failedGoalCount} failed."
        return 1
    | .error errors =>
      for (_, e) in errors do
        let msg ← e.toString
        println! s!"Error: {msg}"
      println! f!"Finished with {errors.size} errors."
      return 1
  | .error msg => do
    println! msg
    println! usageMessage
    return 1
