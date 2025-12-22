/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

-- Executable for verifying a Strata program from a file.
import Strata.Languages.Boogie.Verifier
import Strata.Languages.Boogie.SarifOutput
import Strata.Languages.C_Simp.Verify
import Strata.Util.IO
import Std.Internal.Parsec

open Strata

def isSuccessResult : Boogie.Result → Bool
| .unsat => true
| _ => false

def isSuccessVCResult (vcResult : Boogie.VCResult) :=
  isSuccessResult vcResult.result

def isFailureVCResult (vcResult : Boogie.VCResult) :=
  !isSuccessResult vcResult.result

def parseOptions (args : List String) : Except Std.Format (Options × String × Bool) :=
  go Options.quiet args false
    where
      go : Options → List String → Bool → Except Std.Format (Options × String × Bool)
      | opts, "--verbose" :: rest, sarif => go {opts with verbose := true} rest sarif
      | opts, "--check" :: rest, sarif => go {opts with checkOnly := true} rest sarif
      | opts, "--type-check" :: rest, sarif => go {opts with typeCheckOnly := true} rest sarif
      | opts, "--parse-only" :: rest, sarif => go {opts with parseOnly := true} rest sarif
      | opts, "--stop-on-first-error" :: rest, sarif => go {opts with stopOnFirstError := true} rest sarif
      | opts, "--sarif" :: rest, _ => go opts rest true
      | opts, "--output-format=sarif" :: rest, _ => go opts rest true
      | opts, "--solver-timeout" :: secondsStr :: rest, sarif =>
         let n? := String.toNat? secondsStr
         match n? with
         | .none => .error f!"Invalid number of seconds: {secondsStr}"
         | .some n => go {opts with solverTimeout := n} rest sarif
      | opts, [file], sarif => pure (opts, file, sarif)
      | _, [], _ => .error "StrataVerify requires a file as input"
      | _, args, _ => .error f!"Unknown options: {args}"

def usageMessage : Std.Format :=
  f!"Usage: StrataVerify [OPTIONS] <file.\{boogie, csimp}.st>{Std.Format.line}\
  {Std.Format.line}\
  Options:{Std.Format.line}\
  {Std.Format.line}  \
  --verbose                   Print extra information during analysis.{Std.Format.line}  \
  --check                     Process up until SMT generation, but don't solve.{Std.Format.line}  \
  --type-check                Exit after semantic dialect's type inference/checking.{Std.Format.line}  \
  --parse-only                Exit after DDM parsing and type checking.{Std.Format.line}  \
  --stop-on-first-error       Exit after the first verification error.{Std.Format.line}  \
  --solver-timeout <seconds>  Set the solver time limit per proof goal.{Std.Format.line}  \
  --sarif                     Output results in SARIF format to <file>.sarif{Std.Format.line}  \
  --output-format=sarif       Output results in SARIF format to <file>.sarif"

def main (args : List String) : IO UInt32 := do
  let parseResult := parseOptions args
  match parseResult with
  | .ok (opts, file, outputSarif) => do
    let text ← Strata.Util.readInputSource file
    let inputCtx := Lean.Parser.mkInputContext text (Strata.Util.displayName file)
    let dctx := Elab.LoadedDialects.builtin
    let dctx := dctx.addDialect! Boogie
    let dctx := dctx.addDialect! C_Simp
    let leanEnv ← Lean.mkEmptyEnvironment 0
    match Strata.Elab.elabProgram dctx leanEnv inputCtx with
    | .ok pgm =>
      println! s!"Successfully parsed."
      if opts.parseOnly then
          return 0
      else if opts.typeCheckOnly then
        let ans := if file.endsWith ".csimp.st" then
                     C_Simp.typeCheck pgm opts
                   else
                     -- Boogie.
                     typeCheck inputCtx pgm opts
        match ans with
        | .error e =>
          println! f!"Type checking error: {e}"
          return 1
        | .ok _ =>
          println! f!"Program typechecked."
          return 0
      else -- !typeCheckOnly
        let vcResults ←
            if file.endsWith ".csimp.st" then
              C_Simp.verify "z3" pgm opts
            else
              verify "z3" pgm inputCtx opts

        -- Output in SARIF format if requested
        if outputSarif then
          -- Skip SARIF generation for C_Simp files because the translation from C_Simp to
          -- Boogie discards metadata (file, line, column information), making SARIF output
          -- less useful. The vcResultsToSarif function would work type-wise (both produce
          -- Boogie.VCResults), but the resulting SARIF would lack location information.
          if file.endsWith ".csimp.st" then
            println! "SARIF output is not supported for C_Simp files (.csimp.st) because location metadata is not preserved during translation to Boogie."
          else
            let sarifDoc := Boogie.Sarif.vcResultsToSarif vcResults
            let sarifJson := Boogie.Sarif.toPrettyJsonString sarifDoc
            let sarifFile := file ++ ".sarif"
            IO.FS.writeFile sarifFile sarifJson
            println! f!"SARIF output written to {sarifFile}"

        -- Also output standard format
        for vcResult in vcResults do
          let posStr := match Boogie.formatPositionMetaData vcResult.obligation.metadata with
                        | .none => "<none>"
                        | .some str => s!"{str}"
          println! f!"{posStr} [{vcResult.obligation.label}]: {vcResult.result}"
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
    -- Strata.Elab.elabProgram
    | .error errors =>
      for e in errors do
        let msg ← e.toString
        println! s!"Error: {msg}"
      println! f!"Finished with {errors.size} errors."
      return 1
  -- parseResult
  | .error msg => do
    println! msg
    println! usageMessage
    return 1
