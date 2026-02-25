/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

-- Executable for verifying a Strata program from a file.
import Strata.Languages.Core.Verifier
import Strata.Languages.Core.SarifOutput
import Strata.Languages.C_Simp.Verify
import Strata.Languages.B3.Verifier.Program
import Strata.Util.IO
import Std.Internal.Parsec

open Strata

def parseOptions (args : List String) : Except Std.Format (Options × String × Option (List String)) :=
  go Options.quiet args none
    where
      go : Options → List String → Option (List String) → Except Std.Format (Options × String × Option (List String))
      | opts, "--verbose" :: rest, procs => go {opts with verbose := .normal} rest procs
      | opts, "--check" :: rest, procs => go {opts with checkOnly := true} rest procs
      | opts, "--type-check" :: rest, procs => go {opts with typeCheckOnly := true} rest procs
      | opts, "--parse-only" :: rest, procs => go {opts with parseOnly := true} rest procs
      | opts, "--stop-on-first-error" :: rest, procs => go {opts with stopOnFirstError := true} rest procs
      | opts, "--sarif" :: rest, procs => go {opts with outputSarif := true} rest procs
      | opts, "--output-format=sarif" :: rest, procs => go {opts with outputSarif := true} rest procs
      | opts, "--vc-directory" :: dir :: rest, procs =>
        go { opts with vcDirectory := .some dir } rest procs
      | opts, "--procedures" :: procList :: rest, _ =>
         let procs := procList.splitToList (· == ',')
         go opts rest (some procs)
      | opts, "--solver" :: solverName :: rest, procs =>
         go {opts with solver := solverName} rest procs
      | opts, "--solver-timeout" :: secondsStr :: rest, procs =>
         let n? := String.toNat? secondsStr
         match n? with
         | .none => .error f!"Invalid number of seconds: {secondsStr}"
         | .some n => go {opts with solverTimeout := n} rest procs
      | opts, "--reach-check" :: rest, procs => go {opts with reachCheck := true} rest procs
      | opts, [file], procs => pure (opts, file, procs)
      | _, [], _ => .error "StrataVerify requires a file as input"
      | _, args, _ => .error f!"Unknown options: {args}"

def usageMessage : Std.Format :=
  f!"Usage: StrataVerify [OPTIONS] <file.\{core, csimp, b3}.st>{Std.Format.line}\
  {Std.Format.line}\
  Options:{Std.Format.line}\
  {Std.Format.line}  \
  --verbose                   Print extra information during analysis.{Std.Format.line}  \
  --check                     Process up until SMT generation, but don't solve.{Std.Format.line}  \
  --type-check                Exit after semantic dialect's type inference/checking.{Std.Format.line}  \
  --parse-only                Exit after DDM parsing and type checking.{Std.Format.line}  \
  --stop-on-first-error       Exit after the first verification error.{Std.Format.line}  \
  --procedures <proc1,proc2>  Verify only the specified procedures (comma-separated).{Std.Format.line}  \
  --sarif                     Output results in SARIF format to <file>.sarif{Std.Format.line}  \
  --output-format=sarif       Output results in SARIF format to <file>.sarif{Std.Format.line}  \
  --vc-directory=<dir>        Store VCs in SMT-Lib format in <dir>{Std.Format.line}  \
  --solver <name>             SMT solver executable to use (default: {defaultSolver}){Std.Format.line}  \
  --reach-check               Enable reachability checks for all asserts and covers."

def main (args : List String) : IO UInt32 := do
  let parseResult := parseOptions args
  match parseResult with
  | .ok (opts, file, proceduresToVerify) => do
    let text ← Strata.Util.readInputSource file
    let inputCtx := Lean.Parser.mkInputContext text (Strata.Util.displayName file)
    let dctx := Elab.LoadedDialects.builtin
    let dctx := dctx.addDialect! Core
    let dctx := dctx.addDialect! C_Simp
    let dctx := dctx.addDialect! B3CST
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
                     -- Strata Core.
                     typeCheck inputCtx pgm opts
        match ans with
        | .error e =>
          println! f!"{e.formatRange (some inputCtx.fileMap) true} {e.message}"
          return 1
        | .ok _ =>
          println! f!"Program typechecked."
          return 0
      else -- !typeCheckOnly
        let vcResults ← try
          if file.endsWith ".csimp.st" then
            C_Simp.verify pgm opts
          else if file.endsWith ".b3.st" || file.endsWith ".b3cst.st" then
            -- B3 verification (different model, handle inline)
            let ast ← match B3.Verifier.programToB3AST pgm with
              | Except.error msg => throw (IO.userError s!"Failed to convert to B3 AST: {msg}")
              | Except.ok ast => pure ast
            let solver ← B3.Verifier.createInteractiveSolver opts.solver
            let reports ← B3.Verifier.programToSMT ast solver
            -- B3 uses a different result format, print directly and return empty array
            for report in reports do
              IO.println s!"\nProcedure: {report.procedureName}"
              for (result, _) in report.results do
                let marker := if result.result.isError then "✗" else "✓"
                let desc := match result.result with
                  | .error .counterexample => "counterexample found"
                  | .error .unknown => "unknown"
                  | .error .refuted => "refuted"
                  | .success .verified => "verified"
                  | .success .reachable => "reachable"
                  | .success .reachabilityUnknown => "reachability unknown"
                IO.println s!"  {marker} {desc}"
            pure #[]  -- Return empty array since B3 prints directly
          else
            verify pgm inputCtx proceduresToVerify opts
        catch e =>
          println! f!"{e}"
          return (1 : UInt32)

        -- Output in SARIF format if requested
        if opts.outputSarif then
          -- Skip SARIF generation for C_Simp files because the translation from C_Simp to
          -- Core discards metadata (file, line, column information), making SARIF output
          -- less useful. The vcResultsToSarif function would work type-wise (both produce
          -- Core.VCResults), but the resulting SARIF would lack location information.
          if file.endsWith ".csimp.st" then
            println! "SARIF output is not supported for C_Simp files (.csimp.st) because location metadata is not preserved during translation to Core."
          else
            -- Create a files map with the single input file
            let uri := Strata.Uri.file file
            let files := Map.empty.insert uri inputCtx.fileMap
            Core.Sarif.writeSarifOutput files vcResults (file ++ ".sarif")

        -- Also output standard format
        for vcResult in vcResults do
          let posStr := Imperative.MetaData.formatFileRangeD vcResult.obligation.metadata (some inputCtx.fileMap)
          println! f!"{posStr} [{vcResult.obligation.label}]: {vcResult.result}"
        let success := vcResults.all Core.VCResult.isSuccess
        if success && !opts.checkOnly then
          println! f!"All {vcResults.size} goals passed."
          return 0
        else if success && opts.checkOnly then
          println! f!"Skipping verification."
          return 0
        else
          let provedGoalCount := (vcResults.filter Core.VCResult.isSuccess).size
          let failedGoalCount := (vcResults.filter Core.VCResult.isNotSuccess).size
          println! f!"Finished with {provedGoalCount} goals passed, {failedGoalCount} failed."
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
