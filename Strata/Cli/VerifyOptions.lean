/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Cli.Framework
public import Strata.Languages.Core.Verifier
public import Strata.Languages.Laurel.LaurelCompilationPipeline

/-! # Verify-options flag parsing

Common CLI flag definitions and parsers for `Core.VerifyOptions` and
`Laurel.LaurelVerifyOptions`. -/

public section

open Strata
open Core (VerifyOptions VerboseMode VerificationMode CheckLevel)
open Laurel (LaurelVerifyOptions LaurelTranslateOptions)

def parseCheckMode (pflags : ParsedFlags)
    (default : VerificationMode := .deductive) : IO VerificationMode :=
  match pflags.getString "check-mode" with
  | .none => pure default
  | .some s => match VerificationMode.ofString? s with
    | .some m => pure m
    | .none => exitFailure s!"Invalid check mode: '{s}'. Must be {VerificationMode.options}."

def parseCheckLevel (pflags : ParsedFlags)
    (default : CheckLevel := .minimal) : IO CheckLevel :=
  match pflags.getString "check-level" with
  | .none => pure default
  | .some s => match CheckLevel.ofString? s with
    | .some l => pure l
    | .none => exitFailure s!"Invalid check level: '{s}'. Must be {CheckLevel.options}."

/-- Common CLI flags for VerifyOptions fields.
    Commands can append these to their own flags list.
    Note: `parseOnly`, `typeCheckOnly`, and `checkOnly` are omitted here
    because they are specific to the `verify` command. -/
def verifyOptionsFlags : List Flag := [
  { name := "check-mode",
    help := s!"Check mode: {VerificationMode.options}. Default: 'deductive'.",
    takesArg := .arg "mode" },
  { name := "check-level",
    help := s!"Check level: {CheckLevel.options}. Default: 'minimal'.",
    takesArg := .arg "level" },
  { name := "verbose", help := "Enable verbose output." },
  { name := "quiet", help := "Suppress warnings on stderr." },
  { name := "profile", help := "Print elapsed time for each pipeline step." },
  { name := "sarif", help := "Write results as SARIF to <file>.sarif." },
  { name := "solver",
    help := s!"SMT solver executable (default: {Core.defaultSolver}).",
    takesArg := .arg "name" },
  { name := "solver-timeout",
    help := "Solver timeout in seconds (default: 10).",
    takesArg := .arg "seconds" },
  { name := "vc-directory",
    help := "Store VCs in SMT-Lib format in <dir>.",
    takesArg := .arg "dir" },
  { name := "no-solve",
    help := "Generate SMT-Lib files but do not invoke the solver." },
  { name := "stop-on-first-error",
    help := "Exit after the first verification error." },
  { name := "unique-bound-names",
    help := "Use globally unique names for quantifier-bound variables." },
  { name := "use-array-theory",
    help := "Use SMT-LIB Array theory instead of axiomatized maps." },
  { name := "remove-irrelevant-axioms",
    help := "Prune irrelevant axioms: 'off', 'aggressive', or 'precise'.",
    takesArg := .arg "mode" },
  { name := "overflow-checks",
    help := "Comma-separated overflow checks to enable (signed,unsigned,float64,all,none).",
    takesArg := .arg "checks" },
  { name := "incremental",
    help := "Use incremental solver backend (stdin/stdout) instead of batch file I/O." },
  { name := "path-cap",
    help := "Maximum continuing paths between statements. 'none' (default) disables; N merges paths when count exceeds N.",
    takesArg := .arg "N|none" },
  { name := "parallel",
    help := "Number of parallel solver workers (default: 1, sequential).",
    takesArg := .arg "N" }
]

/-- Build a VerifyOptions from parsed CLI flags, starting from a base config.
    Fields not present in the flags keep their base values.
    Note: boolean flags can only enable a setting; a `true` in the base
    cannot be turned off from the CLI (there is no `--no-X` syntax). -/
def parseVerifyOptions (pflags : ParsedFlags)
    (base : VerifyOptions := VerifyOptions.default) : IO VerifyOptions := do
  let checkMode ← parseCheckMode pflags base.checkMode
  let checkLevel ← parseCheckLevel pflags base.checkLevel
  let solverTimeout ← match pflags.getString "solver-timeout" with
    | .none => pure base.solverTimeout
    | .some s => match s.toNat? with
      | .some n => pure n
      | .none => exitFailure s!"Invalid solver timeout: '{s}'"
  let noSolve := pflags.getBool "no-solve"
  let removeIrrelevantAxioms ← match pflags.getString "remove-irrelevant-axioms" with
    | .none => pure base.removeIrrelevantAxioms
    | .some "off" => pure .Off
    | .some "aggressive" => pure .Aggressive
    | .some "precise" => pure .Precise
    | .some s => exitFailure s!"Invalid remove-irrelevant-axioms mode: '{s}'. Must be 'off', 'aggressive', or 'precise'."
  let overflowChecks := match pflags.getString "overflow-checks" with
    | .none => base.overflowChecks
    | .some s => s.splitOn "," |>.foldl (fun acc c =>
        match c.trimAscii.toString with
        | "signed"   => { acc with signedBV := true }
        | "unsigned" => { acc with unsignedBV := true }
        | "float64"  => { acc with float64 := true }
        | "none"     => { signedBV := false, unsignedBV := false, float64 := false }
        | "all"      => { signedBV := true, unsignedBV := true, float64 := true }
        | _          => acc) { signedBV := false, unsignedBV := false, float64 := false }
  let pathCap ← match pflags.getString "path-cap" with
    | .none => pure base.pathCap
    | .some "none" => pure .none
    | .some s => match s.toNat? with
      | .some n => if n == 0 then exitFailure "--path-cap must be at least 1 or 'none'."
                   else pure (.some n)
      | .none => exitFailure s!"Invalid path-cap: '{s}'. Must be a positive number or 'none'."
  let parallelWorkers ← match pflags.getString "parallel" with
    | .none => pure base.parallelWorkers
    | .some s => match s.toNat? with
      | .some n => if n == 0 then exitFailure "--parallel must be at least 1."
                   else pure n
      | .none => exitFailure s!"Invalid parallel workers: '{s}'. Must be a positive number."
  let vcDirectory := (pflags.getString "vc-directory" |>.map (⟨·⟩ : String → System.FilePath)).orElse (fun _ => base.vcDirectory)
  let skipSolver := noSolve || base.skipSolver
  if skipSolver && vcDirectory.isNone then
    exitFailure "--no-solve requires --vc-directory to specify where SMT files are stored."
  pure { base with
    verbose := if pflags.getBool "verbose" then .normal
              else if pflags.getBool "quiet" then .quiet
              else base.verbose,
    solver := pflags.getString "solver" |>.getD base.solver,
    solverTimeout,
    checkMode, checkLevel,
    stopOnFirstError := pflags.getBool "stop-on-first-error" || base.stopOnFirstError,
    uniqueBoundNames := pflags.getBool "unique-bound-names" || base.uniqueBoundNames,
    useArrayTheory := pflags.getBool "use-array-theory" || base.useArrayTheory,
    removeIrrelevantAxioms,
    outputSarif := pflags.getBool "sarif" || base.outputSarif,
    profile := pflags.getBool "profile" || base.profile,
    incremental := if noSolve then false else pflags.getBool "incremental" || base.incremental,
    skipSolver,
    alwaysGenerateSMT := noSolve || base.alwaysGenerateSMT,
    overflowChecks,
    vcDirectory,
    pathCap,
    parallelWorkers
  }

/-- Additional CLI flags for `LaurelVerifyOptions` fields that are not already
    covered by `verifyOptionsFlags`. -/
def laurelTranslateFlags : List Flag := [
  { name := "keep-all-files",
    help := "Store intermediate Laurel and Core programs in <dir>.",
    takesArg := .arg "dir" }
]

/-- All CLI flags accepted by Laurel verify commands. -/
def laurelVerifyOptionsFlags : List Flag := verifyOptionsFlags ++ laurelTranslateFlags

/-- Build a `LaurelVerifyOptions` from parsed CLI flags. -/
def parseLaurelVerifyOptions (pflags : ParsedFlags)
    (base : LaurelVerifyOptions := default) : IO LaurelVerifyOptions := do
  let verifyOptions ← parseVerifyOptions pflags base.verifyOptions
  let keepAllFilesPrefix := (pflags.getString "keep-all-files").orElse
    (fun _ => base.translateOptions.keepAllFilesPrefix)
  let translateOptions : LaurelTranslateOptions :=
    { base.translateOptions with
      keepAllFilesPrefix
      overflowChecks := verifyOptions.overflowChecks
      useArrayTheory := verifyOptions.useArrayTheory }
  return { translateOptions, verifyOptions }

end -- public section
