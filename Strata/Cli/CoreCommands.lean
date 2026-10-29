/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Lean.Parser.Extension
public import Strata.Cli.Framework
public import Strata.Cli.VerifyOptions
public import Strata.Cli.DialectCommands
public import Strata.Languages.Core.Verifier
public import Strata.Languages.Core.IncrementalSolve
public import Strata.Languages.Core.SarifOutput
public import Strata.Pipeline.Context
public import Strata.Languages.B3.Verifier.Program
public import Strata.Transform.ProcedureInlining
public import StrataDDM.Util.IO
public import Strata.SimpleAPI
public import StrataDDM.BuiltinDialects
public meta import Strata.Cli.Framework
public meta import Strata.Cli.VerifyOptions
public meta import Strata.Cli.DialectCommands
public meta import Strata.Languages.Core
public meta import Strata.Languages.B3.DDMTransform.ParseCST
public meta import Strata.DL.SMT.DDMTransform.Parse

public section

open Strata
open StrataDDM.Elab (LoadedDialects)

open Core (VerifyOptions VerboseMode VerificationMode CheckLevel)

namespace Strata.Cli

/-- Read and parse a Strata program file via the DDM API. Returns the parsed
    program and the input context (for source location resolution). Throws an
    `IO.userError` with formatted diagnostics on parse failure, and a separate
    error if the file defines a dialect rather than a program. -/
private def readStrataProgram (fm : StrataDDM.DialectFileMap) (file : String)
    : IO (StrataDDM.Program × Lean.Parser.InputContext) := do
  let text ← StrataDDM.Util.readInputSource file
  let displayPath := StrataDDM.Util.displayName file
  let inputCtx := Lean.Parser.mkInputContext text displayPath
  match ← StrataDDM.readStrataText fm displayPath text.toUTF8 with
  | .program pgm => pure (pgm, inputCtx)
  | .dialect _ =>
    throw (IO.userError s!"Expected a program file, got a dialect: {file}")

/-! Canonical phase names (`AbstractedPhase.name`) for the passes supported
    by the `transform` command. The CLI's help text and pass dispatch use
    these instead of string literals, so they cannot drift from the
    registry in `Strata.Languages.Core`. -/

private def inlineProceduresPass : String := Strata.Core.passInlineAll.phase.name
private def insertLoopInvariantAssertsPass : String := Strata.Core.passInsertLoopInvariantAsserts.phase.name
private def loopElimPass : String := Strata.Core.passLoopElim.phase.name
private def callElimPass : String := Strata.Core.passCallElim.phase.name
private def filterProceduresPass : String := (Strata.Core.passFilterProcedures []).phase.name
private def removeIrrelevantAxiomsPass : String := (Strata.Core.passRemoveIrrelevantAxioms []).phase.name

private def validPasses : String := String.intercalate ", " [
  inlineProceduresPass, insertLoopInvariantAssertsPass, loopElimPass,
  callElimPass, filterProceduresPass, removeIrrelevantAxiomsPass]

/-- A single transform pass together with the `--procedures`/`--functions`
    that were specified immediately after it on the command line. -/
private structure PassConfig where
  name : String
  procedures : List String := []
  functions : List String := []
deriving Inhabited

/-- The pipeline `verify` runs (`none` = the default order) together with any notes to print
    before verification.

    A resolver sets `notes` to report a difference between the pipeline it returned and the one
    the caller asked for, such as the checks added for what a registered pipeline assumes of its
    input. -/
structure PipelineChoice where
  pipeline : Option (Core.ValidatedPipeline Core.ProgramFactSet.empty) := none
  notes : List String := []

/-- A binary's answer to which pipeline `verify` runs: the flags it accepts for choosing one,
    the phases it admits, and the resolution from the one to the other. The default value
    accepts `--phases` and admits every phase Core defines. A binary keeping a registry of
    pipelines supplies a value that refuses a list it does not know and carries flags of its
    own, such as `--pipeline`. -/
structure PipelineResolver where
  /-- Extra `verify` flags this resolver accepts, added to the command's flag list so they
      appear in `--help` and parse like the built-in ones. -/
  extraFlags : List Flag := []
  /-- The pipeline to run, with whatever the run has to report about it, or a message to exit
      with. -/
  resolve : ParsedFlags → Core.VerifyOptions → Except String PipelineChoice :=
    fun pflags options =>
      match pflags.getString "phases" with
      | none => .ok {}
      | some names => do
        let phases ← Strata.Core.resolvePhases (Strata.Core.nameablePhases options)
          (names.splitToList (· == ','))
          (hint := "Use --display-phases to see the available phases.")
        let vp ← Strata.Core.validatePipeline phases
        pure { pipeline := some vp }
  /-- Every phase this resolver accepts a name for. `--display-phases` lists these, so a
      resolver overriding `resolve` states here what it will accept, or its help text and
      what it takes would drift apart. -/
  nameable : List Core.PipelinePhase := Strata.Core.nameablePhases
  /-- What this binary calls the flags that select and explain phases. -/
  flagNames : Core.PhaseFlagNames :=
    { select := "--phases", displayContracts := "--display-phase-contracts" }

/-- Walk the ordered flag entries and bind each `--procedures`/`--functions`
    to the most recent `--pass`. -/
private def buildPassConfigs (entries : Array (String × Option String))
    : IO (Array PassConfig) := do
  let mut configs : Array PassConfig := #[]
  for (flag, value) in entries do
    match flag with
    | "pass" => configs := configs.push { name := value.getD "" }
    | "procedures" =>
      let some cur := configs.back? | exitFailure "--procedures must appear after a --pass"
      let procs := (value.getD "").splitToList (· == ',')
      configs := configs.pop.push { cur with procedures := cur.procedures ++ procs }
    | "functions" =>
      let some cur := configs.back? | exitFailure "--functions must appear after a --pass"
      let fns := (value.getD "").splitToList (· == ',')
      configs := configs.pop.push { cur with functions := cur.functions ++ fns }
    | _ => pure ()
  return configs

def transformCommand (dialects : LoadedDialects) : Command where
  name := "transform"
  args := [ "file" ]
  flags := [
    includeFlag,
    { name := "pass",
      help := s!"Transform pass to apply (repeatable, applied left to right). \
               Valid passes: {validPasses}. \
               --procedures and --functions after a --pass apply to that pass.",
      takesArg := .repeat "name" },
    { name := "procedures",
      help := s!"Comma-separated procedure names for the preceding --pass. \
               For {filterProceduresPass}: procedures to keep. \
               For {inlineProceduresPass}: procedures to inline.",
      takesArg := .repeat "procs" },
    { name := "functions",
      help := s!"Comma-separated function names for the preceding --pass (used by {removeIrrelevantAxiomsPass}).",
      takesArg := .repeat "funcs" }]
  help := "Apply one or more transforms to a Core program and print the result."
  callback := fun v pflags => do
    let file := v[0]
    let passConfigs ← buildPassConfigs pflags.entries
    if passConfigs.isEmpty then
      exitFailure s!"No --pass specified. Valid passes: {validPasses}."
    let fm ← pflags.buildDialectFileMap dialects
    -- Read and parse the Core program
    let (pgm, _) ← readStrataProgram fm file
    match Strata.strataProgramToCore pgm with
    | .error msg =>
      exitFailure msg
    | .ok initProgram =>
      -- Validate and convert pass configs to TransformPass values.
      let mut passes : List Core.PipelinePhase := []
      for pc in passConfigs do
        if pc.name == inlineProceduresPass then
          if pc.procedures.isEmpty then
            passes := passes ++ [Strata.Core.passInlineAll]
          else
            passes := passes ++ [Strata.Core.passInlineMatching pc.procedures]
        else if pc.name == insertLoopInvariantAssertsPass then
          passes := passes ++ [Strata.Core.passInsertLoopInvariantAsserts]
        else if pc.name == loopElimPass then
          passes := passes ++ [Strata.Core.passLoopElim]
        else if pc.name == callElimPass then
          passes := passes ++ [Strata.Core.passCallElim]
        else if pc.name == filterProceduresPass then
          if pc.procedures.isEmpty then
            exitFailure s!"{filterProceduresPass} requires --procedures"
          passes := passes ++ [Strata.Core.passFilterProcedures pc.procedures]
        else if pc.name == removeIrrelevantAxiomsPass then
          if pc.functions.isEmpty then
            exitFailure s!"{removeIrrelevantAxiomsPass} requires --functions"
          passes := passes ++ [Strata.Core.passRemoveIrrelevantAxioms pc.functions]
        else
          exitFailure s!"Unknown pass '{pc.name}'. Valid passes: {validPasses}."
      -- Run all passes in a single CoreTransformM chain so fresh variable
      -- counters accumulate and cached analyses are reused across passes.
      match ← (Strata.Core.runTransforms initProgram passes).toBaseIO with
      | .ok (program, _) => IO.print (Core.formatProgram program)
      | .error e => exitFailure s!"Transform failed: {e}"

/-- A rejected `--phases` list gets a pointer to the contract table, which is where the
    reason lives: the table shows, per phase, which requirement went unmet. An unknown phase
    name is a different problem and already carries its own hint, so it is left alone, and a
    command that offers no contracts flag adds nothing. -/
private def withContractsHint (resolver : PipelineResolver) (pflags : ParsedFlags)
    (msg : String) : String :=
  let flag := resolver.flagNames.displayContracts
  if (pflags.getString "phases").isSome && !flag.isEmpty
      && !msg.startsWith "Unknown phase name" then
    msg ++ s!"\n\nTo see where each phase's requirements are met across this order, run {flag}."
  else msg

/-- The `verify` command. `backendOf` gives the discharge and the sessions of the solver
    backend an invocation selects, both `none` to use Core's own discharge and local solver
    processes; the discharge uses Core's own default when both are `none`. -/
def verifyCommand (dialects : LoadedDialects)
    (extraFlags : List Flag := [])
    (checkOptions : Core.VerifyOptions → ParsedFlags → List String := fun _ _ => [])
    (resolver : PipelineResolver := {})
    (backendOf : ParsedFlags → Core.VerifyOptions →
      Option Core.MkDischargeFn × Option Core.IncrementalSolve.SessionFactory) :
    Command where
  name := "verify"
  args := [ "file" ]
  flags := includeFlag :: verifyOptionsFlags ++ extraFlags ++ resolver.extraFlags ++ [
    { name := "phases", help := "Run these phases, in this order (comma-separated). \
        Without a file, report whether they compose.", takesArg := .arg "names" },
    { name := "display-phases", help := "Print the phases available and the default order." },
    { name := "display-phase-contracts",
      help := "Print what each phase requires, delivers and preserves." },
    { name := "check", help := "Process up until SMT generation, but don't solve." },
    { name := "type-check", help := "Exit after semantic dialect's type inference/checking." },
    { name := "parse-only", help := "Exit after DDM parsing and type checking." },
    { name := "output-format", help := "Output format (only 'sarif' supported).", takesArg := .arg "format" },
    { name := "procedures", help := "Verify only the specified procedures (comma-separated).", takesArg := .arg "procs" }]
  help := "Verify a Strata program file (.core.st or .b3.st)."
  -- Both answer without a file to verify: one lists the phases, the other checks an order.
  reportFlags :=
    [("display-phases", fun _ =>
        -- The extras are whatever the resolver accepts beyond the default order, so the
        -- text cannot advertise less than `--phases` takes.
        let dflt := Strata.Core.corePipelinePhases
        let extras := resolver.nameable.filter fun p =>
          !dflt.any fun d => Strata.Core.phaseName d == Strata.Core.phaseName p
        IO.println (Strata.Core.displayPhasesText resolver.flagNames dflt (extras := extras))),
     -- Tables the order asked for, so `#` marks a requirement that order leaves unmet; with no
     -- `--phases` it tables the default order, which is the one a caller is comparing against.
     ("display-phase-contracts", fun pflags => do
        let options ← parseVerifyOptions pflags { VerifyOptions.default with verbose := .quiet }
        let phases ← match pflags.getString "phases" with
          | none => pure (Strata.Core.corePipelinePhases options)
          | some names =>
            match Strata.Core.resolvePhases (Strata.Core.nameablePhases options)
                    (names.splitToList (· == ','))
                    (hint := "Use --display-phases to see the available phases.") with
            | .ok phases => pure phases
            | .error msg => exitUserError msg
        IO.println (Strata.Core.displayPhaseContractsText phases)),
     ("phases", fun pflags => do
        -- The same options the run would use, since a resolver may compare a list against
        -- the default order for the options in effect: reporting under different ones could
        -- accept a list the run then refuses.
        let opts ← parseVerifyOptions pflags { VerifyOptions.default with verbose := .quiet }
        match resolver.resolve pflags opts with
        | .ok choice =>
          choice.notes.forM IO.println
          match choice.pipeline with
          | none => IO.println "This is the default order."
          | some vp =>
            let names := ", ".intercalate (vp.phases.map Strata.Core.phaseName)
            IO.println s!"This order composes: {names}"
        | .error msg => exitUserError (withContractsHint resolver pflags msg))]
  callback := fun v pflags => do
    let file := v[0]
    let proceduresToVerify := pflags.getString "procedures" |>.map (·.splitToList (· == ','))
    let opts ← parseVerifyOptions pflags { VerifyOptions.default with verbose := .quiet }
      (inputFile := some file)
    let opts := { opts with
      checkOnly := pflags.getBool "check",
      typeCheckOnly := pflags.getBool "type-check",
      parseOnly := pflags.getBool "parse-only",
      proceduresToVerify := proceduresToVerify,
      outputSarif := opts.outputSarif || pflags.getString "output-format" == some "sarif" }
    let optionIssues := checkOptions opts pflags
    unless optionIssues.isEmpty do
      exitUserError (String.intercalate "\n" optionIssues)
    let (ownDischarge, mkSession) := backendOf pflags opts
    let choice ← match resolver.resolve pflags opts with
      | .ok c => pure c
      | .error msg => exitUserError (withContractsHint resolver pflags msg)
    let pipeline := choice.pipeline
    -- `--procedures` narrows verification by splicing `filterProcedures`, which only the
    -- default pipeline does. A caller-supplied pipeline is run exactly as given, so the
    -- filter would be silently dropped and the run would report procedures the caller did
    -- not ask about. Refuse the combination rather than mislead.
    if pipeline.isSome && proceduresToVerify.isSome then
      exitUserError <|
        s!"--procedures cannot be combined with {resolver.flagNames.select} or a named "
          ++ "pipeline: the supplied pipeline is run exactly as given, so the procedure "
          ++ "filter would be silently dropped. Omit --procedures, or run the default "
          ++ "pipeline, which applies it."
    -- Only the Core path takes a pipeline: a B3 program never reaches the Core phases.
    -- Accepting a phase list for B3 would run something other than what the caller asked for.
    if pipeline.isSome && (file.endsWith ".b3.st" || file.endsWith ".b3cst.st") then
      exitUserError <|
        s!"The selected pipeline applies to Core programs only, and {file} is not one."
    -- Print notes only after the Core-only check above, so a rejected run prints nothing.
    choice.notes.forM IO.println
    -- `--keep-all-files` has no effect for B3 files: the B3 pipeline runs no
    -- Core transform phases, so there are no intermediate programs to emit.
    -- Reject it up front — before the parse-only / type-check-only early
    -- returns below, which would otherwise silently ignore the flag — and exit
    -- with the user-error code (1), not internal-error (3).
    if (file.endsWith ".b3.st" || file.endsWith ".b3cst.st") && opts.keepAllFilesPrefix.isSome then
      exitUserError "--keep-all-files is not supported for B3 files (.b3.st/.b3cst.st)."
    let fm ← pflags.buildDialectFileMap dialects
    let mode := if opts.profile then Strata.Pipeline.OutputMode.profile else .quiet
    let pctx ← Strata.Pipeline.PipelineContext.create (outputMode := mode)
    let (pgm, inputCtx) ← pctx.withPhase "parse" do readStrataProgram fm file
    println! s!"Successfully parsed."
      if opts.parseOnly then return
      if opts.typeCheckOnly then
        let ans := typeCheck inputCtx pgm opts
        match ans with
        | .error e =>
          println! f!"{e.formatRange (some inputCtx.fileMap) true} {e.message}"
          IO.Process.exit ExitCode.userError
        | .ok _ =>
          println! f!"Program typechecked."
          return
      -- Full verification
      let vcResults ← try
        if file.endsWith ".b3.st" || file.endsWith ".b3cst.st" then
          let ast ← match B3.Verifier.programToB3AST pgm with
            | Except.error msg => throw (IO.userError s!"Failed to convert to B3 AST: {msg}")
            | Except.ok ast => pure ast
          let solver ← B3.Verifier.createInteractiveSolver opts.solver
          let reports ← B3.Verifier.programToSMT ast solver
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
          pure #[]
        else if pgm.dialect == "Boole" then
          throw <| IO.Error.userError "Boole dialect support requires the StrataBoole package"
        else
          Strata.Core.verify pgm inputCtx opts
            (pipeline := pipeline) (mkDischarge := ownDischarge) (pipelineCtx := pctx)
            (mkSession := mkSession)
      catch e =>
        println! f!"{e}"
        IO.Process.exit ExitCode.internalError
      if opts.outputSarif then
        let uri := Strata.Uri.file file
        let files := Map.empty.insert uri inputCtx.fileMap
        Core.Sarif.writeSarifOutput opts.checkMode files vcResults (file ++ ".sarif")
      for vcResult in vcResults do
        let posStr := Imperative.MetaData.formatFileRangeD vcResult.obligation.metadata (some inputCtx.fileMap)
        -- `formatOutcome` omits the counterexample model, so render it here,
        -- inline on the obligation line to keep one line per obligation for
        -- tools that parse this output.
        let modelFmt :=
          if vcResult.verbose >= .models && !vcResult.lexprModel.isEmpty then
            f!" Model: {Std.format vcResult.lexprModel}"
          else f!""
        println! f!"{posStr} [{vcResult.obligation.label}]: \
                      {vcResult.formatOutcome}{modelFmt}"
      let success := vcResults.all Core.VCResult.isSuccess
      if success && !opts.checkOnly then
        println! f!"All {vcResults.size} goals passed."
      else if success && opts.checkOnly then
        println! f!"Skipping verification."
      else
        let provedGoalCount := (vcResults.filter Core.VCResult.isSuccess).size
        let failedGoalCount := (vcResults.filter Core.VCResult.isNotSuccess).size
        -- Encoding failures, solver crashes, or per-check SMT errors (exit 3)
        let hasImplError := vcResults.any (fun r => r.isImplementationError || r.hasSMTError)
        -- Assertion violations that are not timeouts or internal errors (exit 2)
        let hasFailure := vcResults.any (fun r => !r.isSuccess && !r.isTimeout && !r.isImplementationError && !r.hasSMTError)
        println! f!"Finished with {provedGoalCount} goals passed, {failedGoalCount} failed."
        if hasImplError then
          IO.Process.exit ExitCode.internalError
        else if hasFailure then
          IO.Process.exit ExitCode.failuresFound

/-- A named solver backend: the `--solver` value it answers to and the discharge
    factory that handles verification queries for that solver. -/
structure SolverBackend where
  name : String
  /-- Extra `verify` flags this backend accepts. They are added to the command's flag
      list, so they appear in `--help` and parse like the built-in flags. -/
  extraFlags : List Flag := []
  /-- Returns one message per option this backend cannot apply in the given invocation
      (empty means every option is fine). -/
  checkOptions : Core.VerifyOptions → ParsedFlags → List String := fun _ _ => []
  mkDischarge : ParsedFlags → Core.MkDischargeFn
  /-- The solvers `--incremental` walks the obligation tree with. Without them, or when this
      answers `none` for an invocation, every obligation goes through `mkDischarge`, as
      without `--incremental`. -/
  mkSession : Option (ParsedFlags → Option Core.IncrementalSolve.SessionFactory) := none

/-- The discharge and the sessions of the backend `--solver` selects, both `none` when no
    backend answers to it, which leaves Core its own discharge and local solver processes. -/
private def dispatchBackend (backends : List SolverBackend) (pflags : ParsedFlags)
    (options : Core.VerifyOptions) :
    Option Core.MkDischargeFn × Option Core.IncrementalSolve.SessionFactory :=
  match backends.find? (·.name == options.solver) with
  | none => (none, none)
  | some b => (some (b.mkDischarge pflags), b.mkSession.bind (· pflags))

/-- Build one discharge factory that picks a backend by the `--solver` value,
    falling back to the default process solver when none matches. -/
private def dispatchDischarge (backends : List SolverBackend) (pflags : ParsedFlags) : Core.MkDischargeFn :=
  fun options counter tempDir vars md label termCache captured ctx =>
    match backends.find? (·.name == options.solver) with
    | some b => b.mkDischarge pflags options counter tempDir vars md label termCache captured ctx
    | none   => Core.mkDischargeFn options counter tempDir vars md label termCache captured ctx

/-- A backend's `extraFlags` apply only when that backend is selected. Returns a
    message for each such flag that is set under a different `--solver`. -/
private def foreignBackendFlagIssues (backends : List SolverBackend) (solver : String)
    (pflags : ParsedFlags) : List String :=
  backends.flatMap fun b =>
    if b.name == solver then []
    else b.extraFlags.filterMap fun f =>
      if pflags.getBool f.name then some s!"--{f.name} only applies to --solver {b.name}" else none

def baseDialects : LoadedDialects :=
  StrataDDM.Elab.LoadedDialects.builtin
    |>.addDialect! Strata.Core
    |>.addDialect! B3CST
    |>.addDialect! Strata.smtReservedKeywordsDialect
    |>.addDialect! Strata.SMTCore
    |>.addDialect! Strata.SMT
    |>.addDialect! Strata.SMTResponse

structure CliFrontend where
  dialects : List StrataDDM.Dialect
  group : Core.MkDischargeFn → CommandGroup

/-- Build the command groups, wiring the solver-aware commands to dispatch over
    the given backends. -/
def buildCommandGroups (backends : List SolverBackend := [])
    (resolver : PipelineResolver := {}) (frontends : List CliFrontend := []) : List CommandGroup :=
  let dialects := frontends.foldl (init := baseDialects) fun ld f => f.dialects.foldl (·.addDialect! ·) ld
  let extraFlags := backends.flatMap (·.extraFlags)
  let mkDischargeOf := dispatchDischarge backends
  let checkOptions := fun (opts : Core.VerifyOptions) (pflags : ParsedFlags) =>
    foreignBackendFlagIssues backends opts.solver pflags ++
      ((backends.find? (·.name == opts.solver)).map (·.checkOptions opts pflags) |>.getD [])
  -- Commands that don't parse backend-specific flags use the empty-flag dispatch.
  let mkDischarge := mkDischargeOf {}
  [ { name := "Core"
      commands := [verifyCommand dialects extraFlags checkOptions resolver
                     (dispatchBackend backends),
                   transformCommand dialects, checkCommand dialects, toIonCommand dialects,
                   printCommand dialects, diffCommand dialects]
      commonFlags := [includeFlag] } ] ++
  frontends.map (·.group mkDischarge)

/-- The commands as a flat list. It threads the resolver through to `buildCommandGroups`, so
    the `verify` command keeps its pipeline flags; a binary that builds its commands from this
    list would otherwise have an ungated `--phases`. -/
def buildCommandList (backends : List SolverBackend := [])
    (resolver : PipelineResolver := {}) (frontends : List CliFrontend := []) : List Command :=
  (buildCommandGroups backends resolver frontends).foldl (init := []) fun acc g => acc ++ g.commands

def buildCommandMap (backends : List SolverBackend := [])
    (resolver : PipelineResolver := {}) (frontends : List CliFrontend := []) :
    Std.HashMap String Command :=
  (buildCommandList backends resolver frontends).foldl (init := {}) fun m c => m.insert c.name c

private def expectedCommandNames : List String :=
  ["check", "diff", "print", "toIon", "transform", "verify"]

private def commandNames (backends : List SolverBackend := []) : List String :=
  (buildCommandList backends).map (·.name) |>.mergeSort (· < ·)

-- A throwaway backend (reuses the default discharge factory) so the guards below
-- can exercise a non-empty registry without needing an external solver to build.
private def incrementalBackend : SolverBackend where
  name := "incremental"
  mkDischarge := fun _pflags options counter tempDir vars md label termCache captured ctx =>
    Core.mkDischargeFn { options with incremental := true }
      counter tempDir vars md label termCache captured ctx

#guard commandNames [] == expectedCommandNames
#guard (buildCommandMap []).size == (buildCommandList []).length

-- Adding a backend does not change the exposed command set.
#guard (buildCommandMap [incrementalBackend]).size == (buildCommandMap []).size
#guard commandNames [incrementalBackend] == expectedCommandNames

-- A test-only backend with one extra flag, to exercise `foreignBackendFlagIssues`.
private def flagTestBackend : SolverBackend where
  name := "tb"
  extraFlags := [{ name := "tb-opt", help := "", takesArg := .arg "v" }]
  mkDischarge := fun _ => Core.mkDischargeFn

-- A backend flag set under a different `--solver` is rejected; under its own backend, allowed.
#guard foreignBackendFlagIssues [flagTestBackend] "other" (({} : ParsedFlags).insert "tb-opt" (some "x"))
  == ["--tb-opt only applies to --solver tb"]
#guard foreignBackendFlagIssues [flagTestBackend] "tb" (({} : ParsedFlags).insert "tb-opt" (some "x")) == []

-- A test-only resolver carrying a flag of its own, which is the shape a binary with a
-- registry of pipelines has.
private def flagTestResolver : PipelineResolver where
  extraFlags := [{ name := "pipeline", help := "", takesArg := .arg "name" }]

-- Checks the resolver's flag reaches `verify` through both builders.
private def verifyCommandFrom (map : Std.HashMap String Command) : Option Command := map["verify"]?

private def offersPipelineFlag (cmd : Command) : Bool := cmd.flags.any (·.name == "pipeline")

#guard ((buildCommandList [] flagTestResolver).find? (·.name == "verify")).map offersPipelineFlag
  == some true
#guard (verifyCommandFrom (buildCommandMap [] flagTestResolver)).map offersPipelineFlag
  == some true
#guard ((verifyCommandFrom (buildCommandMap [])).map offersPipelineFlag) == some false

def commandGroups : List CommandGroup := buildCommandGroups []
def commandList : List Command := buildCommandList []
def commandMap : Std.HashMap String Command := buildCommandMap []

end Strata.Cli

end -- public section
