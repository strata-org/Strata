/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Pipeline.Diagnostic
public import Strata.Util.Statistics
public import Strata.Languages.Core.EntryPoint
public import Strata.Languages.Core.Verifier
import Strata.Languages.Python.PySpecPipeline
import Strata.Languages.Python.PyFactory
import Strata.SimpleAPI

namespace Strata.Pipeline

/-- The outcome of the full pyAnalyzeLaurel pipeline. -/
public inductive PyAnalyzeOutcome where
  /-- Pipeline completed verification successfully. -/
  | verified (vcResults : _root_.Core.VCResults) (coreProgram : Core.Program)
  /-- User code error detected during translation. -/
  | userError (range : SourceRange) (message : String)
  /-- Known limitation prevented pipeline completion. -/
  | knownLimitation (message : String)
  /-- Internal error. -/
  | internalError (message : String)

/-- Configuration for the pyAnalyzeLaurel pipeline. -/
public structure PyAnalyzeConfig where
  filePath : String
  specDir : System.FilePath
  dispatchModules : Array String := #[]
  pyspecModules : Array String := #[]
  sourcePath : Option String := none
  profile : Bool := false
  keepAllFilesPrefix : Option String := none
  verifyOptions : Core.VerifyOptions
  entryPoint : Core.EntryPoint := Core.EntryPoint.roots
  isBugFinding : Bool := true
  outputMode : OutputMode := .default
  skipVerification : Bool := false
  skipTiming : Bool := false
  metricsHandle : Option IO.FS.Handle := none

/-- Full result of the pyAnalyzeLaurel pipeline. Warnings are always populated. -/
public structure PyAnalyzeResult where
  outcome : PyAnalyzeOutcome
  warnings : Array PipelineMessage
  timing : Array PhaseTimingEntry := #[]
  laurelPassStats : Statistics := {}

private def runPipeline (config : PyAnalyzeConfig)
    : PipelineM (PyAnalyzeOutcome × Statistics) := do
  let pipelineResult ← withPhase "pythonAndSpecToLaurel" do
    let ctx ← read
    let r ← Strata.pythonAndSpecToLaurel
          (specDir := config.specDir)
          config.filePath config.dispatchModules config.pyspecModules config.sourcePath
          (pipelineCtx := ctx)
    pure r

  let combinedLaurel ← match pipelineResult with
    | .success r _ => pure r
    | .failure (.userCode range msg) _ =>
      return (PyAnalyzeOutcome.userError range msg, {})
    | .failure (.knownLimitation msg) _ =>
      return (PyAnalyzeOutcome.knownLimitation msg, {})
    | .failure (.internal msg) _ =>
      return (PyAnalyzeOutcome.internalError msg, {})

  let laurelResult ← withPhase "laurelToCore" do
    let ctx ← read
    (Strata.translateCombinedLaurelWithLowered combinedLaurel
      (keepAllFilesPrefix := config.keepAllFilesPrefix)
      (profile := config.profile)
      (pipelineCtx := some ctx)).toBaseIO

  let (coreProgramOption, laurelTranslateErrors, _, laurelPassStats) ←
    match laurelResult with
    | .ok r => pure r
    | .error e =>
      return (PyAnalyzeOutcome.internalError s!"Laurel translation error: {e}", {})

  let phase ← getPhase
  let laurelMessages := PipelineMessage.fromDiagnostics phase laurelTranslateErrors
  Strata.addMessages laurelMessages

  let coreProgram ← match coreProgramOption with
    | some core => pure core
    | none =>
      return (PyAnalyzeOutcome.internalError
        s!"Laurel to Core translation failed: {laurelTranslateErrors}", laurelPassStats)

  if config.skipVerification then
    return (PyAnalyzeOutcome.verified #[] coreProgram, laurelPassStats)

  let verifyResult ← withPhase "verification" do
    let ctx ← read
    let userSourcePath := config.sourcePath.getD config.filePath
    let (_, userProcNames) := Strata.splitProcNames coreProgram [userSourcePath]
    let (proceduresToVerify, inlinePhases) :=
      if config.isBugFinding then
        let ⟨p, i⟩ := Core.chooseEntryProceduresAndBuildInlinePhases
          coreProgram userProcNames config.entryPoint
        (p, [i])
      else (userProcNames, [])
    Strata.Core.verifyProgram coreProgram config.verifyOptions
        (moreFns := Strata.Python.ReFactory)
        (proceduresToVerify := some proceduresToVerify)
        (externalPhases := [Strata.frontEndPhase])
        (prefixPhases := inlinePhases)
        (keepAllFilesPrefix := config.keepAllFilesPrefix)
        (pipelineCtx := some ctx)
        |>.toBaseIO

  let vcResults ← match verifyResult with
    | .ok r => pure r.mergeByAssertion
    | .error msg =>
      return (PyAnalyzeOutcome.internalError msg, laurelPassStats)

  for vcResult in vcResults do
    match vcResult.outcome with
    | .error (.encoding msg) =>
      Strata.emitMessage .verificationError msg
    | .error (.solverTimeout msg) =>
      Strata.emitMessage .verificationTimeout msg
    | .error (.solverCrash msg) =>
      Strata.emitMessage .verificationError msg
    | .ok _ => pure ()

  return (PyAnalyzeOutcome.verified vcResults coreProgram, laurelPassStats)

/-- Run the full pyAnalyzeLaurel pipeline: Python+PySpec to Laurel,
    Laurel to Core, then SMT verification.

    Accumulates pipeline messages from all phases. The caller is responsible
    for printing warnings and handling the outcome (exit codes, SARIF, etc.). -/
public def runPyAnalyzePipeline (config : PyAnalyzeConfig) : IO (PyAnalyzeResult × PipelineContext) := do
  let ctx ← PipelineContext.create
    (outputMode := config.outputMode)
    (skipTiming := config.skipTiming)
    (metricsHandle := config.metricsHandle)
  let result ← (runPipeline config |>.run ctx).toBaseIO
  let warnings ← ctx.messagesRef.get
  let timing ← ctx.timingRef.get
  match result with
  | .ok (outcome, stats) =>
    let r : PyAnalyzeResult := { outcome, warnings, timing, laurelPassStats := stats }
    return (r, ctx)
  | .error () =>
    let r : PyAnalyzeResult :=
      { outcome := .internalError "Pipeline aborted due to fatal errors", warnings, timing }
    return (r, ctx)

end Strata.Pipeline
