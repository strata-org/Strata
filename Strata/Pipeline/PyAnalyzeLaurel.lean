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

/-- Full result of the pyAnalyzeLaurel pipeline. Warnings are always populated. -/
public structure PyAnalyzeResult where
  outcome : PyAnalyzeOutcome
  warnings : Array PipelineMessage
  timing : Array PhaseTimingEntry := #[]
  laurelPassStats : Statistics := {}

private def runPipeline (config : PyAnalyzeConfig)
    : PipelineM (PyAnalyzeOutcome × Statistics) := do
  -- Phase 0-3: Python + PySpec → Laurel
  startPhase (Phase.base "pythonAndSpecToLaurel" 0)
  let pipelineResult ← Strata.pythonAndSpecToLaurel
        (specDir := config.specDir)
        config.filePath config.dispatchModules config.pyspecModules config.sourcePath
        (profile := config.profile)
  Strata.addMessages pipelineResult.warnings

  let combinedLaurel ← match pipelineResult with
    | .success r _ => pure r
    | .failure (.userCode range msg) _ =>
      return (PyAnalyzeOutcome.userError range msg, {})
    | .failure (.knownLimitation msg) _ =>
      return (PyAnalyzeOutcome.knownLimitation msg, {})
    | .failure (.internal msg) _ =>
      return (PyAnalyzeOutcome.internalError msg, {})

  -- Phase 4-5: Laurel → Core
  startPhase (Phase.base "laurelToCore" 5)
  let (coreProgramOption, laurelTranslateErrors, _, laurelPassStats) ←
    match ← (Strata.translateCombinedLaurelWithLowered combinedLaurel
      (keepAllFilesPrefix := config.keepAllFilesPrefix)
      (profile := config.profile)).toBaseIO with
    | .ok r => pure r
    | .error e =>
      return (PyAnalyzeOutcome.internalError s!"Laurel translation error: {e}", {})

  let laurelMessages := PipelineMessage.fromDiagnostics (Phase.base "laurelToCore" 5) laurelTranslateErrors
  Strata.addMessages laurelMessages

  let coreProgram ← match coreProgramOption with
    | some core => pure core
    | none =>
      return (PyAnalyzeOutcome.internalError
        s!"Laurel to Core translation failed: {laurelTranslateErrors}", laurelPassStats)

  -- Skip verification if requested
  if config.skipVerification then
    return (PyAnalyzeOutcome.verified #[] coreProgram, laurelPassStats)

  -- Phase 7: SMT Verification
  startPhase (Phase.base "verification" 7)
  let userSourcePath := config.sourcePath.getD config.filePath
  let (_, userProcNames) := Strata.splitProcNames coreProgram [userSourcePath]
  let (proceduresToVerify, inlinePhases) :=
    if config.isBugFinding then
      let ⟨p, i⟩ := Core.chooseEntryProceduresAndBuildInlinePhases
        coreProgram userProcNames config.entryPoint
      (p, [i])
    else (userProcNames, [])

  let vcResults ← match ← Strata.Core.verifyProgram coreProgram config.verifyOptions
        (moreFns := Strata.Python.ReFactory)
        (proceduresToVerify := some proceduresToVerify)
        (externalPhases := [Strata.frontEndPhase])
        (prefixPhases := inlinePhases)
        (keepAllFilesPrefix := config.keepAllFilesPrefix)
        |>.toBaseIO with
    | .ok r => pure r.mergeByAssertion
    | .error msg =>
      return (PyAnalyzeOutcome.internalError msg, laurelPassStats)

  -- Collect verification errors into pipeline messages
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
public def runPyAnalyzePipeline (config : PyAnalyzeConfig) : IO PyAnalyzeResult := do
  let ctx ← PipelineContext.create
    (outputMode := config.outputMode)
    (skipTiming := config.skipTiming)
  let (outcome, stats) ← runPipeline config |>.run ctx
  ctx.endCurrentPhase
  let warnings ← ctx.messagesRef.get
  let timing ← ctx.timingRef.get
  return { outcome, warnings, timing, laurelPassStats := stats }

end Strata.Pipeline
