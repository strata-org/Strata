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
import Strata.Languages.Laurel.Grammar.AbstractToConcreteTreeTranslator
import Strata.SimpleAPI

namespace Strata.Pipeline

/-- The outcome of the full pyAnalyzeLaurel pipeline.
    Error details are derived from the accumulated messages in PipelineContext. -/
public inductive PyAnalyzeOutcome where
  /-- Pipeline completed verification successfully. -/
  | verified (vcResults : _root_.Core.VCResults) (coreProgram : Core.Program)
  /-- Pipeline aborted due to a fatal error. -/
  | failed

/-- Configuration for the pyAnalyzeLaurel pipeline. -/
public structure PyAnalyzeConfig where
  filePath : String
  specDir : System.FilePath
  dispatchModules : Array String := #[]
  pyspecModules : Array String := #[]
  sourcePath : Option String := none
  keepAllFilesPrefix : Option String := none
  verifyOptions : Core.VerifyOptions
  entryPoint : Core.EntryPoint := Core.EntryPoint.roots
  isBugFinding : Bool := true
  outputMode : OutputMode := .default
  skipVerification : Bool := false
  typedPython : Bool := false
  profilePipeline : Bool := true
  metricsHandle : Option IO.FS.Handle := none

private def runPipeline (config : PyAnalyzeConfig)
    : PipelineM (PyAnalyzeOutcome × Statistics) := do
  let combinedLaurel ← withPhase "pythonAndSpecToLaurel" do
    Strata.pythonAndSpecToLaurel
      (specDir := config.specDir) (typedPython := config.typedPython)
      config.filePath config.dispatchModules config.pyspecModules config.sourcePath

  if config.outputMode == .verbose then
    let _ ← (show IO Unit from do
      IO.println "---- BEGIN Laurel Program ----"
      IO.println (toString (Std.format combinedLaurel))
      IO.println "---- END Laurel Program ----").toBaseIO

  let uri := config.sourcePath.getD config.filePath

  let (coreProgram, laurelPassStats) ← withPhase "laurelToCore" do
    let ctx ← read
    let laurelResult ←
      Strata.translateCombinedLaurelWithLowered combinedLaurel
        (keepAllFilesPrefix := config.keepAllFilesPrefix)
        (pipelineCtx := some ctx) |>.toBaseIO
    match laurelResult with
    | .ok (coreOpt, diags, _, stats) =>
      let phase ← getPhase
      for msg in PipelineMessage.fromDiagnostics phase diags do
        addMessage msg
        if msg.kind.impact.isFatal then throw ()
      match coreOpt with
      | some core => pure (core, stats)
      | none =>
        emitMessageAndAbort (file := uri) .laurelToCoreError s!"Laurel to Core translation failed: {diags}"
    | .error e =>
      emitMessageAndAbort (file := uri) .laurelToCoreError s!"Laurel translation error: {e}"

  if config.outputMode == .verbose then
    let _ ← (show IO Unit from do
      IO.println "---- BEGIN Core Program ----"
      IO.println (toString coreProgram)
      IO.println "---- END Core Program ----").toBaseIO

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

  let vcResults ←
    match verifyResult with
    | .ok r =>
      pure r.mergeByAssertion
    | .error msg =>
      emitMessageAndAbort (file := uri) .verificationError msg

  for vcResult in vcResults do
    match vcResult.outcome with
    | .error (.encoding msg) =>
      emitMessageAndAbort (file := uri) .verificationError msg
    | .error (.solverTimeout msg) =>
      emitMessage .verificationTimeout msg
    | .error (.solverCrash msg) =>
      emitMessageAndAbort (file := uri) .verificationError msg
    | .ok _ => pure ()

  return (PyAnalyzeOutcome.verified vcResults coreProgram, laurelPassStats)

/-- Run the full pyAnalyzeLaurel pipeline: Python+PySpec to Laurel,
    Laurel to Core, then SMT verification.

    Accumulates pipeline messages from all phases. The caller is responsible
    for inspecting the outcome and accumulated messages to determine exit codes. -/
public def runPyAnalyzePipeline (config : PyAnalyzeConfig)
    : IO (PyAnalyzeOutcome × Statistics × PipelineContext) := do
  let ctx ← PipelineContext.create
    (outputMode := config.outputMode)
    (profilePipeline := config.profilePipeline)
    (metricsHandle := config.metricsHandle)
  let result ← runPipeline config |>.run ctx |>.toBaseIO
  match result with
  | .ok (outcome, stats) => return (outcome, stats, ctx)
  | .error () => return (.failed, {}, ctx)

end Strata.Pipeline
