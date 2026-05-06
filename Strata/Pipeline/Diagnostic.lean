/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Pipeline.Messages
public import Strata.Util.FileRange

namespace Strata.Pipeline

open Strata (DiagnosticType DiagnosticModel FileRange Uri)

/-- Map a `DiagnosticType` to a `MessageKind` for a given phase.
    Each phase has four message kinds corresponding to the four
    diagnostic severity levels. -/
public def MessageKind.fromDiagnosticType (phase : Phase) : DiagnosticType → MessageKind
  | .Warning =>
    { phase, category := "warning", impact := .internalWarning }
  | .UserError =>
    { phase, category := "userError", impact := .userCodeIssue }
  | .NotYetImplemented =>
    { phase, category := "notYetImplemented", impact := .knownLimitation }
  | .StrataBug =>
    { phase, category := "error", impact := .internalError }

/-- Convert a `DiagnosticModel` to a `PipelineMessage` using the given phase. -/
public def PipelineMessage.fromDiagnostic (phase : Phase) (d : DiagnosticModel) : PipelineMessage :=
  let file : System.FilePath := match d.fileRange.file with
    | .file path => path
  { file
    loc := d.fileRange.range
    kind := MessageKind.fromDiagnosticType phase d.type
    message := d.message }

/-- Convert a list of `DiagnosticModel` values to pipeline messages. -/
public def PipelineMessage.fromDiagnostics (phase : Phase) (ds : List DiagnosticModel)
    : Array PipelineMessage :=
  ds.toArray.map (PipelineMessage.fromDiagnostic phase)

end Strata.Pipeline
