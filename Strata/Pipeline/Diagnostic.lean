/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Pipeline.Messages
public import Strata.Util.FileRange

namespace Strata.Pipeline

open Strata (DiagnosticType DiagnosticModel FileRange Uri)

/-- Map a `DiagnosticType` to a `MessageKind`.
    Each diagnostic severity maps to a category and impact. -/
public def MessageKind.fromDiagnosticType : DiagnosticType → MessageKind
  | .Warning =>
    { category := "warning", impact := .internalWarning }
  | .UserError =>
    { category := "userError", impact := .userCodeIssue }
  | .NotYetImplemented =>
    { category := "notYetImplemented", impact := .knownLimitation }
  | .StrataBug =>
    { category := "error", impact := .internalError }

/-- Convert a `DiagnosticModel` to a `PipelineMessage` using the given phase. -/
public def PipelineMessage.fromDiagnostic (phase : Phase) (d : DiagnosticModel) : PipelineMessage :=
  let file : System.FilePath := match d.fileRange.file with
    | .file path => path
  { file
    loc := d.fileRange.range
    phase
    kind := MessageKind.fromDiagnosticType d.type
    message := d.message }

/-- Convert a list of `DiagnosticModel` values to pipeline messages. -/
public def PipelineMessage.fromDiagnostics (phase : Phase) (ds : List DiagnosticModel)
    : Array PipelineMessage :=
  ds.toArray.map (PipelineMessage.fromDiagnostic phase)

end Strata.Pipeline
