/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import StrataLaurel.Implementation.LaurelCompilationPipeline
public import StrataLaurel.Implementation.InferThrows
public import StrataCortex.Implementation.FromLaurel
public import Strata.Languages.Cortex.Pipeline

namespace Cortex

open Strata Strata.Laurel

public section

def resolveLaurel (options : LaurelTranslateOptions) (program : LaurelProgram) :
    Except (List Message) (LaurelProgram × SemanticModel × List Message) :=
  let dollar := validateNoDollarNames program
  if dollar.any (·.kind != .warning) then .error dollar else
  let program := { program with
    staticProcedures := coreDefinitionsForLaurel.staticProcedures ++ program.staticProcedures
    types := coreDefinitionsForLaurel.types ++ program.types }
  let result := resolveWithInferredThrows program (gradualTypes := options.gradualTypes)
    (realizeCoercion := options.realizeCoercion) (toBool := options.toBool)
    (reservedNames := options.reservedNames)
  let errs := result.errors.toList
  if errs.any (·.kind != .warning) then .error errs else .ok (result.program, result.model, errs)

def translate (options : LaurelTranslateOptions) (program : LaurelProgram) :
    Option Core.Program × List Message :=
  if options.passes.isSome then
    (none, [Message.fromString "--phases and --skip-phases select Laurel phases, which the Cortex pipeline does not run"
      MessageKind.userError])
  else
  match resolveLaurel options program with
  | .error ds => (none, ds)
  | .ok (resolved, model, ds) =>
    match FromLaurel.run model resolved options.overflowChecks with
    | (none, d) =>
      let all := ds ++ d
      (none, if all.isEmpty then [Message.fromString "Laurel to Cortex translation failed" MessageKind.strataBug] else all)
    | (some m, d) =>
      match toCoreProgram m with
      | .ok core => (some core, ds ++ d)
      | .error e => (none, ds ++ d ++ [Message.fromString s!"Cortex lowering failed: {e}" MessageKind.strataBug])

def runCoreVerify (core : Core.Program) (options : LaurelVerifyOptions) :
    IO (Except Message Core.VCResults) := do
  let verifyOptions := effectiveCoreVerifyOptions options
  let runner tempDir : IO (Except Message Core.VCResults) :=
    (_root_.Core.verify core tempDir verifyOptions).toBaseIO
  match verifyOptions.vcDirectory with
  | .none => IO.FS.withTempDir runner
  | .some p => IO.FS.createDirAll ⟨p.toString⟩; runner ⟨p.toString⟩

def verifyToVcResults (program : LaurelProgram) (options : LaurelVerifyOptions := default) :
    IO (Option Core.VCResults × List Message) := do
  let (core?, diags) := translate options.translateOptions program
  match core? with
  | none => return (none, diags)
  | some core =>
    match ← runCoreVerify core options with
    | .ok results => return (some results, diags)
    | .error dm => return (none, diags ++ [dm])

def verifyToMessages (program : LaurelProgram) (options : LaurelVerifyOptions := default) :
    IO (Array Message) := do
  let (core?, diags) := translate options.translateOptions program
  match core? with
  | none => return diags.toArray
  | some core =>
    match ← runCoreVerify core options with
    | .error dm => return (diags ++ [dm]).toArray
    | .ok results =>
      let phases := _root_.Core.coreAbstractedPhases (options := effectiveCoreVerifyOptions options)
      return (diags ++ results.mergeByAssertion.toList.filterMap (Strata.toMessage · phases)).toArray

end

end Cortex
