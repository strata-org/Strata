/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Laurel.LaurelToCoreTranslator
import Strata.Languages.Laurel.DesugarShortCircuit
import Strata.Languages.Laurel.MergeAndLiftReturns
import Strata.Languages.Laurel.EliminateValueInReturns
import Strata.Languages.Laurel.ModifiesClauses
import Strata.Languages.Laurel.HeapParameterization
import Strata.Languages.Laurel.TypeHierarchy
import Strata.Languages.Laurel.InferHoleTypes
import Strata.Languages.Laurel.EliminateDeterministicHoles
import Strata.Languages.Laurel.CoreDefinitionsForLaurel
import Strata.Languages.Laurel.LiftImperativeExpressions
import Strata.Languages.Laurel.ConstrainedTypeElim
import Strata.Languages.Laurel.TypeAliasElim
public import Strata.Languages.Laurel.LaurelPass
public import Strata.Languages.Core
import Strata.Languages.Core.DDMTransform.ASTtoCST
import Strata.Languages.Core.Verifier
import Strata.Languages.Laurel.Grammar.AbstractToConcreteTreeTranslator
import Strata.Util.Statistics

/-!
## Laurel Compilation Pipeline

Orchestrates the Laurel-to-Laurel lowering passes and the final translation
to Strata Core. The pipeline is:

1. Prepend core definitions for Laurel.
2. Run a sequence of Laurel-to-Laurel lowering passes (resolution, heap
   parameterization, type hierarchy, modifies clauses, hole inference,
   desugaring, lifting, constrained type elimination).
3. Group and order declarations into an `OrderedLaurel`.
4. Translate the `OrderedLaurel` to a `Core.Program`.
-/

open Core (VCResult VCResults VerifyOptions)

namespace Strata.Laurel

/-! ### Pipeline Monad

`PipelineM` wraps `IO` with a `PipelineContext` that carries the step counter
and file-prefix option so that `emit` can be called from any pipeline stage
(Laurel-to-Laurel passes *and* the final translation to Core).
-/

/-- Context threaded through the compilation pipeline via `ReaderT`. -/
private structure PipelineContext where
  /-- When set, intermediate programs are written to `{prefix}.{n}.{name}.{ext}`. -/
  keepAllFilesPrefix : Option String
  /-- Monotonically increasing step counter shared across all pipeline stages. -/
  stepRef : IO.Ref Nat

/-- The pipeline monad: `IO` extended with a shared `PipelineContext`. -/
abbrev PipelineM := ReaderT PipelineContext IO

/-- Write the current program state to disk when `keepAllFilesPrefix` is set.
    Each call increments the shared step counter so files are numbered in order
    across both `runLaurelPasses` and `translateWithLaurel`. -/
def emit {AstType : Type} [Std.ToFormat AstType] (name : String) (ext : String) (p : AstType) : PipelineM Unit := do
  let ctx ← read
  match ctx.keepAllFilesPrefix with
  | some pfx => do
    let n ← ctx.stepRef.modifyGet (fun n => (n, n + 1))
    IO.FS.writeFile s!"{pfx}.{n}.{name}.{ext}"
      ((Std.format p).pretty ++ "\n")
  | none => pure ()

/-- Create a `PipelineContext` and run a `PipelineM` action.
    Ensures the parent directory for emitted files exists. -/
def runPipelineM (keepAllFilesPrefix : Option String) (m : PipelineM α) : IO α := do
  if let some pfx := keepAllFilesPrefix then
    if let some parent := (System.FilePath.mk pfx).parent then
      IO.FS.createDirAll parent
  let stepRef ← IO.mkRef (0 : Nat)
  m { keepAllFilesPrefix, stepRef }

public section

/-- Like `translate` but also returns the lowered Laurel program (after all
    Laurel-to-Laurel passes, before the final translation to Core). -/
abbrev TranslateResultWithLaurel := (Option Core.Program) × (List DiagnosticModel) × Program × Statistics

/-- The ordered sequence of Laurel-to-Laurel lowering passes. -/
def laurelPipeline : Array LaurelPass := #[
  typeAliasElimPass,
  filterNonCompositeModifiesPass,
  eliminateValueInReturnsPass,
  heapParameterizationPass,
  typeHierarchyTransformPass,
  modifiesClausesTransformPass,
  inferHoleTypesPass,
  eliminateDeterministicHolesPass,
  desugarShortCircuitPass,
  liftExpressionAssignmentsPass,
  mergeAndLiftReturnsPass,
  constrainedTypeElimPass
]

/--
Run all Laurel-to-Laurel lowering passes on a program, returning the lowered
program, the semantic model, accumulated diagnostics, and merged statistics.

When `keepAllFilesPrefix` is provided (via the `PipelineM` context), the
program state after each named Laurel pass is written to
`{prefix}.{n}.{passName}.laurel.st`.
-/
private def runLaurelPasses (options : LaurelTranslateOptions)
    (pctx : Strata.Pipeline.PipelineContext) (program : Program)
    : PipelineM (Program × SemanticModel × List DiagnosticModel × Statistics) := do
  let program := { program with
    staticProcedures := coreDefinitionsForLaurel.staticProcedures ++ program.staticProcedures,
    types := coreDefinitionsForLaurel.types ++ program.types
  }

  -- Step 0: the input program before any passes
  emit "Initial" "laurel.st" program

  -- Initial resolution
  let result := resolve program
  let resolutionErrors : List DiagnosticModel := result.errors.toList
  let (program, model) := (result.program, result.model)

  let mut program := program
  let mut model := model
  let mut allDiags : List DiagnosticModel := resolutionErrors
  let mut allStats : Statistics := {}

  for pass in laurelPipeline do
    let (program', diags, stats) ← pctx.withPhase pass.name do pure (pass.run program model)
    program := program'
    allDiags := allDiags ++ diags
    allStats := allStats.merge stats
    -- Run resolve after the pass if needed
    if pass.needsResolves then
      let result := resolve program (some model)
      let newErrors := result.errors.filter fun e => !resolutionErrors.contains e
      if !newErrors.isEmpty then
        emit pass.name "laurel.st" program
      program := result.program
      model := result.model
    emit pass.name "laurel.st" program

  return (program, model, allDiags, allStats)

/--
Translate Laurel Program to Core Program, also returning the lowered Laurel program.

When `keepAllFilesPrefix` is provided, the program state after each named
Laurel-to-Laurel pass is written to `{prefix}.{n}.{passName}.laurel.st`.
-/
def translateWithLaurel (options : LaurelTranslateOptions) (program : Program)
    (pipelineCtx : Option Strata.Pipeline.PipelineContext := none)
    : IO TranslateResultWithLaurel := do
  let pctx ← match pipelineCtx with
    | some ctx => pure ctx
    | none => Strata.Pipeline.PipelineContext.create (outputMode := .quiet)
  runPipelineM options.keepAllFilesPrefix do
    let (program, model, passDiags, stats) ← runLaurelPasses options pctx program
    let ordered := orderProgram program

    -- This early return is a simple way to protect against duplicative errors. Without this return,
    -- resolution errors reported by Laurel would also be reported by Core.
    -- There might be better solution that allows getting some resolution errors from Laurel and some verification errors from Core,
    -- but that would need more consideration.
    if passDiags.any (·.type != .Warning) then
      return (none, passDiags, program, stats)

    let initState : TranslateState := { model := model, overflowChecks := options.overflowChecks }
    let (coreProgramOption, translateState) :=
      runTranslateM initState (translateLaurelToCore options program ordered)
    if let some coreProgram := coreProgramOption then
      emit "CoreProgram" "core.st" coreProgram
    let mut allDiagnostics := passDiags ++ translateState.diagnostics

    if translateState.coreDiagnostics.length > 0 && allDiagnostics.isEmpty then
      allDiagnostics := allDiagnostics ++ translateState.coreDiagnostics

    let coreProgramOption :=
      if !translateState.coreDiagnostics.isEmpty then none else coreProgramOption
    return (coreProgramOption, allDiagnostics, program, stats)

/--
Translate Laurel Program to Core Program.
-/
def translate (options : LaurelTranslateOptions) (program : Program) : IO TranslateResult := do
  let (core, diags, _, _) ← translateWithLaurel options program
  return (core, diags)

/--
Verify a Laurel program using an SMT solver.
-/
def verifyToVcResults (program : Program)
    (options : LaurelVerifyOptions := default)
    : IO (Option VCResults × List DiagnosticModel) := do
  let (coreProgramOption, translateDiags) ← translate options.translateOptions program

  match coreProgramOption with
  | some coreProgram =>
    let options := { options.verifyOptions with removeIrrelevantAxioms := .Precise }
    let runner tempDir :=
      EIO.toIO (fun f => IO.Error.userError (toString f))
          (_root_.Core.verify coreProgram tempDir .none options)
    let ioResult ← match options.vcDirectory with
      | .none => IO.FS.withTempDir runner
      | .some p => IO.FS.createDirAll ⟨p.toString⟩; runner ⟨p.toString⟩
    return (some ioResult, translateDiags)
  | none => return (none, translateDiags)

/--
Verify a Laurel program using an SMT solver, returning results with
duplicated assertions merged at the VCOutcome level.
-/
def verifyToMergedResults (program : Program)
    (options : LaurelVerifyOptions := default)
    : IO (Option VCResults × List DiagnosticModel) := do
  let (vcOpt, diags) ← verifyToVcResults program options
  return (vcOpt.map (·.mergeByAssertion), diags)

def verifyToDiagnostics (files : Map Strata.Uri Lean.FileMap) (program : Program)
    (options : LaurelVerifyOptions := default) : IO (Array Diagnostic) := do
  let results ← verifyToMergedResults program options
  let phases := Core.coreAbstractedPhases
  let translationDiags := results.snd.map (fun dm => dm.toDiagnostic files)
  let vcDiags := match results.fst with
  | some vcResults => vcResults.toList.filterMap (fun (vcr : VCResult) => Core.VCResult.toDiagnostic files vcr phases)
  | none => []
  return (translationDiags ++ vcDiags).toArray

def verifyToDiagnosticModels (program : Program) (options : LaurelVerifyOptions := default)
    : IO (Array DiagnosticModel) := do
  let results ← verifyToMergedResults program options
  let phases := Core.coreAbstractedPhases
  let vcDiags := match results.fst with
  | none => []
  | some vcResults => vcResults.toList.filterMap (fun (vcr : VCResult) => toDiagnosticModel vcr phases)
  return (results.snd ++ vcDiags).toArray

end -- public section
end Laurel
