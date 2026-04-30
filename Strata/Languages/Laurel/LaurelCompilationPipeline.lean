/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Laurel.LaurelToCoreTranslator
import Strata.Languages.Laurel.DesugarShortCircuit
import Strata.Languages.Laurel.EliminateReturnsInExpression
import Strata.Languages.Laurel.EliminateValueReturns
import Strata.Languages.Laurel.ConstrainedTypeElim
import Strata.Languages.Laurel.TypeAliasElim
import Strata.Languages.Core.Verifier
import Strata.Util.Profile
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

/-- A single Laurel-to-Laurel pass. Each pass receives the current program and
    semantic model and returns the (possibly modified) program, accumulated
    diagnostics, and statistics. -/
structure LaurelPass where
  /-- Human-readable name, used for profiling and file emission. -/
  name : String
  /-- Whether `resolve` should be run after the pass. -/
  needsResolves : Bool := false
  /-- The pass action. -/
  run : Program → SemanticModel → Program × List DiagnosticModel × Statistics

/-- The ordered sequence of Laurel-to-Laurel lowering passes. -/
private def laurelPipeline : Array LaurelPass := #[
  { name := "FilterNonCompositeModifies"
    run := fun p m =>
      let (p', diags) := filterNonCompositeModifies m p
      (p', diags, {}) },
  { name := "EliminateValueReturns"
    run := fun p _m =>
      let (p', diags) := eliminateValueReturnsTransform p
      (p', diags.toList, {}) },
  { name := "HeapParameterization"
    needsResolves := true
    run := fun p m =>
      (heapParameterization m p, [], {}) },
  { name := "TypeHierarchyTransform"
    needsResolves := true
    run := fun p m =>
      (typeHierarchyTransform m p, [], {}) },
  { name := "ModifiesClausesTransform"
    needsResolves := true
    run := fun p m =>
      let (p', diags) := modifiesClausesTransform m p
      (p', diags, {}) },
  { name := "InferHoleTypes"
    run := fun p m =>
      let (p', stats) := inferHoleTypes m p
      (p', [], stats) },
  { name := "EliminateHoles"
    run := fun p _m =>
      let (p', stats) := eliminateHoles p
      (p', [], stats) },
  { name := "DesugarShortCircuit"
    run := fun p m =>
      (desugarShortCircuit m p, [], {}) },
  { name := "LiftExpressionAssignments"
    run := fun p m =>
      (liftExpressionAssignments m p, [], {}) },
  { name := "EliminateReturns"
    needsResolves := true
    run := fun p _m =>
      (eliminateReturnsInExpressionTransform p, [], {}) },
  { name := "ConstrainedTypeElim"
    needsResolves := true
    run := fun p m =>
      let (p', diags) := constrainedTypeElim m p
      (p', diags, {}) }
]

/--
Run all Laurel-to-Laurel lowering passes on a program, returning the lowered
program, the semantic model, accumulated diagnostics, and merged statistics.

When `keepAllFilesPrefix` is provided (via the `PipelineM` context), the
program state after each named Laurel pass is written to
`{prefix}.{n}.{passName}.laurel.st`.
-/
private def runLaurelPasses (options : LaurelTranslateOptions) (program : Program)
    : PipelineM (Program × SemanticModel × List DiagnosticModel × Statistics) := do
  let program := { program with
    staticProcedures := coreDefinitionsForLaurel.staticProcedures ++ program.staticProcedures,
    types := coreDefinitionsForLaurel.types ++ program.types
  }

  -- Step 0: the input program before any passes
  emit "Initial" "laurel.st" program

  -- Initial resolution
  let result := resolve program
  let resolutionErrors : List DiagnosticModel :=
    if options.emitResolutionErrors then result.errors.toList else []
  let (program, model) := (result.program, result.model)
  emit "Resolve" "laurel.st" program

  let program := typeAliasElim model program
  emit "TypeAliasElim" "laurel.st" program

  let diamondErrors := validateDiamondFieldAccesses model program

  let mut program := program
  let mut model := model
  let mut allDiags : List DiagnosticModel := resolutionErrors ++ diamondErrors
  let mut allStats : Statistics := {}

  for pass in laurelPipeline do
    let (program', diags, stats) ← profileStep options.profile s!"  {pass.name}" do
      pure (pass.run program model)
    program := program'
    allDiags := allDiags ++ diags
    allStats := allStats.merge stats
    -- Run resolve after the pass if needed
    if pass.needsResolves then
      let result := resolve program (some model)
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
    : IO TranslateResultWithLaurel :=
  runPipelineM options.keepAllFilesPrefix do
    let (program, model, passDiags, stats) ← runLaurelPasses options program
    let ordered := orderProgram program

    let initState : TranslateState := { model := model, overflowChecks := options.overflowChecks }
    let (coreProgramOption, translateState) :=
      runTranslateM initState (translateLaurelToCore options program ordered)
    if let some coreProgram := coreProgramOption then
      emit "CoreProgram" "core.st" coreProgram
    let mut allDiagnostics := passDiags ++ translateState.diagnostics
    let coreProgramOption :=
      if translateState.coreProgramHasSuperfluousErrors then none else coreProgramOption
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
          (Core.verify coreProgram tempDir .none options)
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
