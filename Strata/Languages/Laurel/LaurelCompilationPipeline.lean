/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Laurel.LaurelToCoreTranslator
import Strata.Languages.Laurel.DatatypeTesters
import Strata.Languages.Laurel.DesugarShortCircuit
import Strata.Languages.Laurel.EliminateReturnsInExpression
import Strata.Languages.Laurel.EliminateReturnStatements
import Strata.Languages.Laurel.EliminateValuesInReturns
import Strata.Languages.Laurel.InlineLocalVariablesInExpressions
import Strata.Languages.Laurel.ConstrainedTypeElim
import Strata.Languages.Laurel.ContractPass
import Strata.Languages.Laurel.EliminateMultipleOutputs
import Strata.Languages.Laurel.TypeAliasElim
import Strata.Languages.Core.Verifier
import Strata.Util.Statistics

/-!
## Laurel Compilation Pipeline

Orchestrates the Laurel-to-Laurel lowering passes and the final translation
to Strata Core. The pipeline is:

1. Prepend core definitions for Laurel.
2. Run a sequence of Laurel-to-Laurel lowering passes (resolution, heap
   parameterization, type hierarchy, modifies clauses, hole inference,
   desugaring, lifting, constrained type elimination, contract pass).
3. Run the transparency pass to produce an `UnorderedCoreWithLaurelTypes`.
4. Group and order declarations into a `CoreWithLaurelTypes`.
5. Translate the `CoreWithLaurelTypes` to a `Core.Program`.
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
  { name := "EliminateReturnsInExpressions"
    needsResolves := true
    run := fun p _m =>
      let (p', diags) := eliminateReturnsInExpressionTransform p
      (p', diags.toList, {}) },
  { name := "EliminateValuesInReturns"
    run := fun p _m =>
      let (p', diags) := eliminateValuesInReturnsTransform p
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
      let (p', diags, stats) := inferHoleTypes m p
      (p', diags, stats) },
  { name := "EliminateHoles"
    run := fun p _m =>
      let (p', stats) := eliminateHoles p
      (p', [], stats) },
  { name := "DesugarShortCircuit"
    run := fun p _ =>
      (desugarShortCircuit p, [], {}) },
  -- { name := "LiftExpressionAssignments"
  --   run := fun p m =>
  --     (liftExpressionAssignments p m [], [], {}) },
  { name := "ConstrainedTypeElim"
    needsResolves := true
    run := fun p m =>
      let (p', diags) := constrainedTypeElim m p
      (p', diags, {}) },
  { name := "EliminateReturnStatements"
    needsResolves := false
    run := fun p _ =>
      let (p') := eliminateReturnStatements p
      (p', [], {}) },
  { name := "ContractPass"
    needsResolves := true
    run := fun p _ =>
      let (p') := contractPass p
      (p', [], {}) }
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

  -- Generate external tester functions for datatype constructors
  let program := generateDatatypeTesters program

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
    let (program', diags, stats) ← pctx.withPhase pass.name do pure (pass.run program model)
    program := program'
    allDiags := allDiags ++ diags
    allStats := allStats.merge stats
    -- Run resolve after the pass if needed
    if pass.needsResolves then
      let result := resolve program (some model)
      let newErrors := result.errors.filter fun e => !resolutionErrors.contains e
      if !newErrors.isEmpty then
        let newDiags := newErrors.toList.map fun d =>
          { d with
              message :=
                s!"Internal error: resolution after '{pass.name}' introduced this diagnostic: {d.message}"
              type := .StrataBug }
        emit pass.name "laurel.st" program
        return (program, model, allDiags ++ newDiags, allStats)
      program := result.program
      model := result.model
    emit pass.name "laurel.st" program

  return (program, model, allDiags, allStats)

/--
Apply `liftExpressionAssignments` to the core (non-functional) procedures in an
`UnorderedCoreWithLaurelTypes`. Only procedures whose names appear in the core
procedure list are transformed; functions are left unchanged.
-/
def liftImperativeExpressionsInCore (uc : UnorderedCoreWithLaurelTypes)
    (model : SemanticModel) : UnorderedCoreWithLaurelTypes :=
  let imperativeCallees := uc.coreProcedures.map (·.name.text)
  let liftedProgram := liftExpressionAssignments
    { staticProcedures := uc.coreProcedures, staticFields := [], types := [], constants := [] }
    model imperativeCallees
  let liftedProcs := liftedProgram.staticProcedures
  { uc with
    functions := uc.functions
    coreProcedures := liftedProcs
  }

/-- A single pass on the unordered Core representation. Each pass receives the
    current `UnorderedCoreWithLaurelTypes` and the semantic model and returns
    the (possibly modified) program. -/
structure CorePass where
  /-- Human-readable name, used for profiling and file emission. -/
  name : String
  /-- Whether `resolveUnorderedCore` should be run after the pass. -/
  needsResolves : Bool := false
  /-- The pass action. -/
  run : UnorderedCoreWithLaurelTypes → SemanticModel → UnorderedCoreWithLaurelTypes

/-- The ordered sequence of passes on the unordered Core representation. -/
private def corePipeline : Array CorePass := #[
  -- { name := "EliminateMultipleOutputs"
  --   run := fun uc _m => eliminateMultipleOutputs uc },
  -- { name := "InlineLocalVariablesInExpressions"
  --   needsResolves := true
  --   run := fun uc _m => inlineLocalVariablesInExpressions uc },
  { name := "LiftImperativeExpressionsInCore"
    needsResolves := true
    run := fun uc m => liftImperativeExpressionsInCore uc m }
]

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
  if ! passDiags.isEmpty then
    return (none, passDiags, program, stats)

  let unorderedCore := transparencyPass program
  emit "transparencyPass" "core.st" unorderedCore
  let mut unorderedCore := unorderedCore
  let mut fnModel := model

  for pass in corePipeline do
    unorderedCore := pass.run unorderedCore fnModel
    if pass.needsResolves then
      let compositeTypes := program.types.filter (fun t => match t with | .Composite _ => true | _ => false)
      let (uc', m', errors) := resolveUnorderedCore unorderedCore (some fnModel) compositeTypes
      if !errors.isEmpty then
        let newDiags := errors.toList.map fun d =>
          { d with message :=
              s!"Internal error: resolution after '{pass.name}' introduced this diagnostic: {d.message}" }
        emit pass.name "unorderedCoreWithLaurelTypes.st" unorderedCore
        return (none, passDiags ++ newDiags, program, stats)
      unorderedCore := uc'
      fnModel := m'
    emit pass.name "unorderedCoreWithLaurelTypes.st" unorderedCore

  let coreWithLaurelTypes := orderFunctionsAndProcedures unorderedCore
  -- This early return is a simple way to protect against duplicative errors. Without this return,
  -- resolution errors reported by Laurel would also be reported by Core.
  -- There might be better solution that allows getting some resolution errors from Laurel and some verification errors from Core,
  -- but that would need more consideration.
  if ! passDiags.isEmpty then
    return (none, passDiags, program, stats)
  else
      emit "CoreWithLaurelTypes" "core.st" coreWithLaurelTypes
    let initState : TranslateState := { model := fnModel, overflowChecks := options.overflowChecks }
    let (coreProgramOption, translateState) :=
      runTranslateM initState (translateLaurelToCore options program coreWithLaurelTypes)
    -- Because of the duplication between functions and proofs, this translation is liable to create duplicate diagnostics
    -- User errors should be checked in an earlier phase, and all dumb translation errors are Strata bugs
    let mut allDiagnostics := translateState.diagnostics.eraseDups
    if translateState.coreDiagnostics.length > 0 && allDiagnostics.isEmpty then
      -- The program was suppressed but no diagnostics explain why — report the core diagnostics
      -- that have a known source location (those without one are not actionable for the user).
      allDiagnostics := allDiagnostics ++ translateState.coreDiagnostics

    if coreProgramOption.isSome then
      emit "Core" "core.st" coreProgramOption.get!
    let coreProgramOption :=
      if translateState.coreDiagnostics.isEmpty then coreProgramOption else none
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
