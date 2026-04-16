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
  /-- How many times `resolve` should be run after the pass. -/
  resolvesAfter : Nat := 0
  /-- The pass action. -/
  run : Program → SemanticModel → Program × List DiagnosticModel × Statistics

/-- The ordered sequence of Laurel-to-Laurel lowering passes. -/
private def laurelPipeline : Array LaurelPass := #[
  { name := "EliminateValueReturns"
    run := fun p _m =>
      let (p', diags) := eliminateValueReturnsTransform p
      (p', diags.toList, {}) },
  { name := "FilterNonCompositeModifies"
    run := fun p m =>
      let (p', diags, stats) := filterNonCompositeModifies m p
      (p', diags, stats) },
  { name := "HeapParameterization"
    resolvesAfter := 1
    run := fun p m =>
      let (p', stats) := heapParameterization m p
      (p', [], stats) },
  { name := "TypeHierarchyTransform"
    resolvesAfter := 1
    run := fun p m =>
      let (p', stats) := typeHierarchyTransform m p
      (p', [], stats) },
  { name := "ModifiesClausesTransform"
    resolvesAfter := 2
    run := fun p m =>
      let (p', diags, stats) := modifiesClausesTransform m p
      (p', diags, stats) },
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
      let (p', stats) := desugarShortCircuit m p
      (p', [], stats) },
  { name := "LiftExpressionAssignments"
    run := fun p m =>
      let (p', stats) := liftExpressionAssignments m p
      (p', [], stats) },
  { name := "EliminateReturns"
    resolvesAfter := 1
    run := fun p _m =>
      let (p', stats) := eliminateReturnsInExpressionTransform p
      (p', [], stats) },
  { name := "ConstrainedTypeElim"
    resolvesAfter := 1
    run := fun p m =>
      let (p', diags, stats) := constrainedTypeElim m p
      (p', diags, stats) }
]

/--
Run all Laurel-to-Laurel lowering passes on a program, returning the lowered
program, the semantic model, accumulated diagnostics, and merged statistics.

When `keepAllFilesPrefix` is provided, the program state after each named
Laurel pass is written to `{prefix}.{n}.{passName}.laurel.st`.
-/
private def runLaurelPasses (options : LaurelTranslateOptions) (program : Program)
    (keepAllFilesPrefix : Option String := none)
    : IO (Program × SemanticModel × List DiagnosticModel × Statistics) := do
  let program := { program with
    staticProcedures := coreDefinitionsForLaurel.staticProcedures ++ program.staticProcedures
  }

  if let some pfx := keepAllFilesPrefix then
    if let some parent := (System.FilePath.mk pfx).parent then
      IO.FS.createDirAll parent
  let stepRef ← IO.mkRef (0 : Nat)
  let emit (name : String) (p : Program) : IO Unit :=
    match keepAllFilesPrefix with
    | some pfx => do
      let n ← stepRef.modifyGet (fun n => (n, n + 1))
      IO.FS.writeFile s!"{pfx}.{n}.{name}.laurel.st"
        ((formatProgram p).pretty ++ "\n")
    | none => pure ()

  -- Step 0: the input program before any passes
  emit "Initial" program

  -- Initial resolution
  let result := resolve program
  let resolutionErrors : List DiagnosticModel :=
    if options.emitResolutionErrors then result.errors.toList else []
  let (program, model) := (result.program, result.model)
  emit "Resolve" program
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
    -- Run resolve the requested number of times after the pass
    for _ in List.range pass.resolvesAfter do
      let result := resolve program (some model)
      program := result.program
      model := result.model
    emit pass.name program

  return (program, model, allDiags, allStats)

/--
Translate Laurel Program to Core Program, also returning the lowered Laurel program.

When `keepAllFilesPrefix` is provided, the program state after each named
Laurel-to-Laurel pass is written to `{prefix}.{n}.{passName}.laurel.st`.
-/
def translateWithLaurel (options : LaurelTranslateOptions) (program : Program)
    (keepAllFilesPrefix : Option String := none)
    : IO TranslateResultWithLaurel := do
  let (program, model, passDiags, stats) ← runLaurelPasses options program keepAllFilesPrefix
  let ordered := orderProgram program
  let initState : TranslateState := { model := model, overflowChecks := options.overflowChecks }
  let (coreProgramOption, translateState) :=
    runTranslateM initState (translateLaurelToCore options program ordered)
  let allDiagnostics := passDiags ++ translateState.diagnostics
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
    (options : VerifyOptions := .default)
    : IO (Option VCResults × List DiagnosticModel) := do
  let (coreProgramOption, translateDiags) ← translate {} program

  match coreProgramOption with
  | some coreProgram =>
    let options := { options with removeIrrelevantAxioms := .Precise }
    let runner tempDir :=
      EIO.toIO (fun f => IO.Error.userError (toString f))
          (Core.verify coreProgram tempDir .none options)
    let ioResult ← match options.vcDirectory with
      | .none => IO.FS.withTempDir runner
      | .some p => IO.FS.createDirAll ⟨p.toString⟩; runner ⟨p.toString⟩
    return (some ioResult, translateDiags)
  | none => return (none, translateDiags)

def verifyToDiagnostics (files : Map Strata.Uri Lean.FileMap) (program : Program)
    (options : VerifyOptions := .default) : IO (Array Diagnostic) := do
  let results ← verifyToVcResults program options
  let phases := Core.coreAbstractedPhases
  let translationDiags := results.snd.map (fun dm => dm.toDiagnostic files)
  let vcDiags := match results.fst with
  | some vcResults => vcResults.toList.filterMap (fun (vcr : VCResult) => Core.VCResult.toDiagnostic files vcr phases)
  | none => []
  return (translationDiags ++ vcDiags).toArray

def verifyToDiagnosticModels (program : Program) (options : VerifyOptions := .default)
    : IO (Array DiagnosticModel) := do
  let results ← verifyToVcResults program options
  let phases := Core.coreAbstractedPhases
  let vcDiags := match results.fst with
  | none => []
  | some vcResults => vcResults.toList.filterMap (fun (vcr : VCResult) => toDiagnosticModel vcr phases)
  return (results.snd ++ vcDiags).toArray

end -- public section
end Laurel
