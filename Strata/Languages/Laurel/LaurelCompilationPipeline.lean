/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Laurel.LaurelToCoreTranslator
import Strata.Languages.Laurel.DesugarShortCircuit
import Strata.Languages.Laurel.EliminateReturnsInExpression
import Strata.Languages.Laurel.EliminateReturnStatements
import Strata.Languages.Laurel.ConstrainedTypeElim
import Strata.Languages.Laurel.ContractPass
import Strata.Languages.Laurel.EliminateMultipleOutputs
import Strata.Languages.Core.Verifier

/-!
## Laurel Compilation Pipeline

Orchestrates the Laurel-to-Laurel lowering passes and the final translation
to Strata Core. The pipeline is:

1. Prepend core definitions for Laurel.
2. Run a sequence of Laurel-to-Laurel lowering passes (resolution, heap
   parameterization, type hierarchy, modifies clauses, hole inference,
   desugaring, lifting, constrained type elimination, contract pass).
3. Run the proof pass to produce a `FunctionsAndProofsProgram`.
4. Group and order declarations into a `CoreWithLaurelTypes`.
5. Translate the `CoreWithLaurelTypes` to a `Core.Program`.
-/

open Core (VCResult VCResults VerifyOptions)

namespace Strata.Laurel

public section

/-- Like `translate` but also returns the lowered Laurel program (after all
    Laurel-to-Laurel passes, before the final translation to Core). -/
abbrev TranslateResultWithLaurel := (Option Core.Program) × (List DiagnosticModel) × Program

/--
Run all Laurel-to-Laurel lowering passes on a program, returning the lowered
program, the semantic model, and accumulated diagnostics.

When `keepAllFilesPrefix` is provided, the program state after each named
Laurel pass is written to `{prefix}.{n}.{passName}.laurel.st`.
-/
private def runLaurelPasses (options : LaurelTranslateOptions) (program : Program)
    (keepAllFilesPrefix : Option String := none)
    : IO (Program × SemanticModel × List DiagnosticModel) := do
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

  let result := resolve program
  let resolutionErrors : List DiagnosticModel :=
    if options.emitResolutionErrors then result.errors.toList else []
  let (program, model) := (result.program, result.model)
  emit "Resolve" program
  let diamondErrors := validateDiamondFieldAccesses model program

  let (program, nonCompositeDiags) := filterNonCompositeModifies model program
  emit "FilterNonCompositeModifies" program

  let program := heapParameterization model program
  let result := resolve program (some model)
  let (program, model) := (result.program, result.model)
  emit "HeapParameterization" program

  let program := typeHierarchyTransform model program
  let result := resolve program (some model)
  let (program, model) := (result.program, result.model)
  emit "TypeHierarchyTransform" program
  let (program, modifiesDiags) := modifiesClausesTransform model program
  let result := resolve program (some model)
  let (program, model) := (result.program, result.model)
  let result := resolve program (some model)
  let (program, model) := (result.program, result.model)
  emit "ModifiesClausesTransform" program
  let program := inferHoleTypes model program
  emit "InferHoleTypes" program
  let program := eliminateHoles program
  emit "EliminateHoles" program
  let program := desugarShortCircuit model program
  emit "DesugarShortCircuit" program
  let program := liftExpressionAssignments model program
  emit "LiftExpressionAssignments" program
  let program := eliminateReturnsInExpressionTransform program
  let result := resolve program (some model)
  let (program, model) := (result.program, result.model)
  emit "EliminateReturns" program

  let program := eliminateReturnStatements program
  emit "EliminateReturnStatements" program

  let (program, constrainedTypeDiags) := constrainedTypeElim model program
  let result := resolve program (some model)
  let (program, model) := (result.program, result.model)
  emit "ConstrainedTypeElim" program

  let program := contractPass program

  -- Check if the pipeline introduced new resolution errors that weren't present initially.
  -- This catches bugs where a pass produces unresolvable names, which would silently
  -- cause coreProgramHasSuperfluousErrors to be set with no user-visible diagnostic.
  let finalResolutionErrors := (resolve program (some model)).errors
  let newResolutionErrors : List DiagnosticModel :=
    if finalResolutionErrors.size > resolutionErrors.length then
      let newCount := finalResolutionErrors.size - resolutionErrors.length
      let firstNew := finalResolutionErrors.toList.drop resolutionErrors.length
        |>.head?.map (·.message) |>.getD "unknown"
      [DiagnosticModel.fromMessage
        s!"Strata bug: {newCount} new resolution error(s) introduced by pipeline passes. First new error: {firstNew}"
        DiagnosticType.StrataBug]
    else []

  let allDiags := resolutionErrors ++ diamondErrors ++ nonCompositeDiags ++
    modifiesDiags ++ constrainedTypeDiags ++ newResolutionErrors
  return (program, model, allDiags)

/--
Translate Laurel Program to Core Program, also returning the lowered Laurel program.

When `keepAllFilesPrefix` is provided, the program state after each named
Laurel-to-Laurel pass is written to `{prefix}.{n}.{passName}.laurel.st`.
-/
def translateWithLaurel (options : LaurelTranslateOptions) (program : Program)
    (keepAllFilesPrefix : Option String := none)
    : IO TranslateResultWithLaurel := do
  let (program, model, passDiags) ← runLaurelPasses options program keepAllFilesPrefix
  let functionsAndProofs := laurelToFunctionsAndProofs program
  let functionsAndProofs := eliminateMultipleOutputs functionsAndProofs

  let fnProgram : Program := {
    staticProcedures := functionsAndProofs.functions ++ functionsAndProofs.proofs,
    staticFields := [],
    types := functionsAndProofs.datatypes.map TypeDefinition.Datatype ++
    -- Hack to compensate for references to composite types not having been updated yet.
      program.types.filter (fun t => match t with | .Composite _ => true | _ => false),
    constants := program.constants
  }
  let fnResolveResult := resolve fnProgram (some model)
  let fnResolutionErrors : List DiagnosticModel :=
    if fnResolveResult.errors.size > 0 then
      let firstErr := fnResolveResult.errors.toList.head?.map (·.message) |>.getD "unknown"
      [DiagnosticModel.fromMessage
        s!"Strata bug: {fnResolveResult.errors.size} resolution error(s) in fnProgram re-resolve. First error: {firstErr}"
        DiagnosticType.StrataBug]
    else []
  let fnModel := fnResolveResult.model

  let ordered := orderFunctionsAndProofs functionsAndProofs
  let initState : TranslateState := { model := fnModel }
  let (coreProgramOption, translateState) :=
    runTranslateM initState (translateLaurelToCore options program ordered)
  let allDiagnostics := passDiags ++ fnResolutionErrors ++ translateState.diagnostics
  let allDiagnostics :=
    if translateState.coreProgramHasSuperfluousErrors && allDiagnostics.isEmpty then
      -- The program was suppressed but no diagnostics explain why — that's a bug.
      allDiagnostics ++ [DiagnosticModel.fromMessage
        "Core program was suppressed due to superfluous errors, but no diagnostics were emitted. This is a bug."
        DiagnosticType.StrataBug]
    else allDiagnostics
  let coreProgramOption :=
    if translateState.coreProgramHasSuperfluousErrors then none else coreProgramOption
  return (coreProgramOption, allDiagnostics, program)

/--
Translate Laurel Program to Core Program.
-/
def translate (options : LaurelTranslateOptions) (program : Program) : IO TranslateResult := do
  let (core, diags, _) ← translateWithLaurel options program
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
