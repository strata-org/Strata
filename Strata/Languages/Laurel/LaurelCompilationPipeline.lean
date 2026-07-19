/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Laurel.LaurelToCoreSchemaPass
import Strata.Languages.Laurel.DesugarShortCircuit
import Strata.Languages.Laurel.EliminateReturnStatements
import Strata.Languages.Laurel.EliminateDoWhile
import Strata.Languages.Laurel.EliminateIncrDecr
import Strata.Languages.Laurel.MergeAndLiftReturns
import Strata.Languages.Laurel.EliminateValueInReturns
import Strata.Languages.Laurel.ModifiesClauses
import Strata.Languages.Laurel.HeapParameterization
import Strata.Languages.Laurel.TypeHierarchy
import Strata.Languages.Laurel.InferHoleTypes
import Strata.Languages.Laurel.EliminateDeterministicHoles
import Strata.Languages.Laurel.CoreDefinitionsForLaurel
import Strata.Languages.Laurel.CoreGroupingAndOrdering
import Strata.Languages.Laurel.TransparencyPass
import Strata.Languages.Laurel.LiftImperativeExpressions
import Strata.Languages.Laurel.ConstrainedTypeElim
import Strata.Languages.Laurel.ContractPass
import Strata.Languages.Laurel.PushOldInward
import Strata.Languages.Laurel.LiftInstanceProcedures
import Strata.Languages.Laurel.TypeAliasElim
import Strata.Languages.Laurel.MonomorphizeComposites
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

/-- The ordered sequence of Laurel-to-Laurel lowering passes. -/
def laurelPipeline : Array LoweringPass := #[
  -- Polymorphism: lift instance procedures, then monomorphize, BEFORE everything else
  -- (the lift must precede monomorphization, and both must precede heap parameterization).
  liftInstanceProceduresPass,
  -- TypeAliasElim runs BEFORE monomorphization: an alias of a generic-composite instantiation
  -- (`type BInt = Box<int>`, or a generic `type Foo<T> = Box<T>` used at `Foo<int>`) must unfold
  -- to `Box<int>` so the monomorphizer sees the real `.Applied` and rewrites it to `Box$a1$int`.
  -- Mono is alias-agnostic (no `.Alias` refs); alias-elim only needs the first resolve, which
  -- precedes the whole pipeline. No `comesBefore` pins their relative order.
  typeAliasElimPass,
  { monomorphizeCompositesPass with comesBefore := [⟨heapParameterizationPass.meta, "monomorphization must run before heap parameterization: HeapParam boxes composite fields into the non-parametric Box datatype, so any generic composite still un-monomorphized at that point would be boxed with no concrete instantiation and reach Core un-lowered."⟩] },
  eliminateDoWhilePass,
  eliminateIncrDecrPass,
  constrainedTypeElimPass,
  filterNonCompositeModifiesPass,
  mergeAndLiftReturnsPass,
  -- `liftInstanceProceduresPass` runs at position 0 (it must precede monomorphization);
  -- that also places it before `eliminateValueInReturnsPass`, as value-returning
  -- instance methods require, so no entry is needed here.
  eliminateValueInReturnsPass,
  heapParameterizationPass,
  typeHierarchyTransformPass,
  modifiesClausesTransformPass,
  pushOldInwardPass,
  inferHoleTypesPass,
  eliminateDeterministicHolesPass,
  desugarShortCircuitPass,
  eliminateReturnStatementsPass,
  contractPass
]

/--
Run all Laurel-to-Laurel lowering passes on a program, returning the lowered
program, the semantic model, accumulated diagnostics, and merged statistics.

When `keepAllFilesPrefix` is provided (via the `PipelineM` context), the
program state after each named Laurel pass is written to
`{prefix}.{n}.{passName}.laurel.st`.
-/
private def runLaurelPasses
    (options: LaurelTranslateOptions)
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
  let resolutionErrors : Std.HashSet DiagnosticModel := Std.HashSet.ofArray result.errors
  let (program, model) := (result.program, result.model)

  let mut program := program
  let mut model := model
  let mut allDiags : List DiagnosticModel := result.errors.toList
  let mut allStats : Statistics := {}

  for pass in laurelPipeline do
    let (program', diags, stats) ← pctx.withPhase pass.name do pure (pass.run options program model)
    program := program'
    allDiags := allDiags ++ diags
    allStats := allStats.merge stats
    -- Run resolve after the pass if needed
    if pass.needsResolves then
      let result := resolve program (some model)
      let newErrors := result.errors.filter fun e => !resolutionErrors.contains e
      -- If the program ALREADY has a non-warning error, it is already rejected, so a "new"
      -- re-resolution error is a downstream CASCADE of it (e.g. the same surface error
      -- restated over monomorphized type names, escaping the `resolutionErrors` dedup only
      -- because `Box<bool>` became `Box$a1$bool`). Folding that as an internal `.StrataBug`
      -- would wrongly blame the compiler; suppress it and keep the clean surface diagnostic.
      -- A genuine post-transform failure still fails loud below once the program is otherwise
      -- valid.
      if !newErrors.isEmpty && allDiags.any (·.type != .Warning) then
        return (program, model, allDiags, allStats)
      if !newErrors.isEmpty then
        -- On an otherwise-valid program, a new re-resolution error is a genuine post-transform
        -- COMPILER failure (dangling monomorph ref, unresolved inherited field) — fold it as a
        -- StrataBug so it fails loud (translated=false).
        --
        -- EXCEPTION — a user identifier colliding with a pass-generated name is NOT a compiler
        -- bug: `$`, the `$aN$` tag shape, and the reserved internal type names (`Box`, `Heap`,
        -- `Field`, `TypeTag`, `Composite`) are all legal in source, so a user can declare one.
        -- Such a collision surfaces as a NEW `Duplicate definition` — and a duplicate can ONLY be
        -- a user/generated clash (two user names would have clashed in the first resolve; two
        -- generated names are worklist-deduped), so a genuine internal failure is always a "not
        -- defined" dangling ref, never a duplicate. Report the duplicate as a plain `UserError`
        -- with a rename hint. Location is usually good but incidental: the generated type is
        -- prepended to `program.types`, so the user declaration is the second registrant that
        -- `defineNameCheckDup` blames, carrying its real `FileRange`; a purely-synthetic colliding
        -- name (`$heap`/`$impl`, `source := none`) can still lose location.
        let isUserCollision (d : DiagnosticModel) : Bool :=
          (d.message.splitOn "Duplicate definition").length > 1
        let asStrataBug (d : DiagnosticModel) : DiagnosticModel :=
          { d with
              message :=
                s!"Internal error: resolution after '{pass.name}' introduced this diagnostic: {d.message}"
              type := .StrataBug }
        let collisions := newErrors.toList.filter isUserCollision
        if collisions.isEmpty then
          -- No collision ⇒ every new error is a genuine post-transform compiler failure.
          let newDiags := newErrors.toList.map asStrataBug
          emit pass.name "laurel.st" program
          return (program, model, allDiags ++ newDiags, allStats)
        else
          -- A `Duplicate definition` collision is present. Its own downstream CASCADE — type
          -- mismatches restated over the doubly-defined name (a composite named `Box`/`Field`/
          -- `TypeTag` clashing with a lowering-generated datatype yields `expected 'Composite',
          -- got 'Field'` follow-ons) — is not an independent compiler bug and must not be blamed
          -- on the compiler. Report each collision as a clean `.UserError` with a rename hint.
          -- The doubly-defined name is quoted in the collision message (`Duplicate definition
          -- 'X'`); a cascade follow-on always MENTIONS that name, so we drop only the new errors
          -- that reference a colliding name and still fail loud (`.StrataBug`) on any OTHER new
          -- error — a genuinely independent post-transform failure that merely co-occurred is
          -- NOT masked. (Renaming the identifier removes the collision and routes every new error
          -- through the fail-loud branch above, so nothing is ever permanently hidden.)
          let collidingNames : List String :=
            collisions.filterMap (fun d => (d.message.splitOn "'")[1]?)
          let mentionsColliding (d : DiagnosticModel) : Bool :=
            collidingNames.any (fun n => (d.message.splitOn n).length > 1)
          let hinted := collisions.map fun d =>
            { d with
                message :=
                  s!"{d.message} (this name collides with one introduced by an internal lowering \
                     pass; rename the identifier — a reserved internal type name (e.g. `Box`, \
                     `Heap`, `Field`, `TypeTag`, `Composite`) or a name containing `$` / the \
                     `$aN$` instantiation-tag shape can clash with a synthetic name)"
                type := .UserError }
          let independent := newErrors.toList.filter fun d =>
            !isUserCollision d && !mentionsColliding d
          let newDiags := hinted ++ independent.map asStrataBug
          emit pass.name "laurel.st" program
          return (program, model, allDiags ++ newDiags, allStats)
      program := result.program
      model := result.model
    emit pass.name "laurel.st" program

  return (program, model, allDiags, allStats)

/-- The ordered sequence of passes on the unordered Core representation. -/
private def unorderedCorePipeline : Array (LaurelPass UnorderedCoreWithLaurelTypes UnorderedCoreWithLaurelTypes) := #[
  liftImperativeExpressionsPass
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

  -- Sanity check: `LiftInstanceProcedures` should have cleared every
  -- composite's `instanceProcedures` list.
  let mut passDiags := passDiags
  for td in program.types do
    if let .Composite ct := td then
      for proc in ct.instanceProcedures do
        passDiags := passDiags ++ [diagnosticFromSource proc.name.source
          s!"Instance procedure '{proc.name.text}' on composite type '{ct.name.text}' was not lifted before Core translation (pipeline-ordering bug)"
          DiagnosticType.StrataBug]

  -- This early return is a simple way to protect against duplicative errors. Without this return,
  -- resolution errors reported by Laurel would also be reported by Core.
  -- There might be better solution that allows getting some resolution errors from Laurel and some verification errors from Core,
  -- but that would need more consideration.
  if passDiags.any (·.type != .Warning) then
    return (none, passDiags, program, stats)

  let unorderedCore := (transparencyPass.run options program model).1
  emit "transparencyPass" "core.st" unorderedCore
  let mut unorderedCore := unorderedCore
  let mut fnModel := model

  for pass in unorderedCorePipeline do
    unorderedCore := (pass.run options unorderedCore fnModel).1
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

  let coreWithLaurelTypes := (orderingPass.run options unorderedCore model).1

  emit "CoreWithLaurelTypes" "core.st" coreWithLaurelTypes
  let (coreProgram, coreDiagnostics, _) := laurelToCoreSchemaPass.run options coreWithLaurelTypes fnModel
  let mut allDiagnostics: List DiagnosticModel := passDiags ++ coreDiagnostics;

  emit "Core" "core.st" coreProgram
  let coreProgramOption :=
    if coreDiagnostics.isEmpty then some coreProgram else none
  return (coreProgramOption, allDiagnostics, program, stats)

/--
Translate Laurel Program to Core Program.
-/
def translate (options : LaurelTranslateOptions) (program : Program) : IO TranslateResult := do
  let (core, diags, _, _) ← translateWithLaurel options program
  return (core, diags)

/-- The canonical Core `VerifyOptions` used by *every* Laurel verify path.
    Single source of truth so the diagnostics paths (`verifyToDiagnostics`) and
    the production path (`verifyToVcResults`) cannot silently diverge — they must
    measure the same verification. -/
def coreVerifyOptions (options : LaurelVerifyOptions) : Core.VerifyOptions :=
  { options.verifyOptions with removeIrrelevantAxioms := .Precise }

/-- Run `act` with the VC directory dictated by `verifyOpts`: a fresh temp dir
    (auto-cleaned) when none is configured, else the caller's directory. Shared
    by all verify entry points. -/
def withVcDir {α} (verifyOpts : Core.VerifyOptions) (act : System.FilePath → IO α) : IO α :=
  match verifyOpts.vcDirectory with
  | .none => IO.FS.withTempDir act
  | .some p => do IO.FS.createDirAll ⟨p.toString⟩; act ⟨p.toString⟩

/-- Run `Core.verify` on a translated Core program, returning the verify-phase
    failure as a **structured** `DiagnosticModel` value (via `.toBaseIO`) rather
    than throwing it (file-relative reporting, #1367).

    `Core.verify : EIO DiagnosticModel VCResults` carries its error as a
    `DiagnosticModel` (with byte-offset `fileRange`). Capturing it as an
    `Except` here is the single point where that structure is preserved, so the
    throwing (`verifyToVcResults`) and capturing
    (`verifyToDiagnosticModelsCapturing`) entry points can't drift apart: both
    share this verify setup (`coreVerifyOptions` + `withVcDir`) and only differ in
    how they treat the `.error` case. -/
private def runVerify (coreProgram : Core.Program) (options : LaurelVerifyOptions)
    : IO (Except DiagnosticModel VCResults) := do
  let verifyOptions := coreVerifyOptions options
  withVcDir verifyOptions fun tempDir =>
    (_root_.Core.verify coreProgram tempDir (proceduresToVerify := none) verifyOptions).toBaseIO

/--
Verify a Laurel program using an SMT solver.

A verify-phase failure (a type-checking / symbolic-evaluation error) is
**thrown** as an `IO` exception, exactly as before file-relative reporting was
introduced: the structured error is intercepted at the `runVerify` boundary and
re-thrown via `toString`, so the CLI's control flow and exit codes are
unchanged. Tests that need the structured error as a value (to render it to
`line:col`) call `verifyToDiagnosticModelsCapturing` instead.
-/
def verifyToVcResults (program : Program)
    (options : LaurelVerifyOptions := default)
    : IO (Option VCResults × List DiagnosticModel) := do
  let (coreProgramOption, translateDiags) ← translate options.translateOptions program

  match coreProgramOption with
  | some coreProgram =>
    match ← runVerify coreProgram options with
    | .ok ioResult => return (some ioResult, translateDiags)
    -- Throwing path: stringify the structured error (as #1367 did). A poly fn whose
    -- body mismatches its signature must surface as a Core error FOLDED into the
    -- result (`translated=false`), not a Lean exception — that fold lives in the
    -- CAPTURING entry point consumers use, `verifyToDiagnosticModelsCapturing`, which
    -- routes through this same `runVerify` boundary and returns `.error` as a value.
    -- `verifyToVcResults` keeps #1367's throwing behavior for the production CLI path
    -- (its only external caller, `Languages/Laurel.lean`).
    | .error dm => throw (IO.userError (toString dm))
  | none => return (none, translateDiags)

/--
Verify a Laurel program using an SMT solver, returning results with
duplicated assertions merged at the VCOutcome level.

Unlike `verifyToVcResults` (which THROWS a verify-phase error to preserve the
CLI's exit-code behavior, #1367), this CAPTURES a Core-side `DiagnosticModel`
failure and folds it into the returned diagnostics: a polymorphic
function whose body is incompatible with its signature is a Core type error that
must surface as a diagnostic (`translated=false`), not a thrown exception. This
is the path the non-throwing consumers (`verifyToDiagnostics`,
`verifyToDiagnosticModels`) build on. Both
fold-capturing paths share the `runVerify` boundary, so they can't drift from the
throwing path on verify options or temp-dir handling.
-/
def verifyToMergedResults (program : Program)
    (options : LaurelVerifyOptions := default)
    : IO (Option VCResults × List DiagnosticModel) := do
  let (coreProgramOption, translateDiags) ← translate options.translateOptions program
  match coreProgramOption with
  | none => return (none, translateDiags)
  | some coreProgram =>
    match ← runVerify coreProgram options with
    | .ok results => return (some results.mergeByAssertion, translateDiags)
    | .error coreDiag => return (none, translateDiags ++ [coreDiag])

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

/-- Like `verifyToDiagnosticModels`, but a verify-phase failure is **captured**
    as a structured `DiagnosticModel` (the same value `verifyToVcResults` would
    have thrown via `toString`) and returned in the list, rather than thrown.

    This is the test-framework entry point: the structured error still carries
    its byte-offset `fileRange`, so the caller can render it to snippet-local /
    file-relative `line:col` like every other diagnostic — instead of the raw
    byte offset that a stringified exception would leave in its message text.
    Production code keeps using the throwing `verifyTo*` functions above.

    Shares the `runVerify` boundary with `verifyToVcResults`, differing only in
    that it returns the captured `.error` as a value instead of re-throwing it —
    so the two can't drift apart on verify options or temp-dir handling. -/
def verifyToDiagnosticModelsCapturing (program : Program)
    (options : LaurelVerifyOptions := default) : IO (Array DiagnosticModel) := do
  let (coreProgramOption, translateDiags) ← translate options.translateOptions program
  match coreProgramOption with
  | none => return translateDiags.toArray
  | some coreProgram =>
    match ← runVerify coreProgram options with
    | .error dm => return (translateDiags ++ [dm]).toArray
    | .ok results =>
      let phases := Core.coreAbstractedPhases
      let vcDiags := results.mergeByAssertion.toList.filterMap (toDiagnosticModel · phases)
      return (translateDiags ++ vcDiags).toArray

end -- public section

public def allPasses: Array PassMeta := laurelPipeline.map (fun p => p.meta) ++
  [transparencyPass.meta] ++
  unorderedCorePipeline.map (fun p => p.meta) ++
  [orderingPass.meta, laurelToCoreSchemaPass.meta]

/-- Every `comesBefore` and `comesAfter` constraint is respected by the
    pipeline order. A `comesBefore` dependency requires this pass to appear
    earlier than its target; a `comesAfter` dependency requires it to appear
    later. -/
def orderingRespected : Bool :=
  let names := allPasses.map (·.name)
  (List.range allPasses.size).zip allPasses.toList |>.all fun (i, p) =>
    (p.comesBefore.all fun cb =>
      match names.findIdx? (· == cb.pass.name) with
      | some j => i < j
      | none   => false)  -- target not in allPasses
    &&
    (p.comesAfter.all fun ca =>
      match names.findIdx? (· == ca.pass.name) with
      | some j => j < i
      | none   => false)  -- target not in allPasses

-- Use `initialize` to check at load time instead of `#guard` which requires
-- interpreter IR that is not available for passes defined in `module` files.
initialize do
  unless orderingRespected do
    throw <| .userError "laurelPipeline: comesBefore/comesAfter ordering constraints violated"

end Laurel
