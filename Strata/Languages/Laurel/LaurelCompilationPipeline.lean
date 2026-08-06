/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import Strata.Pipeline.Messages

public import Strata.Languages.Laurel.LaurelToCoreSchemaPass
import Strata.Languages.Laurel.DesugarShortCircuit
import Strata.Languages.Laurel.EliminateReturnStatements
import Strata.Languages.Laurel.EliminateDoWhile
import Strata.Languages.Laurel.EliminateIncrDecrAndCompoundAssign
import Strata.Languages.Laurel.MergeAndLiftReturns
import Strata.Languages.Laurel.EliminateValueInReturns
import Strata.Languages.Laurel.ModifiesClauses
import Strata.Languages.Laurel.HeapParameterization
import Strata.Languages.Laurel.GlobalParameterization
import Strata.Languages.Laurel.TypeHierarchy
import Strata.Languages.Laurel.InferHoleTypes
import Strata.Languages.Laurel.EliminateDeterministicHoles
import Strata.Languages.Laurel.CoreDefinitionsForLaurel
import Strata.Languages.Laurel.CoreGroupingAndOrdering
import Strata.Languages.Laurel.TransparencyPass
import Strata.Languages.Laurel.FilterPrelude
import Strata.Languages.Laurel.LiftImperativeExpressions
import Strata.Languages.Laurel.InlineLocalVariables
import Strata.Languages.Laurel.ConstrainedTypeElim
import Strata.Languages.Laurel.ContractPass
import Strata.Languages.Laurel.LoopInvariantWellFormedness
import Strata.Languages.Laurel.UniqueOverloadNames
import Strata.Languages.Laurel.PushOldInward
import Strata.Languages.Laurel.LiftInstanceProcedures
import Strata.Languages.Laurel.TypeAliasElim
import Strata.Languages.Laurel.EliminateExceptions
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
abbrev TranslateResultWithLaurel := (Option Core.Program) × (List Message) × Program × Statistics

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
  eliminateIncrDecrAndCompoundAssignPass,
  constrainedTypeElimPass,
  mergeAndLiftReturnsPass,
  -- `liftInstanceProceduresPass` runs at position 0 (it must precede monomorphization);
  -- that also places it before `eliminateValueInReturnsPass`, as value-returning
  -- instance methods require, so no entry is needed here.
  -- Note: the exception contract checks (catch-or-declare, plus the
  -- "not yet lowerable" source-shape guards) are *not* a pipeline pass. They are
  -- properties of the authored program, so `resolve` runs them on the initial
  -- resolution only — see `validateExceptionEscapes` /
  -- `validateExceptionLowerability` in `Resolution.lean`.
  eliminateValueInReturnsPass,
  eliminateExceptionsPass,
  -- `globalParameterizationPass` (mainline) threads file-scope globals as hidden proc params.
  -- It runs AFTER monomorphization (which needs the original `staticFields` + un-polluted
  -- `proc.inputs` for per-call-site instantiation inference) and before `heapParameterizationPass`
  -- (globals layered on already-monomorphized concrete procs; heap stays the final hidden input).
  globalParameterizationPass,
  heapParameterizationPass,
  typeHierarchyTransformPass,
  modifiesClausesTransformPass,
  uniqueOverloadNamesPass,
  pushOldInwardPass,
  inferHoleTypesPass,
  eliminateDeterministicHolesPass,
  desugarShortCircuitPass,
  eliminateReturnStatementsPass,
  loopInvariantWellFormednessPass,
  contractPass
]

def newPostPassResolutionErrors (initialDiags : Std.HashSet Message)
    (diagsSoFar : List Message) (postPassDiags : Array Message) : Array Message :=
  if diagsSoFar.any (·.kind != .warning) then #[]
  else postPassDiags.filter fun e => e.kind != .warning && !initialDiags.contains e

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
    : PipelineM (Program × SemanticModel × List Message × Statistics) := do
  -- The always-on prelude: datatypes/functions, "free" for SMT. The generic
  -- `Result` datatype that the exceptional-channel lowering targets is *not*
  -- part of it: `EliminateExceptions` injects `resultDefinitions` itself, and
  -- only when the program actually uses exceptions, so a program that never
  -- throws does not carry it.
  let program := { program with
    staticProcedures := coreDefinitionsForLaurel.staticProcedures ++ program.staticProcedures,
    types := coreDefinitionsForLaurel.types ++ program.types
  }

  -- Step 0: the input program before any passes
  emit "Initial" "laurel.st" program

  -- Initial resolution
  let result := resolve program (gradualTypes := options.gradualTypes)
                  (realizeCoercion := options.realizeCoercion) (toBool := options.toBool)
                  (reservedNames := options.reservedNames)
  let resolutionErrors : Std.HashSet Message := Std.HashSet.ofArray result.errors
  let (program, model) := (result.program, result.model)

  let mut program := program
  let mut model := model
  let mut allDiags : List Message := result.errors.toList
  let mut allStats : Statistics := {}

  if result.errors.any (·.kind != .warning) then
    return (program, model, allDiags, allStats)

  for pass in laurelPipeline do
    let (program', diags, stats) ← pctx.withPhase pass.name do pure (pass.run options program model)
    program := program'
    allDiags := allDiags ++ diags
    allStats := allStats.merge stats
    -- A pass that reported a real (non-warning) error has REJECTED the program; no later pass
    -- should transform an already-invalid program. Each subsequent pass is an independent chance
    -- to cascade a confusing internal error on top of the clean surface diagnostic — e.g. the
    -- depth-cap `notYetImplemented` on a divergent generic (`Box<Box<T>>`) leaves the deep
    -- instantiation un-monomorphized, and HeapParameterization (which does not re-resolve) would
    -- then emit its own `.strataBug` on the leftover. Stop here with the clean diagnostics so the
    -- rejection is order-INDEPENDENT (it does not rely on a later re-resolve or the final gate to
    -- catch it). A pass emitting only warnings continues.
    if diags.any (·.kind != .warning) then
      return (program, model, allDiags, allStats)
    -- Run resolve after the pass if needed
    if pass.needsResolves then
      let result := resolve program (some model) (gradualTypes := options.gradualTypes)
                      (realizeCoercion := options.realizeCoercion) (toBool := options.toBool)
                      (reservedNames := options.reservedNames)
      -- `newPostPassResolutionErrors` (mainline) subsumes poly's earlier explicit cascade guard:
      -- it returns `#[]` when the program ALREADY has a non-warning error (initial resolution
      -- failed, or an earlier pass reported one — depth-cap `notYetImplemented` on a divergent
      -- generic, `EliminateExceptions` rejecting a two-output `throws` proc, or a surface error
      -- restated over a monomorphized name like `Box$a1$bool`). In that case a "new" re-resolution
      -- error is a downstream CASCADE, not a compiler bug, so it must NOT be folded as `.strataBug`;
      -- an empty `newErrors` skips the fold below, and the pass loop stops naturally.
      let newErrors := newPostPassResolutionErrors resolutionErrors allDiags result.errors
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
        let isUserCollision (d : Message) : Bool :=
          (d.message.splitOn "Duplicate definition").length > 1
        -- EXCEPTION — a poly `throws` escape mismatch is a genuine USER error deferred to
        -- here, not a compiler bug. A poly `throws (e:T)` cannot be checked at the initial
        -- resolution (T is not concrete), so `validateExceptionEscapes` defers it and re-runs
        -- post-`MonomorphizeComposites`, where the clone's throws type is concrete and an
        -- `int </: bool` escape surfaces as a NEW `.userError` (from `checkProcedureThrows`).
        -- Wrapping it as an internal `.strataBug` would misblame the compiler for the user's
        -- unsound throws contract, so pass these through unchanged. The two markers are the
        -- SAME string constants `checkProcedureThrows` weaves into its two diagnostics, so this
        -- cross-module match is compile-time-guaranteed to stay in sync — rewording a message
        -- can't silently desync the classifier. (Matching on `MessageKind` instead cannot work:
        -- a genuine dangling-ref failure is also a `.userError`.)
        let isExceptionContract (d : Message) : Bool :=
          (d.message.splitOn escapeNotSubtypeMarker).length > 1
            || (d.message.splitOn escapeUndeclaredMarker).length > 1
        let asStrataBug (d : Message) : Message :=
          { d with
              message :=
                s!"Internal error: resolution after '{pass.name}' introduced this diagnostic: {d.message}"
              kind := .strataBug }
        -- Fold a new re-resolution error: an exception-contract escape is a deferred user error
        -- (passed through as its native `.userError`); anything else is a genuine compiler bug.
        let foldNewError (d : Message) : Message :=
          if isExceptionContract d then d else asStrataBug d
        let collisions := newErrors.toList.filter isUserCollision
        if collisions.isEmpty then
          -- No collision ⇒ every new error is a genuine post-transform compiler failure,
          -- except a deferred poly-throws escape (folded as its native user error).
          let newDiags := newErrors.toList.map foldNewError
          emit pass.name "laurel.st" program
          return (program, model, allDiags ++ newDiags, allStats)
        else
          -- A `Duplicate definition` collision is present. Its own downstream CASCADE — type
          -- mismatches restated over the doubly-defined name (a composite named `Box`/`Field`/
          -- `TypeTag` clashing with a lowering-generated datatype yields `expected 'Composite',
          -- got 'Field'` follow-ons) — is not an independent compiler bug and must not be blamed
          -- on the compiler. Report each collision as a clean `.userError` with a rename hint.
          -- The doubly-defined name is quoted in the collision message (`Duplicate definition
          -- 'X'`); a cascade follow-on always MENTIONS that name, so we drop only the new errors
          -- that reference a colliding name and still fail loud (`.strataBug`) on any OTHER new
          -- error — a genuinely independent post-transform failure that merely co-occurred is
          -- NOT masked. (Renaming the identifier removes the collision and routes every new error
          -- through the fail-loud branch above, so nothing is ever permanently hidden.)
          let collidingNames : List String :=
            collisions.filterMap (fun d => (d.message.splitOn "'")[1]?)
          let mentionsColliding (d : Message) : Bool :=
            collidingNames.any (fun n => (d.message.splitOn n).length > 1)
          let hinted := collisions.map fun d =>
            { d with
                message :=
                  s!"{d.message} (this name collides with one introduced by an internal lowering \
                     pass; rename the identifier — a reserved internal type name (e.g. `Box`, \
                     `Heap`, `Field`, `TypeTag`, `Composite`) or a name containing `$` / the \
                     `$aN$` instantiation-tag shape can clash with a synthetic name)"
                kind := .userError }
          let independent := newErrors.toList.filter fun d =>
            !isUserCollision d && !mentionsColliding d
          let newDiags := hinted ++ independent.map foldNewError
          emit pass.name "laurel.st" program
          return (program, model, allDiags ++ newDiags, allStats)
      program := result.program
      model := result.model
    emit pass.name "laurel.st" program

  return (program, model, allDiags, allStats)

/-- The ordered sequence of passes on the unordered Core representation. -/
private def unorderedCorePipeline : Array (LaurelPass UnorderedCoreWithLaurelTypes UnorderedCoreWithLaurelTypes) := #[
  liftImperativeExpressionsPass,
  inlineLocalVariablesPass
]

/--
Soundness backstop: a discarded Core program (`none`) MUST carry at least
one error diagnostic. The downstream pipeline treats a `none` program as
"nothing to verify", so any translation failure that reaches the verifier
without an error diagnostic would be reported as a vacuous "0 errors /
verified". Every known discard site already emits a diagnostic; this
guarantees the property for any future/unknown path too. Returns `diags`
unchanged when the program is present or an error is already reported.
-/
def ensureDiscardDiagnosed (programPresent : Bool) (diags : List Message)
    : List Message :=
  if !programPresent && !diags.any (·.kind != .warning) then
    diags ++ [Message.fromString
      "internal error: Laurel-to-Core translation produced no program without reporting an error diagnostic"
      MessageKind.strataBug]
  else diags

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

  if passDiags.any (·.kind != .warning) then
    return (none, passDiags, program, stats)

  -- Sanity check: `LiftInstanceProcedures` should have cleared every
  -- composite's `instanceProcedures` list.
  let mut passDiags := passDiags
  for td in program.types do
    if let .Composite ct := td then
      for proc in ct.instanceProcedures do
        passDiags := passDiags ++ [diagnosticFromSource proc.name.source
          s!"Instance procedure '{proc.name.text}' on composite type '{ct.name.text}' was not lifted before Core translation (pipeline-ordering bug)"
          MessageKind.strataBug]

  if passDiags.any (·.kind != .warning) then
    return (none, passDiags, program, stats)

  let unorderedCore := (transparencyPass.run options program model).1
  emit "transparencyPass" "core.st" unorderedCore
  let mut unorderedCore := unorderedCore
  let mut fnModel := model
  let mut ucDiags : List Message := []

  -- Re-resolve after transparency pass (needed for synthetic variables it introduces,
  -- e.g. proof-procedure guard variables).
  if transparencyPass.needsResolves then
    let compositeTypes := program.types.filter (fun t => match t with | .Composite _ => true | _ => false)
    -- Thread the same gradual-type and coercion hooks as every other resolve site: this
    -- pass must see the same type lattice as the main `resolve`, or the widen arm (gated
    -- on `realizeCoercion.isSome`) and the `toBool` truthiness hook differ between passes
    -- and a well-formed gradually-typed program is rejected here. See the note on
    -- `resolveUnorderedCore` in `Resolution.lean`.
    let (uc', m', errors) := resolveUnorderedCore unorderedCore (some fnModel) compositeTypes
                              options.gradualTypes options.realizeCoercion options.toBool options.reservedNames
    if !errors.isEmpty then
      let newDiags := errors.toList.map fun d =>
        { d with
            message :=
              s!"Internal error: resolution after '{transparencyPass.name}' introduced this diagnostic: {d.message}"
            kind := .strataBug }
      return (none, passDiags ++ ucDiags ++ newDiags, program, stats)
    unorderedCore := uc'
    fnModel := m'

  for pass in unorderedCorePipeline do
    let (uc, passPassDiags, _) := pass.run options unorderedCore fnModel
    unorderedCore := uc
    ucDiags := ucDiags ++ passPassDiags
    if pass.needsResolves then
      let compositeTypes := program.types.filter (fun t => match t with | .Composite _ => true | _ => false)
      let (uc', m', errors) := resolveUnorderedCore unorderedCore (some fnModel) compositeTypes options.gradualTypes options.realizeCoercion options.toBool options.reservedNames
      if !errors.isEmpty then
        let newDiags := errors.toList.map fun d =>
          { d with message :=
              s!"Internal error: resolution after '{pass.name}' introduced this diagnostic: {d.message}" }
        emit pass.name "unorderedCoreWithLaurelTypes.st" unorderedCore
        return (none, passDiags ++ ucDiags ++ newDiags, program, stats)
      unorderedCore := uc'
      fnModel := m'
    emit pass.name "unorderedCoreWithLaurelTypes.st" unorderedCore

  -- An error introduced by an unordered-core pass (e.g. an assignment to an
  -- inlined local) prevents producing a Core program, just like Laurel pass
  -- errors above.
  if ucDiags.any (·.kind != .warning) then
    return (none, passDiags ++ ucDiags, program, stats)

  let coreWithLaurelTypes := (orderingPass.run options unorderedCore model).1

  emit "CoreWithLaurelTypes" "core.st" coreWithLaurelTypes
  let (coreProgram, coreDiagnostics, _) := laurelToCoreSchemaPass.run options coreWithLaurelTypes fnModel
  let mut allDiagnostics: List Message := passDiags ++ ucDiags ++ coreDiagnostics;

  emit "Core" "core.st" coreProgram
  let coreProgramOption :=
    if coreDiagnostics.isEmpty then some coreProgram else none
  -- Backstop invariant: if the program was discarded, it must carry at least
  -- one (non-warning) diagnostic, otherwise the discard is silent. This nets
  -- any future discard path that forgets to emit a diagnostic.
  allDiagnostics := ensureDiscardDiagnosed coreProgramOption.isSome allDiagnostics
  return (coreProgramOption, allDiagnostics, program, stats)

/--
Translate Laurel Program to Core Program.
-/
def translate (options : LaurelTranslateOptions) (program : Program) : IO TranslateResult := do
  let (core, diags, _, _) ← translateWithLaurel options program
  return (core, diags)

/-- The effective `Core.VerifyOptions` that `runVerify` actually runs with
    (the caller's options plus Laurel's fixed adjustments). -/
private def effectiveCoreVerifyOptions (options : LaurelVerifyOptions) : Core.VerifyOptions :=
  { options.verifyOptions with
    removeIrrelevantAxioms := .Precise
    keepAllFilesPrefix := options.translateOptions.keepAllFilesPrefix }

/-- Run `Core.verify` on a translated Core program, returning the verify-phase
    failure as a **structured** `Message` value (via `.toBaseIO`) rather
    than throwing it, so callers can render it file-relative.

    `Core.verify : EIO Message VCResults` carries its error as a
    `Message` (with byte-offset `fileRange`). Capturing it as an
    `Except` here is the single point where that structure is preserved, so the
    throwing (`verifyToVcResults`) and capturing
    (`verifyToMessagesCapturing`) entry points can't drift apart: both
    share this verify setup (the `effectiveCoreVerifyOptions` adjustments and
    the `vcDirectory` temp-dir handling) and only differ in how they treat the
    `.error` case. -/
private def runVerify (coreProgram : Core.Program) (options : LaurelVerifyOptions)
    : IO (Except Message VCResults) := do
  let verifyOptions := effectiveCoreVerifyOptions options
  let runner tempDir : IO (Except Message VCResults) :=
    (_root_.Core.verify coreProgram tempDir (proceduresToVerify := none) verifyOptions).toBaseIO
  match verifyOptions.vcDirectory with
  | .none => IO.FS.withTempDir runner
  | .some p => IO.FS.createDirAll ⟨p.toString⟩; runner ⟨p.toString⟩

/--
Verify a Laurel program using an SMT solver.

A verify-phase failure (a type-checking / symbolic-evaluation error) is
**thrown** as an `IO` exception: the structured error is intercepted at the
`runVerify` boundary and re-thrown via `toString`, so the CLI's control flow and
exit codes match those of a stringified exception. Tests that need the
structured error as a value (to render it to `line:col`) call
`verifyToMessagesCapturing` instead.
-/
def verifyToVcResults (program : Program)
    (options : LaurelVerifyOptions := default)
    : IO (Option VCResults × List Message) := do
  let (coreProgramOption, translateDiags) ← translate options.translateOptions program

  match coreProgramOption with
  | some coreProgram =>
    match ← runVerify coreProgram options with
    | .ok ioResult => return (some ioResult, translateDiags)
    -- Throwing path: stringify the structured error. A poly fn whose body mismatches
    -- its signature must surface as a Core error FOLDED into the result
    -- (`translated=false`), not a Lean exception — that fold lives in the CAPTURING
    -- entry point consumers use, `verifyToMessagesCapturing`, which routes through this
    -- same `runVerify` boundary and returns `.error` as a value. `verifyToVcResults`
    -- throws instead, preserving the production CLI's exit-code behavior (its only
    -- external caller is `Languages/Laurel.lean`).
    | .error dm => throw (IO.userError (toString dm))
  | none => return (none, translateDiags)

/--
Verify a Laurel program using an SMT solver, returning results with
duplicated assertions merged at the VCOutcome level.

Unlike `verifyToVcResults` (which THROWS a verify-phase error to preserve the
CLI's exit-code behavior), this CAPTURES a Core-side `Message`
failure and folds it into the returned diagnostics: a polymorphic
function whose body is incompatible with its signature is a Core type error that
must surface as a diagnostic (`translated=false`), not a thrown exception. This
is the path the non-throwing consumers (`verifyToDiagnostics`,
`verifyToMessages`) build on. Both
fold-capturing paths share the `runVerify` boundary, so they can't drift from the
throwing path on verify options or temp-dir handling.
-/
def verifyToMergedResults (program : Program)
    (options : LaurelVerifyOptions := default)
    : IO (Option VCResults × List Message) := do
  -- Unlike `verifyToVcResults` (which THROWS a verify-phase error to preserve the CLI's
  -- exit-code behavior), this CAPTURES a Core-side error and folds it into the
  -- returned diagnostics: a polymorphic function whose body is incompatible with its
  -- signature is a Core type error that must surface as a diagnostic (`translated=false`),
  -- not a thrown exception. This is the path the non-throwing consumers build on.
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
  let phases := Core.coreAbstractedPhases (options := effectiveCoreVerifyOptions options)
  let translationDiags := results.snd.map (fun dm => dm.toDiagnostic files)
  let vcDiags := match results.fst with
  | some vcResults => vcResults.toList.filterMap (fun (vcr : VCResult) => Core.VCResult.toDiagnostic files vcr phases)
  | none => []
  return (translationDiags ++ vcDiags).toArray

def verifyToMessages (program : Program) (options : LaurelVerifyOptions := default)
    : IO (Array Message) := do
  let results ← verifyToMergedResults program options
  let phases := Core.coreAbstractedPhases (options := effectiveCoreVerifyOptions options)
  let vcDiags := match results.fst with
  | none => []
  | some vcResults => vcResults.toList.filterMap (fun (vcr : VCResult) => toMessage vcr phases)
  return (results.snd ++ vcDiags).toArray

/-- Like `verifyToMessages`, but a verify-phase failure is **captured**
    as a structured `Message` (the same value `verifyToVcResults` would
    have thrown via `toString`) and returned in the list, rather than thrown.

    This is the test-framework entry point: the structured error still carries
    its byte-offset `fileRange`, so the caller can render it to snippet-local /
    file-relative `line:col` like every other diagnostic — instead of the raw
    byte offset that a stringified exception would leave in its message text.
    Production code keeps using the throwing `verifyTo*` functions above.

    Shares the `runVerify` boundary with `verifyToVcResults`, differing only in
    that it returns the captured `.error` as a value instead of re-throwing it —
    so the two can't drift apart on verify options or temp-dir handling. -/
def verifyToMessagesCapturing (program : Program)
    (options : LaurelVerifyOptions := default) : IO (Array Message) := do
  let (coreProgramOption, translateDiags) ← translate options.translateOptions program
  match coreProgramOption with
  | none => return translateDiags.toArray
  | some coreProgram =>
    match ← runVerify coreProgram options with
    | .error dm => return (translateDiags ++ [dm]).toArray
    | .ok results =>
      let phases := Core.coreAbstractedPhases (options := effectiveCoreVerifyOptions options)
      let vcDiags := results.mergeByAssertion.toList.filterMap (toMessage · phases)
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
