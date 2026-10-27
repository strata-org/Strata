/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import Strata.Pipeline.Messages

public import StrataLaurel.Implementation.LaurelToCoreSchemaPass
import StrataLaurel.Implementation.DesugarShortCircuit
import StrataLaurel.Implementation.EliminateReturnStatements
import StrataLaurel.Implementation.EliminateDoWhile
-- The passes' `NodeKind` declarations, proven against the pass bodies. Imported
-- here so the pipeline's build checks them: `orderingRespected` below derives the
-- pass order from declarations that these proofs tie to what the passes do.
import StrataLaurel.Implementation.EliminateDoWhileProps
import StrataLaurel.Implementation.EliminateIncrDecrAndCompoundAssignProps
import StrataLaurel.Implementation.ResolutionProps
import StrataLaurel.Implementation.EliminateIncrDecrAndCompoundAssign
import StrataLaurel.Implementation.CopyMutatedInputs
import StrataLaurel.Implementation.EliminateValueInReturns
import StrataLaurel.Implementation.ModifiesClauses
import StrataLaurel.Implementation.HeapParameterization
import StrataLaurel.Implementation.GlobalParameterization
import StrataLaurel.Implementation.TypeHierarchy
import StrataLaurel.Implementation.InferHoleTypes
import StrataLaurel.Implementation.EliminateDeterministicHoles
import StrataLaurel.Implementation.CoreDefinitionsForLaurel
import StrataLaurel.Implementation.CoreGroupingAndOrdering
import StrataLaurel.Implementation.TransparencyPass
import StrataLaurel.Implementation.FilterPrelude
import StrataLaurel.Implementation.LiftImperativeExpressions
import StrataLaurel.Implementation.InlineLocalVariables
import StrataLaurel.Implementation.FunctionalRewrite
import StrataLaurel.Implementation.ConstrainedTypeElim
import StrataLaurel.Implementation.ContractPass
import StrataLaurel.Implementation.LoopInvariantWellFormedness
import StrataLaurel.Implementation.UniqueOverloadNames
import StrataLaurel.Implementation.PushOldInward
import StrataLaurel.Implementation.LiftInstanceProcedures
import StrataLaurel.Implementation.CoroutineElaboration
import StrataLaurel.Implementation.YieldElim
import StrataLaurel.Implementation.CheckOverrideRefinement
import StrataLaurel.Implementation.TypeAliasElim
import StrataLaurel.Implementation.EliminateExceptions
import StrataLaurel.Implementation.MonomorphizeComposites
import StrataLaurel.Implementation.LaurelNodeKindCheck
public import StrataLaurel.Implementation.LaurelPass
public import Strata.Languages.Core
import Strata.Languages.Core.DDMTransform.ASTtoCST
import Strata.Languages.Core.Verifier
import StrataLaurel.Implementation.Grammar.AbstractToConcreteTreeTranslator
import Strata.Util.Statistics

/-!
## Laurel Compilation Pipeline

Orchestrates the Laurel-to-Laurel lowering passes and the final translation
to Strata Core. Every pass runs on a `Program`, and `laurelPipeline` is the
single list of passes:

1. Prepend core definitions for Laurel and resolve.
2. Run the Laurel-to-Laurel lowering passes on a `Program.Unordered`
   (heap parameterization, type hierarchy, modifies clauses, hole inference,
   desugaring, lifting, constrained type elimination, contract pass).
3. The transparency pass splits the procedures into `staticFunctions` and
   `staticProcedures`, which the unordered-core passes rewrite.
4. The ordering pass groups and orders declarations into a
   `Program.Ordered (.WithLaurelTypes _)`.
5. The Core schema pass translates that to a `Program.Ordered (.Core _)`.
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
abbrev TranslateResultWithLaurel := (Option Core.Program) × (List Message) × LaurelProgram × Statistics

/-- The ordered sequence of passes, from a Laurel program to a Core program. -/
def laurelPipeline : Array LaurelPass := #[
  -- Coroutine elaboration emits instance procedures, so it must precede instance lifting.
  coroutineElaborationPass,
  -- Behavioral-subtyping (Liskov) check for method overrides: purely additive (appends
  -- checker procedures), and the soundness prerequisite for dynamic dispatch. Its ordering
  -- matters for soundness, not just tidiness: a checker running after the methods are
  -- flattened off their composites would emit zero checkers and silently accept a
  -- Liskov-violating override, since covariance is guarded by the checker alone.
  checkOverrideRefinementPass,
  -- Polymorphism: lift instance procedures, then monomorphize (the lift must precede
  -- monomorphization).
  liftInstanceProceduresPass,
  -- TypeAliasElim runs BEFORE monomorphization: an alias of a generic-composite instantiation
  -- (`type BInt = Box<int>`, or a generic `type Foo<T> = Box<T>` used at `Foo<int>`) must unfold
  -- to `Box<int>` so the monomorphizer sees the real `.Applied` and rewrites it to `Box$a1$int`.
  -- Mono is alias-agnostic (no `.Alias` refs); alias-elim only needs the first resolve, which
  -- precedes the whole pipeline. Nothing pins their relative order.
  typeAliasElimPass,
  -- Monomorphization must run before heap parameterization: HeapParam boxes composite fields
  -- into the non-parametric Box datatype, so any generic composite still un-monomorphized at
  -- that point would be boxed with no concrete instantiation and reach Core un-lowered.
  monomorphizeCompositesPass,
  eliminateDoWhilePass,
  eliminateIncrDecrAndCompoundAssignPass,
  -- Placement rationale in the pass's module header.
  copyMutatedInputsPass,
  constrainedTypeElimPass,
  -- `liftInstanceProceduresPass` runs before monomorphization; that also places it before
  -- `eliminateValueInReturnsPass`, as value-returning instance methods require, so no entry
  -- is needed here.
  -- Note: the exception contract checks (the declared `throws` upper bound, plus the
  -- "not yet lowerable" source-shape guards) are *not* a pipeline pass. They are
  -- properties of the authored program, so `resolve` runs them on the initial
  -- resolution only — see `validateExceptionEscapes` /
  -- `validateExceptionLowerability` in `Resolution.lean`.
  eliminateValueInReturnsPass,
  eliminateExceptionsPass,
  -- The heap trio: `HeapParameterization` declares `$heap` as a file-scope global
  -- and rewrites field access against it; `TypeHierarchy` lowers `New` (which also
  -- writes the heap); `ModifiesClauses` builds the frames. They share one
  -- re-resolve, which binds those `$heap` references as `$static` fields.
  --
  -- `globalParameterizationPass` runs after the trio: the heap global does not exist
  -- until `HeapParameterization` declares it. Monomorphization precedes the trio (see
  -- `monomorphizeCompositesPass` above), so globals are layered onto already-
  -- monomorphized concrete procedures.
  yieldElimPass,
  heapParameterizationPass,
  typeHierarchyTransformPass,
  modifiesClausesTransformPass,
  -- Threads `$heap` like any other global. Must follow the trio: the global does
  -- not exist until `HeapParameterization` declares it, and `TypeHierarchy`
  -- introduces further heap writes.
  globalParameterizationPass,
  -- After global threading, so `old(g)` normalizes for an arbitrary global: a
  -- written global is by now an inout in the ordinary signature sense, which is
  -- what `procInoutNames` recognizes. Before `Contracts`, so that pass sees `$heap`
  -- as a plain inout and its existing `$out` machinery handles it unchanged.
  pushOldInwardPass,
  inferHoleTypesPass,
  eliminateDeterministicHolesPass,
  uniqueOverloadNamesPass,
  desugarShortCircuitPass,
  eliminateReturnStatementsPass,
  loopInvariantWellFormednessPass,
  contractPass,
  transparencyPass,
  functionalRewritePass,
  liftImperativeExpressionsPass,
  inlineLocalVariablesPass,
  orderingPass,
  laurelToCoreSchemaPass
]

/-- A shape the input must not contain: phase `pass`, at `position` in the order, does not
    support `kind`, and no earlier phase removes it. -/
structure InputRequirement where
  kind : NodeKind
  pass : String
  position : Nat
  message : String

def newPostPassResolutionErrors (initialDiags : Std.HashSet Message)
    (diagsSoFar : List Message) (postPassDiags : Array Message) : Array Message :=
  if diagsSoFar.any (·.kind != .warning) then #[]
  else postPassDiags.filter fun e => e.kind != .warning && !initialDiags.contains e

/--
Run every pass of `laurelPipeline` on a program, returning the final program, the
last Laurel program it passed through, the accumulated diagnostics, the diagnostics
of the last pass that ran, and merged statistics.

When `keepAllFilesPrefix` is provided (via the `PipelineM` context), the
program state after each pass is written to
`{prefix}.{n}.{passName}.{Program.fileExtension}`.
-/
private def runLaurelPasses
    (options: LaurelTranslateOptions) (passes : Array LaurelPass)
    (inputRequirements : List InputRequirement)
    (pctx : Strata.Pipeline.PipelineContext) (program : LaurelProgram)
    : PipelineM (Program × LaurelProgram × List Message × List Message × Statistics) := do
  -- Must run HERE, before the prelude is prepended below and before the first resolve:
  -- see `validateNoDollarNames`. Bails out rather than resolving, so the diagnostic
  -- lands on the declaration rather than on a later collision.
  let dollarDiags := validateNoDollarNames program
  let staticFunctionDiags := program.staticFunctions.map fun proc =>
    diagnosticFromSource proc.name.source
      s!"'{proc.name.text}' is a static function; an input program may not declare static functions, which the transparency pass introduces"
      MessageKind.userError
  let inputDiags := dollarDiags ++ staticFunctionDiags
  if inputDiags.any (·.kind != .warning) then
    return (.Unordered program, program, inputDiags, [], {})

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
  let mut laurelProgram := result.program
  let mut program : Program := .Unordered result.program
  let mut model := result.model
  let mut allDiags : List Message := result.errors.toList
  let mut lastDiags : List Message := []
  let mut allStats : Statistics := {}

  if result.errors.any (·.kind != .warning) then
    return (program, laurelProgram, allDiags, lastDiags, allStats)

  let required := inputRequirements.map (·.kind)
  unless required.isEmpty || Program.containsB (fun k => !required.contains k) program do
    let present := Program.presentKinds required program
    unless present.isEmpty do
      let inputDiags := inputRequirements.filterMap fun r =>
        if present.contains r.kind then some (Message.fromString r.message MessageKind.userError)
        else none
      return (program, laurelProgram, allDiags ++ inputDiags, lastDiags, allStats)

  for pass in passes do
    let (program', diags, stats) ← pctx.withPhase pass.name do pure (pass.run options program model)
    program := program'
    if let .Unordered p := program then laurelProgram := p
    allDiags := allDiags ++ diags
    lastDiags := diags
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
      return (program, laurelProgram, allDiags, lastDiags, allStats)
    -- Run resolve after the pass if needed
    if pass.needsResolves then
      match program with
      | .Unordered p =>
        let result := resolve p (some model) (gradualTypes := options.gradualTypes)
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
          -- bug: `$`, the `$aN$` tag shape, and the reserved internal type names (`Heap`, `Field`,
          -- `TypeTag`, `Composite`) are all legal in source, so a user can declare one.
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
          -- unsound throws contract, so pass these through unchanged. The marker is the
          -- SAME string constant `checkProcedureThrows` weaves into its diagnostic, so this
          -- cross-module match is compile-time-guaranteed to stay in sync — rewording a message
          -- can't silently desync the classifier. (Matching on `MessageKind` instead cannot work:
          -- a genuine dangling-ref failure is also a `.userError`.)
          let isExceptionContract (d : Message) : Bool :=
            (d.message.splitOn escapeNotSubtypeMarker).length > 1
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
            emit pass.name "laurel.st" p
            return (program, laurelProgram, allDiags ++ newDiags, lastDiags, allStats)
          else
            -- A `Duplicate definition` collision is present. Its own downstream CASCADE — type
            -- mismatches restated over the doubly-defined name (a composite named `Field`/
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
                       pass; rename the identifier — a reserved internal type name (e.g. `Heap`, \
                       `Field`, `TypeTag`, `Composite`) or a name containing `$` / the \
                       `$aN$` instantiation-tag shape can clash with a synthetic name)"
                  kind := .userError }
            let independent := newErrors.toList.filter fun d =>
              !isUserCollision d && !mentionsColliding d
            let newDiags := hinted ++ independent.map foldNewError
            emit pass.name "laurel.st" p
            return (program, laurelProgram, allDiags ++ newDiags, lastDiags, allStats)
        program := .Unordered result.program
        laurelProgram := result.program
        model := result.model
      | other =>
        return (program, laurelProgram, allDiags ++ [Message.fromString
          s!"Internal error: pass '{pass.name}' needs re-resolution, which a {other.kind} program does not support" .strataBug],
          lastDiags, allStats)
    emit pass.name program.fileExtension program

  return (program, laurelProgram, allDiags, lastDiags, allStats)

/-- A pass whose declarations are not satisfied by the pipeline order. -/
structure OrderingFailure where
  pass : String
  kind : NodeKind
  stillPresent : Bool := false
  /-- What went wrong, for the failure message. -/
  reason : String
  deriving Repr

/-- A dependency between two passes, as the fold observed it: `later` names `kind` in its
    `unsupported`, and `earlier` is the pass that last removed it. -/
structure PassDependency where
  earlier : String
  later : String
  kind : NodeKind
  reason : String
  deriving Repr

private inductive ShapeOrigin where
  | input
  | created
  deriving BEq, Repr

private structure PhaseObservation where
  pass : String
  position : Nat
  declarationFailures : List OrderingFailure
  live : List (NodeKind × ShapeOrigin)

private def stillLive (pass : String) (k : NodeKind) : OrderingFailure :=
  { pass, kind := k, reason := "declared unsupported but still live here", stillPresent := true }

private def shapeFoldOf (passes : List PassMeta) (entry : NodeKind → Bool) :
    List PhaseObservation × List PassDependency := Id.run do
  let mut origin : NodeKind → Option ShapeOrigin := fun k => if entry k then some .input else none
  -- The pass that last removed each shape, for dependency provenance.
  let mut lastRemover : Std.HashMap NodeKind String := {}
  let mut observations : List PhaseObservation := []
  let mut deps : List PassDependency := []
  for (p, i) in passes.zipIdx do
    let mut declarationFailures : List OrderingFailure := []
    for k in p.creates do
      if p.removes.contains k then
        declarationFailures := declarationFailures ++
          [{ pass := p.name, kind := k, reason := "declared in both creates and removes" }]
      if p.unsupported.contains k then
        declarationFailures := declarationFailures ++
          [{ pass := p.name, kind := k, reason := "declared in both creates and unsupported" }]
    let mut live : List (NodeKind × ShapeOrigin) := []
    for k in p.unsupported do
      if let some o := origin k then
        live := live ++ [(k, o)]
      else if let some earlier := lastRemover[k]? then
        deps := deps ++
          [{ earlier, later := p.name, kind := k, reason := "removes → unsupported" }]
    observations := observations ++ [{ pass := p.name, position := i + 1, declarationFailures, live }]
    -- Bind the declarations before updating `origin`, so the closure does not capture it.
    let (removes, creates, name) := (p.removes, p.creates, p.name)
    for k in removes do lastRemover := lastRemover.insert k name
    -- `creates` wins, which the check above has already rejected as a declaration: the shape
    -- stays live, so a downstream `unsupported` on it fails loudly rather than in silence.
    origin := fun k =>
      if creates.contains k then some .created
      else if removes.contains k then none
      else origin k
  return (observations, deps)

/-- The result of folding the live shape set over the pipeline: the failures, and the
    dependencies observed on the way.

    The live set starts at `NodeKind.inSource` — the shapes an authored program can
    contain — and each pass updates it to `(live \ removes) ∪ creates`. Before a pass runs,
    nothing in its `unsupported` list may be live: every shape it cannot handle must already
    have been removed on this path. Delete the pass that removes a shape and the pass
    declaring it `unsupported` fails.

    `NodeKind.inSource` is therefore load-bearing. Misclassifying a source shape as
    pipeline-generated weakens this check silently — see the note there.

    Re-creating a shape after it has been removed is allowed, so long as nothing downstream
    declares it `unsupported`. A *single* pass declaring the same shape twice is not: a shape
    in both `creates` and `removes`, or in both `creates` and `unsupported`, is rejected here
    rather than resolved. Such a declaration carries no information — the live-set update
    treats a shape in `creates` and `removes` exactly as it treats one in neither — while
    reading as though the shape is gone, and a pass's `Contains` specification cannot
    contradict it: `(s \ removes) ∪ creates` holds the shape either way. The way to say
    "the source form is gone, mine remains" is to declare the two forms as separate refined
    kinds, as `EliminateDoWhile` does with `While` and `While.postTest.true`. -/
def orderingAnalysisOf (passes : List PassMeta) (entry : NodeKind → Bool := NodeKind.inSource) :
    List OrderingFailure × List PassDependency :=
  let (observations, deps) := shapeFoldOf passes entry
  (observations.flatMap fun o => o.declarationFailures ++ o.live.map (stillLive o.pass ·.1), deps)

private structure PassSelection where
  passes : Array LaurelPass
  inputRequirements : List InputRequirement := []

private def PassSelection.default : PassSelection := { passes := laurelPipeline }

private def PassSelection.metas (s : PassSelection) : List PassMeta :=
  s.passes.toList.map (·.toPassMeta)

def structuralPassNames : List String :=
  [transparencyPass.name, orderingPass.name, laurelToCoreSchemaPass.name]

def defaultPassNames : List String :=
  (laurelPipeline.toList.map (·.name)).filter (!structuralPassNames.contains ·)

def unselectablePassName (nm hint : String) : String :=
  if structuralPassNames.contains nm then s!"Phase '{nm}' always runs and cannot be named."
  else Pipeline.unknownPhaseName nm hint

private def beforeTransparency : List LaurelPass :=
  laurelPipeline.toList.takeWhile (·.name != transparencyPass.name)

private def afterTransparency : List LaurelPass :=
  ((laurelPipeline.toList.dropWhile (·.name != transparencyPass.name)).drop 1).filter
    (!structuralPassNames.contains ·.name)

private def selectPasses (names : List String) (hint : String) : Except String PassSelection := do
  if let some dup := names.find? (fun n => names.count n > 1) then
    throw s!"Phase '{dup}' is named more than once; each phase may be named only once."
  let mut lowering : Array LaurelPass := #[]
  let mut unorderedCore : Array LaurelPass := #[]
  let mut lastAfterTransparency : Option String := none
  for nm in names do
    if let some p := beforeTransparency.find? (·.name == nm) then
      if let some later := lastAfterTransparency then
        throw s!"Phase '{nm}' runs before {transparencyPass.name}, so it cannot follow '{later}', which runs after it."
      lowering := lowering.push p
    else if let some p := afterTransparency.find? (·.name == nm) then
      lastAfterTransparency := some nm
      unorderedCore := unorderedCore.push p
    else
      throw (unselectablePassName nm hint)
  return { passes := lowering ++ #[transparencyPass] ++ unorderedCore ++ #[orderingPass, laurelToCoreSchemaPass] }

private def removerHint (run : List PassMeta) (pos : Nat) (k : NodeKind) : String :=
  let later := run.drop pos
  match later.findIdx? (·.removes.contains k), later.find? (·.removes.contains k) with
  | some j, some p => s!" '{p.name}' at position {pos + j + 1} removes it; move it before position {pos}."
  | _, _ =>
    let unused := PassSelection.default.metas.filter fun d => !run.any (·.name == d.name)
    match unused.find? (·.removes.contains k) with
    | some p => s!" '{p.name}' removes it; insert it before position {pos}."
    | none => ""

private def describeFailure (run : List PassMeta) (f : OrderingFailure) : String :=
  if !f.stillPresent then s!"  {f.pass}: {f.kind} {f.reason}" else
  let pos := ((run.findIdx? (·.name == f.pass)).getD 0) + 1
  s!"  Phase {pos} '{f.pass}' does not support {f.kind}, which is still present when it runs."
    ++ removerHint run pos f.kind

private def orderCheckOf (run : List PassMeta) :
    List OrderingFailure × List InputRequirement := Id.run do
  let mut failures : List OrderingFailure := []
  let mut requirements : List InputRequirement := []
  let mut reported : List NodeKind := []
  for o in (shapeFoldOf run NodeKind.inSource).fst do
    let mut created : List OrderingFailure := []
    let mut fromInput : List OrderingFailure := []
    for (k, origin) in o.live do
      match origin with
      | .created => created := created ++ [stillLive o.pass k]
      | .input =>
        if reported.contains k then continue
        reported := reported ++ [k]
        if !k.isPseudo then
          requirements := requirements ++ [{
            kind := k, pass := o.pass, position := o.position
            message := s!"The program contains {k}, which phase {o.position} '{o.pass}' does not support."
              ++ removerHint run o.position k }]
        else if !o.declarationFailures.any (·.kind == k) then
          fromInput := fromInput ++ [stillLive o.pass k]
    failures := failures ++ o.declarationFailures ++ created ++ fromInput
  return (failures, requirements)

private def resolvePassSelection (names : List String) (hint : String := "") :
    Except String PassSelection := do
  let sel ← selectPasses names hint
  let run := sel.metas
  let (failures, requirements) := orderCheckOf run
  unless failures.isEmpty do
    throw ("This phase order does not satisfy the phases' declarations:\n"
      ++ "\n".intercalate (failures.map (describeFailure run)))
  return { sel with inputRequirements := requirements }

def checkPassSelection (names : List String) (hint : String := "") :
    Except String (List String) :=
  (resolvePassSelection names hint).map fun sel => sel.metas.map (·.name)

def passSelectionContracts (names : Option (List String)) (hint : String := "") :
    Except String (List PassMeta) := do
  let sel ← match names with
    | none => pure PassSelection.default
    | some ns => selectPasses ns hint
  return sel.metas

def resolvePassOrder (names : List String) (hint : String := "") :
    Except String (List String × List InputRequirement) :=
  (resolvePassSelection names hint).map fun sel => (sel.metas.map (·.name), sel.inputRequirements)

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

When `keepAllFilesPrefix` is provided, the program state after each pass is
written to `{prefix}.{n}.{passName}.{Program.fileExtension}`.
-/
def translateWithLaurel (options : LaurelTranslateOptions) (program : LaurelProgram)
    (pipelineCtx : Option Strata.Pipeline.PipelineContext := none)
    : IO TranslateResultWithLaurel := do
  let pctx ← match pipelineCtx with
    | some ctx => pure ctx
    | none => Strata.Pipeline.PipelineContext.create (outputMode := .quiet)
  let selection ← match options.passes with
    | none => pure PassSelection.default
    | some names => match resolvePassSelection names with
      | .ok sel => pure sel
      | .error msg => return (none, [Message.fromString msg MessageKind.userError], program, {})
  runPipelineM options.keepAllFilesPrefix do
  let (program, laurelProgram, diags, lastDiags, stats) ←
    runLaurelPasses options selection.passes selection.inputRequirements pctx program
  if diags.any (·.kind != .warning) then
    return (none, diags, laurelProgram, stats)
  let coreProgramOption := match program with
    | .Ordered (.Core coreProgram) => if lastDiags.isEmpty then some coreProgram else none
    | _ => none
  -- Backstop invariant: if the program was discarded, it must carry at least
  -- one (non-warning) diagnostic, otherwise the discard is silent. This nets
  -- any future discard path that forgets to emit a diagnostic.
  return (coreProgramOption, ensureDiscardDiagnosed coreProgramOption.isSome diags, laurelProgram, stats)

/--
Translate Laurel Program to Core Program.
-/
def translate (options : LaurelTranslateOptions) (program : LaurelProgram) : IO TranslateResult := do
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
    (_root_.Core.verify coreProgram tempDir verifyOptions).toBaseIO
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
def verifyToVcResults (program : LaurelProgram)
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
def verifyToMergedResults (program : LaurelProgram)
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

def verifyToDiagnostics (files : Map Strata.Uri Lean.FileMap) (program : LaurelProgram)
    (options : LaurelVerifyOptions := default) : IO (Array Diagnostic) := do
  let results ← verifyToMergedResults program options
  let phases := Core.coreAbstractedPhases (options := effectiveCoreVerifyOptions options)
  let translationDiags := results.snd.map (fun dm => dm.toDiagnostic files)
  let vcDiags := match results.fst with
  | some vcResults => vcResults.toList.filterMap (fun (vcr : VCResult) => Core.VCResult.toDiagnostic files vcr phases)
  | none => []
  return (translationDiags ++ vcDiags).toArray

def verifyToMessages (program : LaurelProgram) (options : LaurelVerifyOptions := default)
    : IO (Array Message) := do
  let results ← verifyToMergedResults program options
  let phases := Core.coreAbstractedPhases (options := effectiveCoreVerifyOptions options)
  let vcDiags := match results.fst with
  | none => []
  | some vcResults =>
    vcResults.toList.filterMap (fun (vcr : VCResult) => toMessage vcr phases)
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
def verifyToMessagesCapturing (program : LaurelProgram)
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


public def orderingAnalysis : List OrderingFailure × List PassDependency :=
  orderingAnalysisOf PassSelection.default.metas

/-- Passes whose declarations the pipeline order does not satisfy. Empty when the order is
    valid with respect to the declarations. -/
public def orderingFailures : List OrderingFailure := orderingAnalysis.fst

/-- The pass dependencies the fold observed, for documentation generation. -/
public def passDependencies : List PassDependency := orderingAnalysis.snd

/-- The pipeline order satisfies every pass's `unsupported` declarations. -/
public def orderingRespected : Bool := orderingFailures.isEmpty

-- Use `initialize` to check at load time instead of `#guard` which requires
-- interpreter IR that is not available for passes defined in `module` files.
initialize do
  unless orderingRespected do
    let rendered := orderingFailures.map fun f =>
      s!"  {f.pass}: {f.kind} {f.reason}"
    throw <| .userError
      ("laurelPipeline: pass declarations are not satisfied by the pipeline order:\n"
        ++ "\n".intercalate rendered)

end Laurel
