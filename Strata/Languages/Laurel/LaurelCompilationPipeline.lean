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
  -- NOTE (merge of #1381): #1381 inserted `liftInstanceProceduresPass` here so it runs
  -- before `eliminateValueInReturnsPass` (so value-returning instance methods get lowered).
  -- The instance-procedure lift already moved that pass to position 0 (it must precede monomorphization),
  -- which ALSO satisfies #1381's before-eliminateValueInReturns requirement — so the single
  -- pos-0 entry is correct for both; #1381's duplicate insertion is dropped.
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
      if !newErrors.isEmpty then
        let newDiags := newErrors.toList.map fun d =>
          { d with
              message :=
                s!"Internal error: resolution after '{pass.name}' introduced this diagnostic: {d}. Existing diagnostics were: {resolutionErrors.toList}"
              type := .StrataBug }
        emit pass.name "laurel.st" program
        -- Re-resolution fires after each `needsResolves := true` pass (lift at pos 0,
        -- monomorphize at pos 1, and the elim/lift passes later) and a NEW error there is
        -- a genuine post-transform failure (dangling monomorph ref, unresolved inherited
        -- field) — folded in as a StrataBug so it fails loud (translated=false). HeapParam
        -- and TypeHierarchy deliberately set `needsResolves := false` because they are one
        -- logical pass whose intermediate states are not independently re-resolvable.
        -- (This supersedes an earlier polymorphism-branch workaround that SUPPRESSED these
        -- diagnostics — #1389 fixed the spurious-error sources so folding is safe; the
        -- monomorphization re-resolution path is exercised by the polymorphism corpus.)
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
    Single source of truth so the differential harness (`verifyToMetrics`) and
    the production path (`verifyToVcResults`) cannot silently diverge — they must
    measure the same verification. -/
def coreVerifyOptions (options : LaurelVerifyOptions) : Core.VerifyOptions :=
  { options.verifyOptions with removeIrrelevantAxioms := .Precise }

/-- Run `act` with the VC directory dictated by `verifyOpts`: a fresh temp dir
    (auto-cleaned) when none is configured, else the caller's directory. Shared
    by all verify entry points (incl. `verifyToMetrics`, which needs the dir to
    hold its metrics JSONL file). -/
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
    -- Reconstruct the throwing path: stringify the structured error exactly as
    -- the previous `EIO.toIO (fun f => .userError (toString f))` did (#1367).
    -- NOTE (merge): our polymorphism work needs Core errors FOLDED, not thrown
    -- (a poly fn whose body mismatches its signature must surface as
    -- `translated=false`, not a Lean exception). That fold lives in the CAPTURING
    -- entry points our consumers use — `verifyToMetrics` and
    -- `verifyToDiagnosticModelsCapturing` — both of which route through the same
    -- `runVerify` boundary and return `.error` as a value. `verifyToVcResults`
    -- keeps #1367's throwing behavior for the production CLI path (its only
    -- external caller, `Languages/Laurel.lean`).
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
`verifyToDiagnosticModels`) build on, so they agree with `verifyToMetrics`. Both
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

/--
Differential-harness metrics for one verification run (harness plan,
Component 1.1). Re-exposes data the pipeline already computes but the existing
verify wrappers discard: the pass-side `Statistics` (dropped by the thin
`translate` wrapper via `(core, diags, _, _)`) and the per-obligation verdicts.

Scope:
- `passStats` is the `Statistics` surfaced by `translateWithLaurel`.
- `coreStats` is the Core-evaluator `Statistics` surfaced via `Core.verifyWithStats`
  (Component 1.2 — carries `verify_numObligations`, `processIteBranches_diverged`,
  etc., the structural-cost proxy for the U-vs-G / C1 comparison).
- `vcDischargeMs` is the SMT-discharge wall-clock, **consumed** from the pipeline's
  existing per-phase timing (Component 3 — a `metricsHandle`-backed
  `PipelineContext` threaded into `Core.verifyWithStats`, then the `vcDischarge`
  record read back). Not a new measurement primitive. `none` if no record found.
- Verdicts are keyed on `"<index>:<obligation.label>"` (the index makes the key
  unique — bare labels collide across procedures) and carry the raw
  `Except VCError VCOutcome` so the `.error` case is preserved.
-/
structure VerifyMetrics where
  verdicts      : Array (String × Except Core.VCError Core.VCOutcome)
  passStats     : Statistics
  coreStats     : Statistics
  numVCs        : Nat
  /-- Count of obligations that did NOT verify successfully, via
      `VCResult.isNotSuccess` (= `!isPass`). This lumps together genuine
      `fail` AND `error`/`unknown` outcomes — coarser than `verdicts`, which
      distinguishes `fail` from `error`. Use `numFailures == 0` for the
      all-verified gate; inspect `verdicts` to tell *why* an obligation didn't
      pass. The two are consistent (both treat non-pass as non-success), just at
      different granularity. -/
  numFailures   : Nat
  translated    : Bool
  /-- SMT discharge wall-clock in ms, from the `vcDischarge` timing record.
      `none` when the metrics file had no such record (e.g. `checkOnly`). -/
  vcDischargeMs : Option Nat

/-- Parse a metrics-JSONL file and extract the `end_ms - start_ms` of the
    `vcDischarge` timing record (Component 3). Each line is a JSON object; we
    scan for `{"type":"timing","phase":"vcDischarge",…}`. Best-effort: returns
    `none` if absent or unparseable.

    Relies on two invariants of `Core.verify`'s current pipeline
    (`Verifier.lean`): (1) there is exactly ONE top-level `withPhase
    "vcDischarge"`, so exactly one matching record — first/last/sum are
    equivalent and we take the first; (2) nested sub-phases serialize as dotted
    `phase` names (`Phase.display`, e.g. `"vcDischarge.encodeSMT"`), which the
    exact `"vcDischarge"` match deliberately excludes. If discharge ever runs in
    a loop, this would report only the first slice — revisit then. `e - s` is
    `Nat`-saturating; both come from one monotonic clock with `e` after `s`, and
    sub-ms spans may round to `some 0` (present-but-zero, not `none`). -/
def parseVcDischargeMs (contents : String) : Option Nat := Id.run do
  for line in contents.splitOn "\n" do
    match Lean.Json.parse line with
    | .error _ => continue
    | .ok j =>
      match j.getObjValAs? String "type", j.getObjValAs? String "phase" with
      | .ok "timing", .ok "vcDischarge" =>
        match j.getObjValAs? Nat "start_ms", j.getObjValAs? Nat "end_ms" with
        | .ok s, .ok e => return some (e - s)
        | _, _ => continue
      | _, _ => continue
  return none

/--
Verify a Laurel program and return `VerifyMetrics`, keeping the pass-side
`Statistics` (which `translate`/`verifyToVcResults` discard), the Core-evaluator
`Statistics` (via `Core.verifyWithStats`), and the `vcDischarge` wall-clock
(consumed from the pipeline's existing per-phase metrics). Does not change any
existing diagnostic-asserting path.
-/
def verifyToMetrics (program : Program) (options : LaurelVerifyOptions := default)
    : IO VerifyMetrics := do
  let (coreProgramOption, _diags, _program, passStats) ←
    translateWithLaurel options.translateOptions program
  match coreProgramOption with
  | some coreProgram =>
    let verifyOpts := coreVerifyOptions options
    -- Run inside a temp/VC dir holding a metrics JSONL file. A `metricsHandle`-
    -- backed PipelineContext makes `Core.verify`'s existing `withPhase
    -- "vcDischarge"` emit a timing record we read back (Component 3).
    let run (dir : System.FilePath) : IO (Except DiagnosticModel (VCResults × Statistics × Option Nat)) := do
      let metricsPath := dir / "metrics.jsonl"
      -- `emitMetric` opens nothing and flushes after every record, so the handle
      -- needs no explicit lifecycle management (Lean has no `Handle.close`;
      -- handles are GC-finalized, and `withVcDir`'s temp dir is auto-removed).
      let h ← IO.FS.Handle.mk metricsPath .write
      let pctx ← (Strata.Pipeline.PipelineContext.create
        (outputMode := .quiet) (metricsHandle := some h) : BaseIO _)
      -- Catch a Core-side DiagnosticModel failure rather than throwing (mirroring
      -- verifyToMergedResults): a Core type error means the program did not verify,
      -- so it surfaces as `translated := false`, not a Lean exception.
      match ← (_root_.Core.verifyWithStats coreProgram dir .none verifyOpts
            (pipelineCtx := some pctx)).toBaseIO with
      | .error coreDiag => pure (.error coreDiag)
      | .ok (merged, coreStats) =>
        let contents ← IO.FS.readFile metricsPath
        pure (.ok (merged, coreStats, parseVcDischargeMs contents))
    match ← withVcDir verifyOpts run with
    | .error _coreDiag =>
      -- Core rejected the (translated) program — report as not-translated for the
      -- metrics view, with no obligations.
      return { verdicts := #[], passStats, coreStats := {}, numVCs := 0,
               numFailures := 0, translated := false, vcDischargeMs := none }
    | .ok (merged, coreStats, vcDischargeMs) =>
    -- Key verdicts on (index, label): `mergeByAssertion` preserves first-occurrence
    -- order, but bare `obligation.label` is NOT unique (two procedures can both emit
    -- `postcondition_0`), so the index disambiguates for stable serialization/diff.
    let verdicts := merged.mapIdx (fun i (vcr : VCResult) =>
      (s!"{i}:{vcr.obligation.label}", vcr.outcome))
    let numFailures := merged.foldl (fun acc vcr => if vcr.isNotSuccess then acc + 1 else acc) 0
    return { verdicts, passStats, coreStats, numVCs := merged.size, numFailures,
             translated := true, vcDischargeMs }
  | none =>
    return { verdicts := #[], passStats, coreStats := {}, numVCs := 0, numFailures := 0,
             translated := false, vcDischargeMs := none }

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
