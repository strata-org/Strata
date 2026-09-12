/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import Strata.Pipeline.Messages

public import StrataDDM
public import Strata.Languages.Core.Verifier
public import Strata.Languages.Core.PipelinePhase
public import Strata.Languages.Core.PipelinePhasePrinter
public import Strata.Transform.ProcedureInlining
import Strata.Transform.CallElim
import Strata.Transform.LoopElim
import Strata.Transform.InsertLoopInvariantAsserts
import Strata.Transform.FilterProcedures

/-! ## Strata Core Transform & Verification API

Translation between the generic Strata AST and the Core dialect AST,
Core program transformations, and Core program verification.

## Differences between Boogie and Strata.Core

1. Strata.Core does not have global variables.

2. Unlike Boogie, Strata.Core is sensitive to global declaration order. E.g.,
   a function must be declared before it can be used in a procedure.

3. Strata.Core does not (yet) support polymorphism.

4. Strata.Core supports `exit` statements that exit the nearest enclosing
   block with a matching label (or the nearest block if no label is given).
   Strata does not support arbitrary `goto` statements.

5. Strata.Core does not support `where` clauses and `unique` constants,
   requiring a tool like `BoogieToStrata` to desugar them.
-/

public section

namespace Strata

open Strata.CoreDDM

/-! ### Transformation between generic and dialect-specific representation -/

/--
Translate a program in the dialect-specific AST for Core into the generic Strata
AST. Usually useful as a step before serialization. Conversion goes through the
Core CST built by `Strata.programToCST`, then projects each `Command` back to
its underlying `Operation` via the DDM-generated `toAst`.
-/
def coreToStrataProgram (p : Core.Program) : StrataDDM.Program :=
  let (_finalCtx, cmds) := Strata.programToCST (M := SourceRange) p
  let ops := cmds.map (·.toAst) |>.toArray
  StrataDDM.Program.create Core_map "Core" ops

/--
Translate a program in the generic AST for Strata into the dialect-specific AST
for Core. This can fail with an error message if the input is not a
well-structured instance of the Core dialect. The optional `ictx` is used to
attach source-range metadata (file name) to the translated program.
-/
def strataProgramToCore (p : StrataDDM.Program)
    (ictx : Lean.Parser.InputContext := Inhabited.default)
    : Except String Core.Program :=
  let (program, errors) := Core.getProgram p ictx
  if errors.isEmpty then
    .ok program
  else
    .error s!"Core DDM translation errors:\n{String.intercalate "\n" errors.toList}"

/-! ### Default Core factory

`Core.defaultFactory` is the default `Lambda.Factory` for the Core dialect: it
contains all built-in integer, boolean, real, string, regex, map, sequence,
and bitvector functions. Pass it as the `moreFns` argument when extending the
factory with additional functions (e.g., `Core.defaultFactory.append ...`).
-/

/-- The default `Lambda.Factory` for the Core dialect. -/
def Core.defaultFactory : Lambda.Factory Core.CoreLParams := Core.Factory

/-! ### Type checking and obligation building -/

/--
Type-check a Core program. Returns the annotated program on success, or a
`Message` describing the error on failure.
-/
def Core.typeCheck (options : Core.VerifyOptions) (program : Core.Program)
    (moreFns : Lambda.Factory Core.CoreLParams := Lambda.Factory.default) :
    Except Message Core.Program := do
  let factory ← Core.Factory.addFactory moreFns
  _root_.Core.typeCheck options program factory

/--
Type-check a Core program, then run symbolic evaluation. Returns the list of
post-evaluation environments and accumulated statistics.
-/
def Core.typeCheckAndEval (options : Core.VerifyOptions) (program : Core.Program)
    (moreFns : Lambda.Factory Core.CoreLParams := Lambda.Factory.default) :
    Except Message ((List Core.Env) × Statistics) :=
  _root_.Core.typeCheckAndEval options program moreFns

/--
Type-check a Core program, then build the proof-obligation program suitable for
downstream phases (Common subexpression elimination, SMT encoding).
-/
def Core.typeCheckAndBuildObligationProgram
    (options : Core.VerifyOptions) (program : Core.Program)
    (moreFns : Lambda.Factory Core.CoreLParams := Lambda.Factory.default) :
    Except Message (Core.Program × Statistics) :=
  _root_.Core.typeCheckAndBuildObligationProgram options program moreFns

/-! ### Transformation of Core programs

Transform passes are values of `Core.PipelinePhase`. Build them with the
smart constructors below (e.g., `Core.passLoopElim`, `Core.passInlineAll`),
and chain them with `Core.runTransforms`. -/

/-- Run a chain of pipeline phases on a Core program. All phases share a
    single `CoreTransformState`, so fresh variable counters accumulate across
    phases and cached analyses (e.g., call graphs) can be reused. Returns the
    transformed program together with the final transform state (statistics,
    cached analyses, etc.).

    Optional knobs:
    * `initState` — initial transform state. Use this to inject a pre-built
      `Lambda.Factory`.
    * `pipelineCtx` — when provided, each phase is wrapped in
      `withRepeatedPhasePure` for telemetry.
    * `keepAllFilesPrefix` — when provided, the program after each phase is
      written to `{prefix}.{n}.{phaseName}.core.st` (1-indexed). Creates the
      parent directory if needed. -/
def Core.runTransforms (p : Core.Program) (phases : List Core.PipelinePhase)
    (initState : Core.Transform.CoreTransformState := .emp)
    (pipelineCtx : Option Strata.Pipeline.PipelineContext := none)
    (keepAllFilesPrefix : Option String := none)
    : EIO Core.Transform.Err (Core.Program × Core.Transform.CoreTransformState) :=
  _root_.Core.runTransforms p phases initState pipelineCtx keepAllFilesPrefix

/-- Inline procedure calls. By default inlines every non-recursive call. -/
def Core.passInlineAll : Core.PipelinePhase :=
  Core.procedureInliningPipelinePhase {}

/-- Inline only the named procedures' call sites. -/
def Core.passInlineMatching (procs : List String) : Core.PipelinePhase :=
  Core.procedureInliningPipelinePhase
    { doInline := fun _caller callee _ => callee ∈ procs }

/-- Inline every procedure call except calls to the named procedures. -/
def Core.passInlineExcept (procs : List String) : Core.PipelinePhase :=
  Core.procedureInliningPipelinePhase
    { doInline := fun _caller callee _ => callee ∉ procs }

/-- Materialize each loop's invariant/measure verification conditions as
    explicit assert/assume statements (run before `passLoopElim`). -/
def Core.passInsertLoopInvariantAsserts : Core.PipelinePhase :=
  Core.insertLoopInvariantAssertsPipelinePhase

/-- Replace each loop with assertions/assumptions about its invariants. -/
def Core.passLoopElim : Core.PipelinePhase :=
  Core.loopElimPipelinePhase

/-- Replace each procedure call with assertions/assumptions about its contract. -/
def Core.passCallElim : Core.PipelinePhase :=
  Core.callElimPipelinePhase

/-- Keep only the named procedures and their transitive callees. -/
def Core.passFilterProcedures (procs : List String) : Core.PipelinePhase :=
  Core.filterProceduresPipelinePhase procs

/-- Remove axiom declarations that are irrelevant to the named functions
    (based on call graph analysis). -/
def Core.passRemoveIrrelevantAxioms (funcs : List String) : Core.PipelinePhase :=
  Core.irrelevantAxiomsPipelinePhase funcs

/-! ### Standard Core verification pipeline phases

The verification pipeline performs a sequence of program-to-program transforms
(`transformPipelinePhases`), the first of which decides what the rest assume
about the program they are handed. `coreAbstractedPhases` exposes only the
abstracted (model-validation) view used downstream.
-/

/-- The program-to-program transform phases applied before type checking.
    Shape assertion, inlining/loop-elim/call-elim/filtering, in the order
    required by the verification pipeline. See the underlying definition for
    ordering rationale. -/
def Core.transformPipelinePhases (options : Core.VerifyOptions := Core.VerifyOptions.default)
    : List Core.PipelinePhase :=
  _root_.Core.transformPipelinePhases options

/-- The full pipeline phases for program-to-program transforms, including
    type checking, symbolic evaluation, and common subexpression elim. -/
def Core.corePipelinePhases
    (options : Core.VerifyOptions := Core.VerifyOptions.default)
    (moreFns : @Lambda.Factory Core.CoreLParams := Lambda.Factory.default)
    : List Core.PipelinePhase :=
  _root_.Core.corePipelinePhases options moreFns

/-- The abstracted phases derived from the Core pipeline phases. -/
def Core.coreAbstractedPhases
    (options : Core.VerifyOptions := Core.VerifyOptions.default)
    (moreFns : @Lambda.Factory Core.CoreLParams := Lambda.Factory.default)
    : List Core.AbstractedPhase :=
  _root_.Core.coreAbstractedPhases options moreFns

/-- The name a phase is known by: the camelCase name shown in
    `--keep-all-files` output, in the dependency table, and accepted by
    `--phases`. -/
def Core.phaseName (p : Core.PipelinePhase) : String := p.phase.name

/-- Validate an arbitrary phase list, both that its phases compose and that
    what they establish covers what the verification back end requires of the
    program they produce. On failure, an explanatory diagnostic; on success, a
    `ValidatedPipeline` the type of which carries the composition proof, so an
    unchecked order cannot reach `verifyProgram`. -/
def Core.validatePipeline (phases : List Core.PipelinePhase) :
    Except String (Core.ValidatedPipeline Core.ProgramFactSet.empty) :=
  Core.ValidatedPipeline.ofListDelivering
    "the verification back end" Core.backEndRequiredFacts phases

/-- Like `validatePipeline`, but validates against facts `entryFacts` assumed to
    hold on the input program. The result is indexed by `entryFacts`, so
    `verifyProgram` will require a proof that they hold of the program verified.
    This is the API-only path a Lean front end uses to skip phases whose facts
    it can prove of its own output. -/
def Core.validatePipelineFrom (entryFacts : Core.ProgramFactSet)
    (phases : List Core.PipelinePhase) :
    Except String (Core.ValidatedPipeline entryFacts) :=
  Core.ValidatedPipeline.ofListFromDelivering
    entryFacts "the verification back end" Core.backEndRequiredFacts phases

/-- `phases` with `extra` inserted directly after the phase named `after`.
    Anchoring by name rather than by index is what lets a caller place a phase
    relative to one whose facts it needs — procedure inlining after
    `assertNoCFGBodies`, which establishes the structured bodies inlining
    requires. An anchor that is not in the list is an error rather than a
    silent placement, since the position is the point. -/
def Core.splicePhasesAfter (after : String) (extra : List Core.PipelinePhase)
    (phases : List Core.PipelinePhase) : Except String (List Core.PipelinePhase) :=
  match phases.findIdx? (fun p => Core.phaseName p == after) with
  | some i => .ok (phases.take (i + 1) ++ extra ++ phases.drop (i + 1))
  | none => .error s!"Cannot splice after phase '{after}': no phase of that name \
                      is in the list."

/-! ### Resolving a phase list from names

A command that lets a user name phases needs to turn those names into phases,
resolving `assert<Fact>` forms, and to render what is available. These helpers do
that, so a command and the API agree on what a name means.

The flags themselves are deliberately not declared here. Whether phase selection
belongs to `verify` alone or to a shared set of commands is not settled, so
nothing advertises the flags yet; the rendered text names `--phases` and
`--display-phases` as the intended spelling for whoever wires them up. -/

/-- The name of the `assert` phase for a fact: `assert` followed by the fact's
    name with its first letter capitalized, so `noCFGBodies` gives
    `assertNoCFGBodies`, which is what the default pipeline's first phase is
    already called. -/
def Core.assertPhaseName (f : Core.ProgramFact) : String :=
  "assert" ++ (match f.name.toList with
               | [] => ""
               | c :: rest => String.ofList (c.toUpper :: rest))

/-- The `assert<Fact>` phase a name denotes, if any: for a fact `F` with an
    executable check, `assertPhaseName F` is a phase that checks `F` and passes
    the program through. A fact without a check (`typeAnnotated`) has no assert
    form, so `none`. -/
def Core.assertPhaseFor (phaseName : String) : Option Core.PipelinePhase :=
  (Core.ProgramFact.all.find? fun f => phaseName == Core.assertPhaseName f).bind
    fun f =>
      if h : f.check?.isSome = true then
        some (Core.assertFactPhase phaseName f
                s!"❌ Expected {f.name}, but the program does not satisfy it." h)
      else none

/-- Resolve a list of phase names against the phases `available`, also accepting
    `assert<Fact>` forms. A caller decides what is nameable: the option-derived
    pipeline, plus any phase outside it that it is willing to run. An unknown name
    is a user error. -/
def Core.resolvePhases (available : List Core.PipelinePhase) (requested : List String) :
    Except String (List Core.PipelinePhase) :=
  requested.mapM fun nm =>
    match available.find? (fun p => Core.phaseName p == nm) with
    | some p => .ok p
    | none =>
      match Core.assertPhaseFor nm with
      | some p => .ok p
      | none => .error s!"Unknown phase name '{nm}'. \
                          Use --display-phases to see the available phases."

/-- The text describing the available phases: the default order as a pasteable
    `--phases` argument, and the phases available but not in that order. -/
def Core.displayPhasesText (defaultPhases : List Core.PipelinePhase)
    (extras : List Core.PipelinePhase := []) : String :=
  let names := ",".intercalate (defaultPhases.map Core.phaseName)
  let base :=
    s!"To run the phases in the default order:\n\n  --phases {names}\n\n\
       You can change this order. Give it back to --phases with no input file and\n\
       Strata reports whether it composes without verifying anything.\n\
       To see the declared dependencies between phases, use --display-phase-contracts."
  match extras.map Core.phaseName with
  | [] => base
  | extraNames =>
    base ++ "\n\nAvailable, not in the default order:\n\n"
      ++ "\n".intercalate (extraNames.map (fun n => s!"  {n}"))

/-- Front-end phase: any translation from a source language to Core may
    introduce over-approximations. Until front-ends can validate models or
    determine that an assertion is unaffected, all sat results are converted
    to unknown. -/
def frontEndPhase : Core.AbstractedPhase where
  name := "FrontEnd"
  getValidation _ := .modelToValidate (fun _ => /- TODO -/ false)

/-! ### Analysis of Core programs -/

/--
Verify a Core program, including any external solver invocation that is
necessary.

The basic call form passes just `program` and `options`.

Verifying only some procedures requires two `filterProcedures` phases at specific
positions — one before the entry assertion, one after precondition lifting, which
targets the procedures generated from those named. `options.proceduresToVerify`
puts those phases into the phase list, so a caller supplying its own `pipeline`
gets the same filtering by building that pipeline from the options it verifies
with.
-/
def Core.verifyProgram
    (program : Core.Program)
    (options : Core.VerifyOptions := .default)
    (moreFns : @Lambda.Factory Core.CoreLParams := Lambda.Factory.default)
    (externalPhases : List Core.AbstractedPhase := [])
    (entryFacts : Core.ProgramFactSet := Core.ProgramFactSet.empty)
    (pipeline : Option (Core.ValidatedPipeline entryFacts) := none)
    (entryFactsHold : entryFacts.holds program :=
      by exact _root_.Core.ProgramFactSet.empty_holds _)
    (mkDischarge : Core.MkDischargeFn := Core.mkDischargeFn)
    (pipelineCtx : Option Pipeline.PipelineContext := none)
    (fileMap : Option Lean.FileMap := none)
    : EIO String Core.VCResults := do
  let runVerification (tempDir : System.FilePath) : IO Core.VCResults :=
    EIO.toIO (fun dm => IO.Error.userError (toString (dm.format fileMap)))
      (Core.verify program tempDir options moreFns externalPhases
        (entryFacts := entryFacts) (pipeline := pipeline) (entryFactsHold := entryFactsHold)
        (mkDischarge := mkDischarge)
        (pipelineCtx := pipelineCtx))
  let ioAction := match options.vcDirectory with
    | .some vcDir => IO.FS.createDirAll vcDir *> runVerification vcDir
    | .none => IO.FS.withTempDir runVerification
  IO.toEIO (fun e => s!"{e}") ioAction

/--
Convenience wrapper that translates a generic `Strata.Program` to `Core.Program`
and verifies it. Equivalent to `strataProgramToCore` followed by `verifyProgram`,
with DDM translation errors panicking and verifier diagnostics formatted using
`ictx.fileMap`.
-/
def Core.verify
    (env : StrataDDM.Program)
    (ictx : Lean.Parser.InputContext := Inhabited.default)
    (options : Core.VerifyOptions := .default)
    (moreFns : @Lambda.Factory Core.CoreLParams := Lambda.Factory.default)
    (externalPhases : List Core.AbstractedPhase := [])
    (pipeline : Option (Core.ValidatedPipeline Core.ProgramFactSet.empty) := none)
    (mkDischarge : Core.MkDischargeFn := Core.mkDischargeFn)
    (pipelineCtx : Option Pipeline.PipelineContext := none)
    : IO Core.VCResults := do
  -- Run the translation within a pure phase so that we can capture the timing
  -- properly, and unwrap the error outside of it.
  let translated ← show BaseIO _ from match pipelineCtx with
    | some pctx => pctx.withPhasePure "ddmToCore" fun _ => strataProgramToCore env ictx
    | none => pure (strataProgramToCore env ictx)
  let program ← match translated with
    | .ok p => pure p
    | .error msg => throw (IO.userError msg)
  -- The caller-supplied `pipeline` (when present) assumes nothing at entry: a
  -- command line cannot prove entry facts, so this path is always empty-indexed.
  Core.verifyProgram program options moreFns
    (externalPhases := externalPhases)
    (pipeline := pipeline)
    (mkDischarge := mkDischarge)
    (pipelineCtx := pipelineCtx)
    (fileMap := some ictx.fileMap)
    |>.toIO (fun e => IO.Error.userError e)

/-- Convert a `Core.VCResult` to a `Diagnostic` if it should surface as a
diagnostic, looking up the file map for the obligation's source range. Returns
`none` for results that should not be surfaced (e.g. successful obligations). -/
def Core.VCResult.toDiagnostic (files : Map Strata.Uri Lean.FileMap) (vcr : Core.VCResult)
    (phases : List Core.AbstractedPhase := []) : Option Diagnostic := do
  let modelOption := toMessage vcr phases
  modelOption.map (fun dm => dm.toDiagnostic files)

end Strata

end -- public section
