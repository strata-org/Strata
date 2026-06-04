/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import StrataDDM
public import Strata.Languages.Core.Verifier
public import Strata.Languages.Core.PipelinePhase
public import Strata.Transform.ProcedureInlining
import Strata.Transform.CallElim
import Strata.Transform.LoopElim
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
`DiagnosticModel` describing the error on failure.
-/
def Core.typeCheck (options : Core.VerifyOptions) (program : Core.Program)
    (moreFns : Lambda.Factory Core.CoreLParams := Lambda.Factory.default) :
    Except DiagnosticModel Core.Program :=
  _root_.Core.typeCheck options program moreFns

/--
Type-check a Core program, then run symbolic evaluation. Returns the list of
post-evaluation environments and accumulated statistics.
-/
def Core.typeCheckAndEval (options : Core.VerifyOptions) (program : Core.Program)
    (moreFns : Lambda.Factory Core.CoreLParams := Lambda.Factory.default) :
    Except DiagnosticModel ((List Core.Env) × Statistics) :=
  _root_.Core.typeCheckAndEval options program moreFns

/--
Type-check a Core program, then build the proof-obligation program suitable for
downstream phases (ANF encoding, SMT encoding).
-/
def Core.typeCheckAndBuildObligationProgram
    (options : Core.VerifyOptions) (program : Core.Program)
    (moreFns : Lambda.Factory Core.CoreLParams := Lambda.Factory.default) :
    Except DiagnosticModel (Core.Program × Statistics) :=
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
(`transformPipelinePhases`). `coreAbstractedPhases` exposes only the
abstracted (model-validation) view used downstream.
-/

/-- The program-to-program transform phases applied before type checking.
    Inlining/loop-elim/call-elim/filtering, in the order required by the
    verification pipeline. See the underlying definition for ordering rationale. -/
def Core.transformPipelinePhases (procs : Option (List String) := none)
    : List Core.PipelinePhase :=
  _root_.Core.transformPipelinePhases procs

/-- The full pipeline phases for program-to-program transforms, including
    type checking, symbolic evaluation, and ANF encoding. -/
def Core.corePipelinePhases (procs : Option (List String) := none)
    (options : Core.VerifyOptions := Core.VerifyOptions.default)
    (moreFns : @Lambda.Factory Core.CoreLParams := Lambda.Factory.default)
    : List Core.PipelinePhase :=
  _root_.Core.corePipelinePhases procs options moreFns

/-- The abstracted phases derived from the Core pipeline phases. -/
def Core.coreAbstractedPhases (procs : Option (List String) := none)
    (options : Core.VerifyOptions := Core.VerifyOptions.default)
    (moreFns : @Lambda.Factory Core.CoreLParams := Lambda.Factory.default)
    : List Core.AbstractedPhase :=
  _root_.Core.coreAbstractedPhases procs options moreFns

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
-/
def Core.verifyProgram
    (program : Core.Program)
    (options : Core.VerifyOptions := .default)
    (moreFns : @Lambda.Factory Core.CoreLParams := Lambda.Factory.default)
    (proceduresToVerify : Option (List String) := none)
    (externalPhases : List Core.AbstractedPhase := [])
    (prefixPhases : List Core.PipelinePhase := [])
    (keepAllFilesPrefix : Option String := none)
    (mkDischarge : Core.MkDischargeFn := Core.mkDischargeFn)
    (pipelineCtx : Option Pipeline.PipelineContext := none)
    (fileMap : Option Lean.FileMap := none)
    : EIO String Core.VCResults := do
  let runVerification (tempDir : System.FilePath) : IO Core.VCResults :=
    EIO.toIO (fun dm => IO.Error.userError (toString (dm.format fileMap)))
      (Core.verify program tempDir proceduresToVerify options moreFns externalPhases prefixPhases
        (keepAllFilesPrefix := keepAllFilesPrefix)
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
    (proceduresToVerify : Option (List String) := none)
    (options : Core.VerifyOptions := .default)
    (moreFns : @Lambda.Factory Core.CoreLParams := Lambda.Factory.default)
    (externalPhases : List Core.AbstractedPhase := [])
    (keepAllFilesPrefix : Option String := none)
    (mkDischarge : Core.MkDischargeFn := Core.mkDischargeFn)
    : IO Core.VCResults := do
  let program ← match strataProgramToCore env ictx with
    | .ok p => pure p
    | .error msg => throw (IO.userError msg)
  Core.verifyProgram program options moreFns
    (proceduresToVerify := proceduresToVerify)
    (externalPhases := externalPhases)
    (keepAllFilesPrefix := keepAllFilesPrefix)
    (mkDischarge := mkDischarge)
    (fileMap := some ictx.fileMap)
    |>.toIO (fun e => IO.Error.userError e)

/-- Convert a `Core.VCResult` to a `Diagnostic` if it should surface as a
diagnostic, looking up the file map for the obligation's source range. Returns
`none` for results that should not be surfaced (e.g. successful obligations). -/
def Core.VCResult.toDiagnostic (files : Map Strata.Uri Lean.FileMap) (vcr : Core.VCResult)
    (phases : List Core.AbstractedPhase := []) : Option Diagnostic := do
  let modelOption := toDiagnosticModel vcr phases
  modelOption.map (fun dm => dm.toDiagnostic files)

end Strata

end -- public section
