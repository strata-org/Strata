/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.DDM
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

/-! ### Transformation between generic and dialect-specific representation -/

/--
Translate a program in the dialect-specific AST for Core into the generic Strata
AST. Usually useful as a step before serialization. Conversion goes through the
Core CST built by `Strata.programToCST`, then projects each `Command` back to
its underlying `Operation` via the DDM-generated `toAst`.
-/
def coreToStrataProgram (p : Core.Program) : Strata.Program :=
  let (_finalCtx, cmds) := Strata.programToCST (M := SourceRange) p
  let ops := cmds.map (·.toAst) |>.toArray
  Strata.Program.create Strata.Core_map "Core" ops

/--
Translate a program in the generic AST for Strata into the dialect-specific AST
for Core. This can fail with an error message if the input is not a
well-structured instance of the Core dialect.
-/
def strataProgramToCore (p : Strata.Program) : Except String Core.Program :=
  let (program, errors) := Core.getProgram p
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
    phases and cached analyses (e.g., call graphs) can be reused. -/
def Core.runTransforms (p : Core.Program) (phases : List Core.PipelinePhase)
    : Except Core.Transform.Err Core.Program :=
  Core.Transform.run p (fun prog => do
    let mut program := prog
    for phase in phases do
      let (_, prog') ← phase.transform program
      program := prog'
    return program)

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

/-! ### Analysis of Core programs -/

/--
Verify a Core program, including any external solver invocation that is
necessary.

The basic call form passes just `program` and `options`. Power users may
plug in additional Lambda factories, external/prefix pipeline phases, a
custom solver, a custom discharge function, or a shared `PipelineContext`
via the optional named arguments.
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
    : EIO String Core.VCResults := do
  let runVerification (tempDir : System.FilePath) : IO Core.VCResults :=
    EIO.toIO (IO.Error.userError ∘ toString)
      (Core.verify program tempDir proceduresToVerify options moreFns externalPhases prefixPhases
        (keepAllFilesPrefix := keepAllFilesPrefix)
        (mkDischarge := mkDischarge)
        (pipelineCtx := pipelineCtx))
  let ioAction := match options.vcDirectory with
    | .some vcDir => IO.FS.createDirAll vcDir *> runVerification vcDir
    | .none => IO.FS.withTempDir runVerification
  IO.toEIO (fun e => s!"{e}") ioAction

end Strata

end -- public section
