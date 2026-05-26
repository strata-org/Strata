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
or with the per-pass entry points (`Core.inlineAllProcedures`,
`Core.loopElimUsingContract`, …). Chain phases with `Core.runTransforms`. -/

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

/-- Inline every non-recursive procedure call. -/
def Core.inlineAllProcedures (p : Core.Program)
    : Except Core.Transform.Err Core.Program :=
  Core.runTransforms p [Core.passInlineAll]

/-- Inline only the named procedures' call sites. -/
def Core.inlineMatchingProcedures (p : Core.Program) (procs : List String)
    : Except Core.Transform.Err Core.Program :=
  Core.runTransforms p [Core.passInlineMatching procs]

/-- Transform a Core program to replace each loop with assertions/assumptions
    about its invariants. -/
def Core.loopElimUsingContract (p : Core.Program) : Core.Program :=
  (Core.loopElim p).fst

/-- Transform a Core program to replace each procedure call with
    assertions/assumptions about its contract. -/
def Core.callElimUsingContract (p : Core.Program)
    : Except Core.Transform.Err Core.Program :=
  Core.runTransforms p [Core.passCallElim]

/-- Transform a Core program to keep only the named procedures and their
    transitive callees, removing everything else. -/
def Core.filterProcedures (p : Core.Program) (targetProcs : List String)
    : Except Core.Transform.Err Core.Program :=
  Core.runTransforms p [Core.passFilterProcedures targetProcs]

/-- Transform a Core program to remove axiom declarations that are irrelevant
    to the named functions (based on call graph analysis). -/
def Core.removeIrrelevantAxioms (p : Core.Program) (functions : List String)
    : Except Core.Transform.Err Core.Program :=
  Core.runTransforms p [Core.passRemoveIrrelevantAxioms functions]

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
    (solver : Option Core.CoreSMTSolver := none)
    (mkDischarge : Core.MkDischargeFn := Core.mkDischargeFn)
    (pipelineCtx : Option Pipeline.PipelineContext := none)
    : EIO String Core.VCResults := do
  let runVerification (tempDir : System.FilePath) : IO Core.VCResults :=
    EIO.toIO (IO.Error.userError ∘ toString)
      (Core.verify program tempDir proceduresToVerify options moreFns externalPhases prefixPhases
        (keepAllFilesPrefix := keepAllFilesPrefix)
        (solver := solver)
        (mkDischarge := mkDischarge)
        (pipelineCtx := pipelineCtx))
  let ioAction := match options.vcDirectory with
    | .some vcDir => IO.FS.createDirAll vcDir *> runVerification vcDir
    | .none => IO.FS.withTempDir runVerification
  IO.toEIO (fun e => s!"{e}") ioAction

end Strata

end -- public section
