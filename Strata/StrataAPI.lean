/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.DDMAPI
public import Strata.Languages.Core.Verifier
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
AST. Usually useful as a step before serialization. TODO: we can't yet implement
this, but will be able to once we use DDM-generated translation between the
generic and Strata-specific ASTs.
-/
noncomputable opaque coreToGeneric : Core.Program → Strata.Program

/--
Translate a program in the generic AST for Strata into the dialect-specific AST
for Core. This can fail with an error message if the input is not a
well-structured instance of the Core dialect.
-/
def genericToCore (p : Strata.Program) : Except String Core.Program :=
  let (program, errors) := Core.getProgram p
  if errors.isEmpty then
    .ok program
  else
    .error s!"Core DDM translation errors:\n{String.intercalate "\n" errors.toList}"

/-! ### Transformation of Core programs

Transform passes are opaque values built with smart constructors. Clients
chain them with `Core.runTransforms`, or invoke a single pass via the
per-pass entry points (`Core.inlineAllProcedures`, `Core.loopElimUsingContract`,
…). -/

/-- A single Core program transform pass.

This type is intentionally opaque: build values with the smart constructors
below (e.g., `Core.passLoopElim`, `Core.passInlineAll`). Clients should not
pattern-match or inspect fields. -/
structure Core.TransformPass where
  ofTransformPass ::
  /-- Internal: applies the pass inside a running `CoreTransformM`. -/
  apply : Core.Program → Core.Transform.CoreTransformM Core.Program

/-- Run a chain of transform passes on a Core program. All passes share a
    single `CoreTransformState`, so fresh variable counters accumulate across
    passes and cached analyses (e.g., call graphs) can be reused. -/
def Core.runTransforms (p : Core.Program) (passes : List Core.TransformPass)
    : Except Core.Transform.Err Core.Program :=
  Core.Transform.run p (fun prog => do
    let mut program := prog
    for pass in passes do
      program ← pass.apply program
    return program)

/-- Inline procedure calls. By default inlines every non-recursive call. -/
def Core.passInlineAll : Core.TransformPass :=
  { apply := fun program => do
      let (_, prog) ← (Core.procedureInliningPipelinePhase {}).transform program
      return prog }

/-- Inline only the named procedures' call sites. -/
def Core.passInlineMatching (procs : List String) : Core.TransformPass :=
  { apply := fun program => do
      let opts : Core.InlineTransformOptions :=
        { doInline := fun _caller callee _ => callee ∈ procs }
      let (_, prog) ← (Core.procedureInliningPipelinePhase opts).transform program
      return prog }

/-- Inline every procedure call except calls to the named procedures. -/
def Core.passInlineExcept (procs : List String) : Core.TransformPass :=
  { apply := fun program => do
      let opts : Core.InlineTransformOptions :=
        { doInline := fun _caller callee _ => callee ∉ procs }
      let (_, prog) ← (Core.procedureInliningPipelinePhase opts).transform program
      return prog }

/-- Replace each loop with assertions/assumptions about its invariants. -/
def Core.passLoopElim : Core.TransformPass :=
  { apply := fun program => pure (Core.loopElim program).fst }

/-- Replace each procedure call with assertions/assumptions about its contract. -/
def Core.passCallElim : Core.TransformPass :=
  { apply := fun program => do
      let (_, prog) ← Core.Transform.runProgram coreCallElimCmd program
      return prog }

/-- Keep only the named procedures and their transitive callees. -/
def Core.passFilterProcedures (procs : List String) : Core.TransformPass :=
  { apply := fun program => Core.FilterProcedures.run program procs }

/-- Remove axiom declarations that are irrelevant to the named functions
    (based on call graph analysis). -/
def Core.passRemoveIrrelevantAxioms (funcs : List String) : Core.TransformPass :=
  { apply := fun program => Core.IrrelevantAxioms.run program funcs }

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
Power-user entry point for verifying a Core program. Exposes Lambda
factories, external/prefix pipeline phases, a custom solver, a custom
discharge function, and a shared `PipelineContext`. Most clients should
prefer the basic `Core.verifyProgram`.
-/
def Core.verifyProgramAdvanced
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

/--
Verify a Core program, including any external solver invocation that is
necessary.

This is the basic entry point: it takes the program and the user-facing
verification options. Power users who need to plug in additional pipeline
phases, a custom solver, a custom discharge function, or a shared
`PipelineContext` should use `Core.verifyProgramAdvanced`.
-/
def Core.verifyProgram
    (program : Core.Program)
    (options : Core.VerifyOptions := .default)
    : EIO String Core.VCResults :=
  Core.verifyProgramAdvanced program options

end Strata

end -- public section
