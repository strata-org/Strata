/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.DDMAPI
import Strata.Transform.CallElim
import Strata.Transform.LoopElim
public import Strata.Transform.ProcedureInlining
import Strata.Transform.FilterProcedures
public import Strata.Languages.Core.Verifier

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

/-! ### Transformation of Core programs -/

/-- A single named transform pass with its arguments. -/
inductive Core.TransformPass where
  | inlineProcedures (opts : Core.InlineTransformOptions := {})
  | loopElim
  | callElim
  | filterProcedures (procs : List String)
  | removeIrrelevantAxioms (funcs : List String)

/-- Apply a single pass inside a running `CoreTransformM` context. -/
private def Core.applyPass (program : Core.Program) (pass : Core.TransformPass)
    : Core.Transform.CoreTransformM Core.Program := do
  match pass with
  | .inlineProcedures opts =>
    let (_, prog) ← (Core.procedureInliningPipelinePhase opts).transform program
    return prog
  | .loopElim =>
    pure (Core.loopElim program).fst
  | .callElim =>
    let (_, prog) ← Core.Transform.runProgram coreCallElimCmd program
    return prog
  | .filterProcedures procs =>
    Core.FilterProcedures.run program procs
  | .removeIrrelevantAxioms funcs =>
    Core.IrrelevantAxioms.run program funcs

/-- Run a chain of transform passes on a Core program.  All passes share a
    single `CoreTransformState`, so fresh variable counters accumulate across
    passes and cached analyses (e.g., call graphs) can be reused. -/
def Core.runTransforms (p : Core.Program) (passes : List Core.TransformPass)
    : Except Core.Transform.Err Core.Program :=
  Core.Transform.run p (fun prog => do
    let mut program := prog
    for pass in passes do
      program ← Core.applyPass program pass
    return program)

/--
Transform a Core program to inline some or all procedure calls.
-/
def Core.inlineProcedures (p : Core.Program) (opts : Core.InlineTransformOptions)
    : Except Core.Transform.Err Core.Program :=
  Core.runTransforms p [.inlineProcedures opts]

/--
Transform a Core program to replace each loop with assertions and assumptions about
its invariants.
-/
def Core.loopElimUsingContract (p : Core.Program) : Core.Program :=
  (Core.loopElim p).fst

/--
Transform a Core program to replace each procedure call with assertions and
assumptions about its contract.
-/
def Core.callElimUsingContract (p : Core.Program) : Except Core.Transform.Err Core.Program :=
  Core.runTransforms p [.callElim]

/--
Transform a Core program to keep only the named procedures and their
transitive callees, removing everything else.
-/
def Core.filterProcedures (p : Core.Program) (targetProcs : List String)
    : Except Core.Transform.Err Core.Program :=
  Core.runTransforms p [.filterProcedures targetProcs]

/--
Transform a Core program to remove axiom declarations that are irrelevant
to the named functions (based on call graph analysis).
-/
def Core.removeIrrelevantAxioms (p : Core.Program) (functions : List String)
    : Except Core.Transform.Err Core.Program :=
  Core.runTransforms p [.removeIrrelevantAxioms functions]

/-! ### Analysis of Core programs -/

/--
Verify a Core program, including any external solver invocation
that is necessary.
-/
def Core.verifyProgram
    (program : Core.Program)
    (options : Core.VerifyOptions)
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
