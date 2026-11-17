/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Core.PipelinePhase
public import Strata.Languages.Core.Options
public import Strata.Languages.Core.ProgramType
public import Strata.Transform.GenOpaqueTypeParams

/-! # Type checking a Core program

`Core.typeCheck` type-checks a Core program against a factory, annotating its expressions, and
`Core.typeCheckPipelinePhase` is the pipeline phase that runs it.

Key definitions: `Core.typeCheck`, `Core.typeCheckPipelinePhase`. -/

namespace Core
open Imperative Lambda
open Strata

public section

def typeCheck (options : VerifyOptions) (program : Program)
    (factory : Lambda.Factory CoreLParams := Core.Factory) :
    Except Message Program := do
  let T := Lambda.TEnv.default
  -- Callers past `MonomorphizeFunctions` pass the transformed factory (poly
  -- Factory originals dropped, specialized copies added) rather than the default.
  let C := { Lambda.LContext.default with
                functions := factory,
                knownTypes := Core.KnownTypes }
  match Factory.typeCheck C T with
  | .error k =>
    -- TODO: Message for functions defined in Factory?
    throw (Message.fromFormat k)
  | .ok T =>
    let (program, _T) ← Program.typeCheck C T program
    GenOpaqueTypeParams.checkClosedLemmaNames program
    let program := GenOpaqueTypeParams.closeLemmaTypeVars program
    -- dbg_trace f!"[Strata.Core] Annotated program:\n{program}"
    if options.verbose >= .normal then dbg_trace f!"[Strata.Core] Type checking succeeded.\n"
    return program

/-- Type-checking pipeline phase: runs `Core.typeCheck` on the program against
    `factory` (the full function set to type-check against; defaults to the
    pristine `Core.Factory`). -/
def typeCheckPipelinePhase
    (options : VerifyOptions := VerifyOptions.default)
    (factory : @Lambda.Factory CoreLParams := Core.Factory) : PipelinePhase :=
  -- Type checking annotates expressions and leaves every statement where it
  -- is, so it carries all facts across. Annotation does not change which
  -- constructor an expression is, so a redex-free program stays redex-free.
  -- It rejects an `exit` whose label names no enclosing block, so every body of
  -- its output has its exits covered.
  modelPreservingPipelinePhase "typeCheck"
    (establishes := factSet![.typeAnnotated, .exitsCovered])
    (preserves := factSet![.noCFGBodies, .noCalls, .noLoops, .noLoopInvariants,
                         .noLoopMeasures, .staticSingleAssignment, .noBetaRedexes,
                         .noPrecondsFromFuncs, .noNondetGuards, .noProcedureContracts,
                         .noPolymorphicProcedures,
                         .noPolymorphicFunctions, .noInits])
    fun prog => do
      match Core.typeCheck options prog factory with
      | .ok prog' => return (true, prog')
      | .error err => throw { err with message := s!"❌ Type checking error.\n{err.message}" }

end -- public section

end Core
