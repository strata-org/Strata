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

/-- Type check `program` against `factory` (`none`: the built-in functions) extended by
    `moreFns`. A supplied factory is checked first; the built-in one is not. Each function of
    `moreFns` is then checked against the factory and the functions before it. The type names in
    scope are collected once into a set, which grows with the signatures of the added
    functions. -/
def typeCheck (options : VerifyOptions) (program : Program)
    (factory : Option (Lambda.Factory CoreLParams) := none)
    (moreFns : Lambda.Factory CoreLParams := Lambda.Factory.default) :
    Except Message Program := do
  let T := Lambda.TEnv.default
  let C := { initTyContext with functions := factory.getD Core.Factory }
  let S := (scopeTyNameThunk C T).get
  let checked := match factory with
    | some _ => Factory.typeCheckIn (Thunk.pure S) C T
    | none => .ok T
  match checked with
  | .error k =>
    -- TODO: Message for functions defined in Factory?
    throw (Message.fromFormat k)
  | .ok T =>
    let (C, S) ← Factory.checkThenAddIn S C T moreFns.toArray
    let (program, _) ← Program.typeCheckIn S C T program
    if options.verbose >= .normal then dbg_trace f!"[Strata.Core] Type checking succeeded.\n"
    return program

/-- Type-checking pipeline phase: runs `Core.typeCheck` on the program against
    `factory` (`none`: the built-in functions) and the extra functions `moreFns`. Every call of
    its output is well formed and every expression is annotated. Its output records the prefixes
    of its internal names and of the internal names of the functions it is checked against. -/
def typeCheckPipelinePhase
    (options : VerifyOptions := VerifyOptions.default)
    (factory : Option (@Lambda.Factory CoreLParams) := none)
    (moreFns : @Lambda.Factory CoreLParams := Lambda.Factory.default) : PipelinePhase :=
  -- Type checking annotates expressions and leaves every statement where it
  -- is, so it carries all facts across. Annotation does not change which
  -- constructor an expression is, so a redex-free program stays redex-free.
  -- It rejects an `exit` whose label names no enclosing block, so every body of
  -- its output has its exits covered.
  modelPreservingPipelinePhase "typeCheck"
    (establishes := factSet![.wellFormedCalls, .typeAnnotated, .exitsCovered])
    (preserves := factSet![.noCFGBodies, .noCalls, .noLoops, .noLoopInvariants,
                         .noLoopMeasures, .staticSingleAssignment, .noBetaRedexes,
                         .noPrecondsFromFuncs, .noNondetGuards, .noProcedureContracts,
                         .noPolymorphicProcedures,
                         .noPolymorphicFunctions, .noInits, .noCFGCycles])
    fun prog => do
      match Core.typeCheck options prog factory moreFns with
      | .ok prog' =>
        -- The input's recorded prefixes are kept.
        let fns := (factory.getD Core.Factory).toArray.toList ++ moreFns.toArray.toList
        let fnPrefixes := (fns.map (·.name.name)).filter Strata.Name.isInternal
          |>.map Strata.Name.internalPrefixOf
        return (true, { prog' with usedIdentPrefixes := prog.usedIdentPrefixes }
          |>.withCollectedIdentPrefixes |>.addIdentPrefixes fnPrefixes)
      | .error err => throw { err with message := s!"❌ Type checking error.\n{err.message}" }

end -- public section
end Core
