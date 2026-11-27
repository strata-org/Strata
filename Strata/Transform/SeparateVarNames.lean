/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Core.PipelinePhase
public import Strata.Languages.Core.ProgramFactSet
public import Strata.Languages.Core.ShadowingBinders

/-! # Separating variable names from function names

A variable may have the name of a function or constant, which it shadows. Obligation
extraction and the SMT encoding put variables and functions in one namespace, so the
verification back end runs `separateVarNamesPipelinePhase` last, before it extracts
obligations: it renames each such variable apart (`Program.renameShadowingBinders`) and
establishes `varsNotFunctions`.

Key definition: `Core.separateVarNamesPipelinePhase`. -/

namespace Core

public section

/-- Pipeline phase that renames apart each variable named like a function or constant of the
    program or of the factory (`Program.renameShadowingBinders`), establishing
    `varsNotFunctions`. Its contract: it renames only such variables, each consistently
    throughout its declaration (with its `old` form) to a name unused by the program, the
    declaration and the factory, and changes nothing else. So it is intended to preserve every
    verdict, and every fact below: each is about the shape of the program (its declarations,
    statements, calls, loops, contracts, type parameters and annotations) and holds of a program
    exactly when it holds of the program with its variables renamed injectively.

    TODO: prove `PhasePreservesDeductiveVerification` for this phase, which `ValidConfig` needs
    of every phase of the default order; until then its contract is declared, not proved, and
    the injectivity of the renaming is checked by a property test of
    `ShadowingBinders.freshRenaming`. -/
def separateVarNamesPipelinePhase : PipelinePhase :=
  modelPreservingPipelinePhase "separateVarNames"
    (establishes := factSet![.varsNotFunctions])
    (preserves := factSet![.wellFormedCalls, .noCFGBodies, .noCalls, .noLoops, .noLoopInvariants,
      .noLoopMeasures, .uniqueInits, .loopBodyNoInits, .staticSingleAssignment, .noBetaRedexes,
      .noLambdas, .noPrecondsFromFuncs, .noNondetGuards, .hasObligationForm, .noProcedureContracts,
      .noPolymorphicProcedures, .noPolymorphicFunctions, .typeAnnotated, .noInits, .treeForm,
      .exitsCovered, .armsHaveObligations, .noCFGCycles])
    fun prog => do
      let factory ← Core.Transform.getFactory
      return match prog.renameShadowingBinders (fun n => decide (n ∈ factory))
          factory.toArray.size with
        | some prog' => (true, prog')
        | none => (false, prog)

end -- public section

end Core
