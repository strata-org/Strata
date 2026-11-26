/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Transform.RecursiveFunctionAxiomsFactCorrect

/-! # The `recursiveAxioms` pipeline phase

This file only assembles the phase: the transform is `RecursiveAxioms.run`, and its contract is
proved in `RecursiveFunctionAxiomsFactCorrect`, which imports the transform. -/

public section

/-- Recursive-function axioms pipeline phase.

    Model-preserving: each axiom is an equation the function's definition satisfies, so
    it holds in every model of the program and removes none. It changes only function
    declarations, adding axioms, so it preserves every fact about procedure bodies,
    contracts and polymorphism. It does not claim `noBetaRedexes`, which `betaReduce`
    establishes after it.

    Its contract is proved, but for `typeAnnotated` (`Core.recursiveAxioms_keeps`). -/
def Core.recursiveAxiomsPhase (options : Core.VerifyOptions := Core.VerifyOptions.default) :
    Core.PipelinePhase where
  transform := Core.RecursiveAxioms.run options
  phase.name := "recursiveAxioms"
  requires := factSet![.typeAnnotated]
  preserves := factSet![.noCFGBodies, .noCalls, .noLoops, .noLoopInvariants,
                       .noLoopMeasures, .staticSingleAssignment,
                       .noPrecondsFromFuncs, .noNondetGuards, .hasObligationForm,
                       .noProcedureContracts, .noPolymorphicProcedures,
                       .noPolymorphicFunctions, .typeAnnotated, .noInits, .treeForm,
                       .exitsCovered, .armsHaveObligations]
  -- `typeAnnotated`: each generated axiom is a function's body applied to a constructor and
  -- folded by the partial evaluator, so its proof needs the evaluator to keep annotations,
  -- which nothing proves yet. Believed true: the axioms are built from annotated bodies and
  -- constructors, and the encoder, which rejects an unannotated operator, accepts them on
  -- every program the tests run.
  unproved := factSet![.typeAnnotated]
  preserves_ok := by
    intro f hf hu _ _ _ hp _ _ _ hrun
    refine Core.recursiveAxioms_keeps ?_ hrun hp
    revert hf hu
    cases f <;> decide

end -- public section
