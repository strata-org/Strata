/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Transform.IrrelevantAxiomsFactCorrect

/-! # The `removeIrrelevantAxioms` pipeline phase

This file only assembles the phase: its contract is proved
from `IrrelevantAxiomsFactCorrect`, which imports the transform. -/

namespace Core

public section

/-- Pipeline phase that removes axiom declarations irrelevant to the named
    functions. The transform only deletes axioms (no new assumptions are
    introduced), so it is model-preserving.
    If the user of this pass removes further axioms because e.g., it is in the
    'aggressive' mode, it will have to validate the model by itself.

    Its contract is proved: deleting declarations other than procedures keeps every
    fact (`irrelevantAxioms_keeps`). -/
def irrelevantAxiomsPipelinePhase (functions : List String) : PipelinePhase where
  transform := irrelevantAxiomsTransform functions
  phase.name := "removeIrrelevantAxioms"
  requires := factSet![.typeAnnotated]
  preserves := factSet![.wellFormedCalls, .noCFGBodies, .noCalls, .noLoops,
                       .noLoopInvariants, .noLoopMeasures, .staticSingleAssignment,
                       .noBetaRedexes, .noPrecondsFromFuncs, .noNondetGuards,
                       .hasObligationForm, .noProcedureContracts,
                       .noPolymorphicProcedures,
                       .noPolymorphicFunctions, .typeAnnotated, .noInits, .treeForm,
                       .exitsCovered, .armsHaveObligations, .noCFGCycles]
  unproved := ProgramFactSet.empty
  preserves_ok := by
    intro f hf _ p _ _ hp _ _ _ hrun
    refine irrelevantAxioms_keeps ?_ hrun hp
    rintro rfl
    exact absurd hf (by decide)

end -- public section

end Core
