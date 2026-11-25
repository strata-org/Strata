/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Transform.TerminationCheckFactCorrect
import Strata.Transform.CoreTransformProps
import Strata.Languages.Core.AbstractCalls

/-! # The `termCheck` pipeline phase

This file only assembles the phase: the transform is in `TerminationCheck`, and the proofs of
its contract are in `TerminationCheckFactCorrect`, which imports the transform. -/

namespace Core

public section

/-- TermCheck pipeline phase: generates termination-checking lemmas for
    recursive functions. Model-preserving because it only adds new lemmas,
    adtRank functions and their axioms. It keeps every procedure as it is, whatever its
    body.

    Its contract is proved, but for `typeAnnotated` (`termCheck_keeps`). -/
def termCheckPipelinePhase : PipelinePhase where
  -- Its lemmas name the type parameters of a callee that a call does not determine with
  -- `termTyVarPrefix`, and bind the type variables of abstracted calls with `abstractTyPrefix`.
  -- Both are reserved type-variable prefixes (`Lambda.reservedNamePrefixes`), which type
  -- checking renames away from the program's type parameters, so the pass only records them.
  transform p := Transform.recordIdentPrefixes [TermCheck.termTyVarPrefix, abstractTyPrefix] p
    (TermCheck.termCheck p)
  maintainsIdentPrefixes := true
  phase.name := "termCheck"
  requires := factSet![.typeAnnotated]
  -- `noBetaRedexes` is not claimed because a call's measure is instantiated by
  -- substituting the call's arguments, and a function-typed parameter applied to
  -- an abstraction argument leaves a redex behind. `noPolymorphicFunctions` is not
  -- claimed because a rank function is generic in its datatype's type parameters;
  -- `monomorphizeFunctions`, which runs after `termCheck`, specializes it.
  preserves := factSet![.noCFGBodies, .noCalls, .noLoops, .noLoopInvariants,
                       .noLoopMeasures, .staticSingleAssignment,
                       .noPrecondsFromFuncs, .noNondetGuards, .noProcedureContracts,
                       .typeAnnotated, .noInits, .exitsCovered, .noCFGCycles]
  -- `typeAnnotated`: every generated rank function, axiom and lemma has to be shown fully
  -- annotated, through the measures, the specialized rank axioms and the abstraction of
  -- the block's calls in each lemma. Believed true: the generators annotate every operator
  -- they build, `TermCheckContractTests` checks it on the programs it runs, and a rank whose
  -- instance is unknown is annotated at the callee's declared type.
  unproved := factSet![.typeAnnotated]
  preserves_ok := by
    intro f hf hu _ _ _ hp _ _ _ hrun
    obtain ⟨_, hrun₀, rfl⟩ := Transform.recordIdentPrefixes_run hrun
    refine ProgramFact.holds_of_decls_eq ?_ (termCheck_keeps ?_ hrun₀ hp)
    · rfl
    revert hf hu
    cases f <;> decide

end -- public section

end Core
