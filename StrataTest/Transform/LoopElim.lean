/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Transform.LoopElim
import Strata.Languages.Core.Verifier

/-! ## Loop-elimination pipeline phase obligation tests -/
section LoopElimPhaseTests
open Core
open Strata.SMT
open Core.SMT (Result)

private def satResult : Result := .sat []
private def unknownResult : Result := .unknown (some [])

/-- Obligation with loop-elimination labels in path conditions. -/
private def loopElimObligation : Imperative.ProofObligation Core.Expression :=
  { label := "test_loopElim", property := .assert,
    assumptions := [[("assume_invariant_0_0", .fvar () ⟨"x", ()⟩ none), ("assume_guard_0", .fvar () ⟨"y", ()⟩ none)]],
    obligation := .true (), metadata := {} }

/-- Obligation with no abstraction labels — models are sound. -/
private def cleanObligation : Imperative.ProofObligation Core.Expression :=
  { label := "test_clean", property := .assert,
    assumptions := [[("precond_x_positive", .true ())]],
    obligation := .true (), metadata := {} }

-- loopElimPipelinePhase: rejects sat when obligation has non-trivial loop-elim labels
#guard (satResult.adjustForPhases [loopElimPipelinePhase.phase] loopElimObligation).1 == unknownResult

-- loopElimPipelinePhase: preserves sat when obligation has no loop-elim labels
#guard (satResult.adjustForPhases [loopElimPipelinePhase.phase] cleanObligation).1 == satResult

/-- Obligation with trivially-true loop-elimination labels (e.g. while(true) loops). -/
private def trivialLoopElimObligation : Imperative.ProofObligation Core.Expression :=
  { label := "test_trivial_loopElim", property := .assert,
    assumptions := [[("assume_invariant_0_0", .true ()), ("assume_guard_0", .true ())]],
    obligation := .true (), metadata := {} }

-- loopElimPipelinePhase: preserves sat when loop-elim labels have trivially-true expressions
#guard (satResult.adjustForPhases [loopElimPipelinePhase.phase] trivialLoopElimObligation).1 == satResult

end LoopElimPhaseTests
