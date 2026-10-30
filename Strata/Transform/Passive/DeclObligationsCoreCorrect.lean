/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Core.Verifier
public import Strata.Transform.Passive.CoreProgram
public import Strata.Transform.DeadDefElimCoreCorrect
import all Strata.Languages.Core.Verifier
import all Strata.Languages.Core.PipelinePhase
import all Strata.Transform.CoreTransform

/-! # What the declaration pipeline phase computes

The pipeline phases `--vcgen wp` runs in place of symbolic evaluation are
`declObligationsPipelinePhase`, `wpPipelinePhase`, `ssaPipelinePhase`, then
`deadDefElimPipelinePhase` (`wpVCGenPhases`).  This file states what a successful run of the
first computes; `WP/WPCoreCorrect.lean` and `SSA/SSACoreCorrect.lean` state it for the second
and the third.  No theorem lifts a soundness statement to the pipeline phases.

TODO: state the soundness of `declObligationsPipelinePhase` as `OverapproximatesTracesUptoWhen`
(`Strata/Transform/Specification.lean`) on each procedure body it keeps and each lemma obligation
it adds.

Key theorems: `declObligationsPipelinePhase_ok`. -/

namespace Core
namespace WP

open Imperative Imperative.BigStep Imperative.WP Imperative.DeadDefElim Core.DeadDefElim

public section

/-- A successful run of `declObligationsPipelinePhase` on `program` returns the declaration
    program of `program` for some program-level declarations and lemma obligations. -/
theorem declObligationsPipelinePhase_ok {o : VerifyOptions} {m : Lambda.Factory CoreLParams}
    {program out : Program} {s s' : Transform.CoreTransformState} {b : Bool}
    (h : ((declObligationsPipelinePhase o m).transform program).run s = (.ok (b, out), s')) :
    ∃ declProgram lemmaObls,
      declObligationsProgramWith declProgram lemmaObls program = .ok out := by
  simp only [declObligationsPipelinePhase, modelPreservingPipelinePhase, Transform.liftDiag] at h
  rcases hw : declObligationsProgram o program m with _ | ⟨mid, st⟩ <;> rw [hw] at h <;> cases h
  simp only [declObligationsProgram, Bind.bind, Except.bind, throw, throwThe,
    MonadExceptOf.throw] at hw
  repeat (split at hw <;> try cases hw)
  exact ⟨_, _, by assumption⟩

end -- public section

end WP
end Core
