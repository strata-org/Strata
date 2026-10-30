/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Core.Verifier
public import Strata.Transform.WP.WPCoreProgram
public import Strata.Transform.DeadDefElimCoreCorrect
import all Strata.Languages.Core.Verifier
import all Strata.Languages.Core.PipelinePhase
import all Strata.Transform.CoreTransform

/-! # What the WP pipeline phase computes

This file states what a successful run of `wpPipelinePhase`, the second of the pipeline phases
`--vcgen wp` runs (`wpVCGenPhases`, `Passive/DeclObligationsCoreCorrect.lean`), computes.

TODO: state the soundness of `wpPipelinePhase` as `OverapproximatesTracesUptoWhen`
(`Strata/Transform/Specification.lean`) on each procedure body it rewrites.

Key theorems: `wpPipelinePhase_ok`. -/

namespace Core
namespace WP

open Imperative Imperative.BigStep Imperative.WP Imperative.DeadDefElim Core.DeadDefElim

public section

/-- A successful run of `wpPipelinePhase` on `program` returns the guarded program of `program`
    for the names of the functions of the factory `moreFns` extends. -/
theorem wpPipelinePhase_ok {m : Lambda.Factory CoreLParams}
    {program out : Program} {s s' : Transform.CoreTransformState} {b : Bool}
    (h : ((wpPipelinePhase m).transform program).run s = (.ok (b, out), s')) :
    ∃ fac, Core.Factory.addFactory m = .ok fac ∧
      wpProcsProgram (fac.toArray.toList.map (·.name)) program = .ok out := by
  simp only [wpPipelinePhase, modelPreservingPipelinePhase, Transform.liftDiag] at h
  rcases hw : wpProgram program m with _ | mid <;> rw [hw] at h <;> cases h
  simp only [wpProgram, Bind.bind, Except.bind, throw, throwThe, MonadExceptOf.throw] at hw
  repeat (split at hw <;> try cases hw)
  exact ⟨_, ‹_›, by assumption⟩

end -- public section

end WP
end Core
