/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Transform.LambdaLift
import all Strata.Transform.LambdaLift
import all Strata.Transform.CoreTransform

/-! # What `lambdaLift` is proved to do

`lambdaLift` itself carries no proof: its contract is declared and tested
(`LambdaHigherOrderTests`). One fact about `lambdaLiftIfNeeded`, the phase that runs it
only where it is needed, is proved here.

- `runIfNeeded_of_not_needsRun`: on a program `run` has no work to do on (`needsRun`, with
  the arities of the state's factory), `runIfNeeded` reports no change, returns the
  program it was given and leaves the state as it is, so a pipeline ending with
  `lambdaLiftIfNeeded` hands such a program to the next phase as it is.

TODO: the top-level correctness theorem for `lambdaLift`, stated with
`OverapproximatesTraces` (`Strata.Transform.Specification`) between each procedure of
the input and of the output, together with the proof of its declared contract.
-/

namespace Core.LambdaLift

public section

/-- `runIfNeeded` is the identity on a program `run` has no work to do on. -/
theorem runIfNeeded_of_not_needsRun (p : Program) (s : Transform.CoreTransformState)
    (h : needsRun (Program.arityIn p.declArities s.factory) p = false) :
    (runIfNeeded p).run.run s = (.ok (false, p), s) := by
  simp only [needsRun, Bool.or_eq_false_iff] at h
  obtain ⟨hl, hm⟩ := h
  show (if liveNeedsLift (Program.arityIn p.declArities s.factory) p then run p
    else pure ((markSpuriousModels p).2,
      if (markSpuriousModels p).2 then (markSpuriousModels p).1 else p) :
      Transform.CoreTransformM _).run.run s = _
  rw [hl, hm]
  rfl

end -- public section

end Core.LambdaLift
