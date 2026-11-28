/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Transform.TerminationCheckProps
public import Strata.Languages.Core.ProgramFactProps

/-! # The facts `termCheck` keeps

Key results:

* `termCheck_keeps` — `termCheck` keeps every fact that reads only procedures, and
  `noPrecondsFromFuncs`; the `termCheck` phase's contract rests on it. -/

namespace Core

public section

open Transform

/-- **`termCheck` keeps every fact that reads only procedures, and `noPrecondsFromFuncs`.** -/
theorem termCheck_keeps {f : ProgramFact}
    (hf : f.readsOnlyProcedures = true ∨ f = .noPrecondsFromFuncs)
    {p p' : Program} {s s' : CoreTransformState} {b : Bool}
    (hrun : (TermCheck.termCheck p).run s = (.ok (b, p'), s')) (hp : f.holds p) : f.holds p' := by
  obtain ⟨hprocs, hpre⟩ := termCheck_post p s (b, p') s' hrun
  rcases hf with hf | rfl
  · exact ProgramFact.holds_of_procs_eq hf hprocs hp
  · exact hpre hp

end -- public section

end Core
