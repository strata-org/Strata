/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Transform.CFGLoopElim
import all Strata.Transform.CFGLoopElim

/-! # Properties of CFG loop elimination

* `cutLoops_acyclic`: a body `cutLoops` returns has no cycle reachable from its entry,
  which is what the fact `noCFGCycles` asks of every CFG body after `cfgLoopElim`. -/

namespace Core.CFGLoopElim

public section

/-- `rejectCycles` succeeds only on a body with no cycle reachable from its entry. -/
private theorem rejectCycles_ok {procName : String} {cfg : DetCFG}
    (h : rejectCycles procName cfg = .ok ()) :
    (Imperative.CFG.cycleLabelsWith cfg.succMap [cfg.entry]).isEmpty = true := by
  unfold rejectCycles at h
  by_cases hc : (Imperative.CFG.cycleLabelsWith cfg.succMap [cfg.entry]).isEmpty = true
  · exact hc
  · simp [hc] at h

/-- A body `cutLoops` returns has no cycle reachable from its entry. -/
theorem cutLoops_acyclic {procName : String} {cfg cut : DetCFG} {changed : Bool}
    (h : cutLoops procName cfg = .ok (changed, cut)) :
    (Imperative.CFG.cycleLabelsWith cut.succMap [cut.entry]).isEmpty = true := by
  unfold cutLoops at h
  cases hcore : cutLoopsCore procName cfg with
  | error e => rw [hcore] at h; cases h
  | ok r =>
    obtain ⟨_, g⟩ := r
    rw [hcore] at h
    cases hr : rejectCycles procName g with
    | error e =>
      simp only [bind, Except.bind, hr] at h
      cases h
    | ok u =>
      simp only [bind, Except.bind, hr, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨_, rfl⟩ := h
      exact rejectCycles_ok hr

end

end Core.CFGLoopElim
