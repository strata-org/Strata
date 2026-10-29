/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.DL.Imperative.Logic.Termination

/-! # Event-language termination properties

Establishes propagation of must-termination through one-step and finite traced
execution, and extracts a finite terminal or exiting continuation from a
must-termination proof.
-/

public section

namespace Strata.Logic

open Imperative

/-- Every successor of a must-terminating configuration must terminate. -/
theorem EventLang.MustTerminate.of_step
    {P : PureExpr} {EventT : Type} {EL : EventLang P EventT}
    {cfg cfg' : EL.CfgT} {emitted : List EventT}
    (hterm : EL.MustTerminate cfg) (hstep : EL.step cfg emitted cfg') :
    EL.MustTerminate cfg' := by
  cases hterm with
  | terminal ρ => exact (EL.terminal_no_step ρ emitted cfg' hstep).elim
  | exiting label ρ =>
      exact (EL.exiting_no_step label ρ emitted cfg' hstep).elim
  | step _ successors => exact successors emitted cfg' hstep

/-- Every endpoint reachable from a must-terminating configuration must
terminate. -/
theorem EventLang.MustTerminate.of_traceStar
    {P : PureExpr} {EventT : Type} {EL : EventLang P EventT}
    {cfg cfg' : EL.CfgT} {trace : List EventT}
    (hterm : EL.MustTerminate cfg) (hrun : EL.traceStar cfg trace cfg') :
    EL.MustTerminate cfg' := by
  induction hrun with
  | refl => exact hterm
  | step _ emitted next _ _ hstep _ ih =>
    exact ih (hterm.of_step hstep)

/-- Must-termination provides some finite continuation to a terminal or exiting
configuration. This chooses one branch only after all branches have already been
proved terminating by `MustTerminate`. -/
theorem EventLang.MustTerminate.reaches_final
    {P : PureExpr} {EventT : Type} {EL : EventLang P EventT} {cfg : EL.CfgT}
    (hterm : EL.MustTerminate cfg) :
    ∃ (trace : List EventT) (ρ' : Env P),
      EL.traceStar cfg trace (EL.terminalCfg ρ') ∨
      ∃ label, EL.traceStar cfg trace (EL.exitingCfg label ρ') := by
  induction hterm with
  | terminal ρ => exact ⟨[], ρ, .inl (.refl _)⟩
  | exiting label ρ => exact ⟨[], ρ, .inr ⟨label, .refl _⟩⟩
  | step progress _ ih =>
    obtain ⟨emitted, next, hstep⟩ := progress
    obtain ⟨trace, ρ', hfinal⟩ := ih emitted next hstep
    refine ⟨emitted ++ trace, ρ', ?_⟩
    rcases hfinal with hterminal | ⟨label, hexiting⟩
    · exact .inl (.step _ emitted _ trace _ hstep hterminal)
    · exact .inr ⟨label, .step _ emitted _ trace _ hstep hexiting⟩

end Strata.Logic

end -- public section
