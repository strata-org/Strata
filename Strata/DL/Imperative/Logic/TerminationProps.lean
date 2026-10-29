/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.DL.Imperative.Logic.Termination
import Strata.Util.RelationsProps

/-! # Event-language termination properties

Establishes propagation of must-termination through one-step and finite traced
execution, and extracts a finite terminal or exiting continuation from a
must-termination proof.

It also relates must-termination to the two ways an execution can fail to
finish, diverging and getting stuck.

## Key results

- `EventLang.mustTerminate_iff`: a configuration must terminate exactly when it
  neither diverges nor may get stuck.
- `EventLang.not_mustTerminate_iff`: it fails to must-terminate exactly when it
  diverges or may get stuck.
- `EventLang.terminates_iff`: the same characterization for `Terminates`.
- `EventLang.MustTerminate.not_canDiverge`, `EventLang.MustTerminate.not_mayGetStuck`:
  the two directions that need no classical reasoning.
- `EventLang.Final.not_canDiverge`, `EventLang.Stuck.not_canDiverge`: final and
  stuck configurations do not diverge.
- `EventLang.CanDiverge.of_invariant`, `EventLang.CanDiverge.of_cycle`,
  `EventLang.CanDiverge.step`: how a diverging sequence is built, from a set
  whose members each step, or reach in at least one step, a member.
- `EventLang.MustDiverge.canDiverge`, `EventLang.MustDiverge.not_mustTerminate`: a
  configuration that must diverge can, and does not must-terminate.
- `EventLang.traceStar_iff_reachesWithin`: a finite execution is one within some
  bound.
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

/-! ## Diverging and getting stuck -/

/-- A final configuration takes no step. -/
private theorem EventLang.Final.no_step
    {P : PureExpr} {EventT : Type} {EL : EventLang P EventT}
    {cfg cfg' : EL.CfgT} {emitted : List EventT}
    (hfinal : EL.Final cfg) : ¬ EL.step cfg emitted cfg' := by
  rcases hfinal with ⟨ρ, rfl⟩ | ⟨label, ρ, rfl⟩
  · exact EL.terminal_no_step ρ emitted cfg'
  · exact EL.exiting_no_step label ρ emitted cfg'

/-- A final configuration does not diverge. -/
theorem EventLang.Final.not_canDiverge
    {P : PureExpr} {EventT : Type} {EL : EventLang P EventT} {cfg : EL.CfgT}
    (hfinal : EL.Final cfg) : ¬ EL.CanDiverge cfg := by
  rintro ⟨f, rfl, hf⟩
  obtain ⟨_, hstep⟩ := hf 0
  exact hfinal.no_step hstep

/-- A stuck configuration does not diverge. -/
theorem EventLang.Stuck.not_canDiverge
    {P : PureExpr} {EventT : Type} {EL : EventLang P EventT} {cfg : EL.CfgT}
    (hstuck : EL.Stuck cfg) : ¬ EL.CanDiverge cfg := by
  rintro ⟨f, rfl, hf⟩
  obtain ⟨_, hstep⟩ := hf 0
  exact hstuck.2 _ _ hstep

/-- **A configuration in a set whose every member has a successor in the set
    can diverge.** The sequence is built by choice. -/
theorem EventLang.CanDiverge.of_invariant
    {P : PureExpr} {EventT : Type} {EL : EventLang P EventT} (Q : EL.CfgT → Prop)
    (next : ∀ c, Q c → ∃ c' emitted, EL.step c emitted c' ∧ Q c')
    {cfg : EL.CfgT} (h : Q cfg) : EL.CanDiverge cfg :=
  ⟨fun i => (EventLang.chooseSeq Q next ⟨cfg, h⟩ i).1, rfl, fun i =>
    let c := EventLang.chooseSeq Q next ⟨cfg, h⟩ i
    ⟨_, (Classical.choose_spec (Classical.choose_spec (next c.1 c.2))).1⟩⟩

/-- A configuration that steps to one that can diverge can diverge. -/
theorem EventLang.CanDiverge.step
    {P : PureExpr} {EventT : Type} {EL : EventLang P EventT}
    {cfg cfg' : EL.CfgT} {emitted : List EventT}
    (hstep : EL.step cfg emitted cfg') (h : EL.CanDiverge cfg') : EL.CanDiverge cfg := by
  obtain ⟨f, h0, hf⟩ := h
  refine ⟨fun | 0 => cfg | i + 1 => f i, rfl, fun i => ?_⟩
  cases i with
  | zero => exact ⟨emitted, by simpa [h0] using hstep⟩
  | succ i => exact hf i

/-- A configuration can diverge when it belongs to a set `R` whose every member
    reaches another member in at least one step. This is how a concrete loop is
    shown to diverge: `R` is the set of states at the loop head. -/
theorem EventLang.CanDiverge.of_cycle
    {P : PureExpr} {EventT : Type} {EL : EventLang P EventT} (R : EL.CfgT → Prop)
    (hR : ∀ c, R c → ∃ emitted c₁ trace c', EL.step c emitted c₁ ∧
      EL.traceStar c₁ trace c' ∧ R c')
    {cfg : EL.CfgT} (h : R cfg) : EL.CanDiverge cfg := by
  refine EventLang.CanDiverge.of_invariant (EL := EL)
    (fun c => ∃ trace d, EL.traceStar c trace d ∧ R d) ?_ ⟨[], cfg, .refl _, h⟩
  rintro c ⟨trace, d, hrun, hd⟩
  cases hrun with
  | refl =>
    obtain ⟨emitted, c₁, trace', c', hstep, hrun', hc'⟩ := hR _ hd
    exact ⟨c₁, emitted, hstep, trace', c', hrun', hc'⟩
  | step _ emitted c₁ rest _ hstep hrun' =>
    exact ⟨c₁, emitted, hstep, rest, d, hrun', hd⟩

/-- A configuration that must terminate is not stuck. -/
private theorem EventLang.MustTerminate.not_stuck
    {P : PureExpr} {EventT : Type} {EL : EventLang P EventT} {cfg : EL.CfgT}
    (hterm : EL.MustTerminate cfg) : ¬ EL.Stuck cfg := by
  intro hstuck
  cases hterm with
  | terminal ρ => exact hstuck.1 (.inl ⟨ρ, rfl⟩)
  | exiting label ρ => exact hstuck.1 (.inr ⟨label, ρ, rfl⟩)
  | step progress _ =>
    obtain ⟨emitted, cfg', hstep⟩ := progress
    exact hstuck.2 emitted cfg' hstep

/-- No execution from a configuration that must terminate gets stuck. -/
theorem EventLang.MustTerminate.not_mayGetStuck
    {P : PureExpr} {EventT : Type} {EL : EventLang P EventT} {cfg : EL.CfgT}
    (hterm : EL.MustTerminate cfg) : ¬ EL.MayGetStuck cfg := by
  rintro ⟨_, _, hrun, hstuck⟩
  exact (hterm.of_traceStar hrun).not_stuck hstuck

/-- A configuration that must terminate does not diverge. -/
theorem EventLang.MustTerminate.not_canDiverge
    {P : PureExpr} {EventT : Type} {EL : EventLang P EventT} {cfg : EL.CfgT}
    (hterm : EL.MustTerminate cfg) : ¬ EL.CanDiverge cfg := by
  induction hterm with
  | terminal ρ => exact EventLang.Final.not_canDiverge (.inl ⟨ρ, rfl⟩)
  | exiting label ρ => exact EventLang.Final.not_canDiverge (.inr ⟨label, ρ, rfl⟩)
  | step _ _ ih =>
    rintro ⟨f, h0, hf⟩
    obtain ⟨emitted, hstep⟩ := hf 0
    rw [h0] at hstep
    exact ih _ _ hstep ⟨fun i => f (i + 1), rfl, fun i => hf (i + 1)⟩

/-- A configuration that neither diverges nor may get stuck must terminate.
    Classical: from a configuration that does not must-terminate, it picks a
    successor that does not either, and repeats that choice forever. -/
private theorem EventLang.mustTerminate_of_not_canDiverge
    {P : PureExpr} {EventT : Type} {EL : EventLang P EventT} {cfg : EL.CfgT}
    (hdiv : ¬ EL.CanDiverge cfg) (hstuck : ¬ EL.MayGetStuck cfg) : EL.MustTerminate cfg := by
  apply Classical.byContradiction
  intro hnt
  apply hdiv
  refine EventLang.CanDiverge.of_invariant (EL := EL)
    (fun c => ¬ EL.MustTerminate c ∧ ¬ EL.MayGetStuck c) ?_ ⟨hnt, hstuck⟩
  intro c ⟨hnt, hns⟩
  have hnf : ¬ EL.Final c := by
    rintro (⟨ρ, rfl⟩ | ⟨label, ρ, rfl⟩)
    · exact hnt (.terminal ρ)
    · exact hnt (.exiting label ρ)
  have hprog : ∃ emitted c', EL.step c emitted c' :=
    Classical.byContradiction fun hno =>
      hns ⟨[], c, .refl _, hnf, fun emitted c' hstep => hno ⟨emitted, c', hstep⟩⟩
  have hsucc : ∃ emitted c', EL.step c emitted c' ∧ ¬ EL.MustTerminate c' :=
    Classical.byContradiction fun hno =>
      hnt (.step hprog fun emitted c' hstep =>
        Classical.byContradiction fun hm => hno ⟨emitted, c', hstep, hm⟩)
  obtain ⟨emitted, c', hstep, hm⟩ := hsucc
  exact ⟨c', emitted, hstep, hm, fun ⟨trace, d, hrun, hd⟩ =>
    hns ⟨emitted ++ trace, d, .step _ emitted _ trace _ hstep hrun, hd⟩⟩

/-- A configuration must terminate exactly when it neither diverges nor may get
    stuck. -/
theorem EventLang.mustTerminate_iff
    {P : PureExpr} {EventT : Type} {EL : EventLang P EventT} {cfg : EL.CfgT} :
    EL.MustTerminate cfg ↔ ¬ EL.CanDiverge cfg ∧ ¬ EL.MayGetStuck cfg :=
  ⟨fun h => ⟨h.not_canDiverge, h.not_mayGetStuck⟩,
   fun ⟨hdiv, hstuck⟩ => EventLang.mustTerminate_of_not_canDiverge hdiv hstuck⟩

/-- A configuration fails to must-terminate exactly when it diverges or may get
    stuck. -/
theorem EventLang.not_mustTerminate_iff
    {P : PureExpr} {EventT : Type} {EL : EventLang P EventT} {cfg : EL.CfgT} :
    ¬ EL.MustTerminate cfg ↔ EL.CanDiverge cfg ∨ EL.MayGetStuck cfg := by
  rw [EventLang.mustTerminate_iff]
  constructor
  · intro h
    by_cases hdiv : EL.CanDiverge cfg
    · exact .inl hdiv
    · by_cases hstuck : EL.MayGetStuck cfg
      · exact .inr hstuck
      · exact absurd ⟨hdiv, hstuck⟩ h
  · rintro (hdiv | hstuck) ⟨hndiv, hnstuck⟩
    · exact hndiv hdiv
    · exact hnstuck hstuck

/-- Every execution of `s` from `ρ₀` terminates exactly when none diverges and
    none gets stuck. -/
theorem EventLang.terminates_iff
    {P : PureExpr} {EventT : Type} {EL : EventLang P EventT} {s : EL.StmtT} {ρ₀ : Env P} :
    EL.Terminates s ρ₀ ↔
      ¬ EL.CanDiverge (EL.stmtCfg s ρ₀) ∧ ¬ EL.MayGetStuck (EL.stmtCfg s ρ₀) :=
  EventLang.mustTerminate_iff

/-- **A configuration that must diverge can diverge.** -/
theorem EventLang.MustDiverge.canDiverge
    {P : PureExpr} {EventT : Type} {EL : EventLang P EventT} {cfg : EL.CfgT}
    (h : EL.MustDiverge cfg) : EL.CanDiverge cfg := by
  refine EventLang.CanDiverge.of_invariant (EL := EL) EL.MustDiverge ?_ h
  intro c hc
  obtain ⟨emitted, c', hstep⟩ := hc 0 [] c ⟨rfl, rfl⟩
  exact ⟨c', emitted, hstep, fun n trace c'' hr =>
    hc (n + 1) (emitted ++ trace) c'' (.inr ⟨emitted, c', trace, hstep, hr, rfl⟩)⟩

/-- A configuration that must diverge does not must-terminate. -/
theorem EventLang.MustDiverge.not_mustTerminate
    {P : PureExpr} {EventT : Type} {EL : EventLang P EventT} {cfg : EL.CfgT}
    (h : EL.MustDiverge cfg) : ¬ EL.MustTerminate cfg :=
  fun ht => ht.not_canDiverge h.canDiverge

/-- **A finite execution is one within some bound.** -/
theorem EventLang.traceStar_iff_reachesWithin
    {P : PureExpr} {EventT : Type} {EL : EventLang P EventT}
    {cfg cfg' : EL.CfgT} {trace : List EventT} :
    EL.traceStar cfg trace cfg' ↔ ∃ n, EL.ReachesWithin n cfg trace cfg' :=
  reflTransTrace_iff_reflTransTraceN

end Strata.Logic

end -- public section
