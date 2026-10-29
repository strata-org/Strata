/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.DL.Imperative.Logic.Temporal
public import Strata.DL.Imperative.Logic.Termination

/-! # Properties of the temporal operators

## Key results

- `EventLang.AllPathsAlways.of_invariant`: a predicate every step preserves holds
  on all paths, always, from a configuration satisfying it.
- `EventLang.AllPathsEventually.not_somePathAlways_not`: if every run reaches
  `S`, no infinite run avoids it.
- `EventLang.allPathsAlways_iff_not_somePathEventually_not`: `S` holds on all
  paths, always, exactly when no reachable configuration violates it.
- `EventLang.mustTerminate_iff_allPathsEventually`: `MustTerminate` is
  `AllPathsEventually` of the final configurations.
-/

public section

namespace Strata.Logic

open Imperative

variable {P : PureExpr} {EventT : Type}

/-- A predicate every step preserves holds on every configuration reachable from
    one satisfying it. -/
theorem EventLang.AllPathsAlways.of_invariant {EL : EventLang P EventT}
    {S : EL.CfgT → Prop} (hS : ∀ cfg emitted cfg', S cfg → EL.step cfg emitted cfg' → S cfg')
    {cfg : EL.CfgT} (h : S cfg) : EL.AllPathsAlways S cfg := by
  rintro cfg' ⟨trace, hrun⟩
  induction hrun with
  | refl => exact h
  | step _ _ _ _ _ hstep _ ih => exact ih (hS _ _ _ h hstep)

/-- If every run from `cfg` reaches `S`, no infinite run from `cfg` avoids it. -/
theorem EventLang.AllPathsEventually.not_somePathAlways_not {EL : EventLang P EventT}
    {S : EL.CfgT → Prop} {cfg : EL.CfgT} (h : EL.AllPathsEventually S cfg) :
    ¬ EL.SomePathAlways (fun c => ¬ S c) cfg := by
  induction h with
  | now hs =>
    rintro ⟨f, h0, _, hn⟩
    exact hn 0 (by rw [h0]; exact hs)
  | step _ _ ih =>
    rintro ⟨f, h0, hf, hn⟩
    obtain ⟨emitted, hstep⟩ := hf 0
    rw [h0] at hstep
    exact ih _ _ hstep ⟨fun i => f (i + 1), rfl, fun i => hf (i + 1), fun i => hn (i + 1)⟩

/-- `S` holds on all paths, always, exactly when no reachable configuration
    violates it. -/
theorem EventLang.allPathsAlways_iff_not_somePathEventually_not {EL : EventLang P EventT}
    {S : EL.CfgT → Prop} {cfg : EL.CfgT} :
    EL.AllPathsAlways S cfg ↔ ¬ EL.SomePathEventually (fun c => ¬ S c) cfg := by
  constructor
  · rintro h ⟨cfg', hr, hn⟩
    exact hn (h cfg' hr)
  · intro h cfg' hr
    exact Classical.byContradiction fun hn => h ⟨cfg', hr, hn⟩

/-- **`MustTerminate` is `AllPathsEventually` of the final configurations**:
    every run reaches a terminal or exiting configuration. -/
theorem EventLang.mustTerminate_iff_allPathsEventually {EL : EventLang P EventT}
    {cfg : EL.CfgT} : EL.MustTerminate cfg ↔ EL.AllPathsEventually EL.Final cfg := by
  constructor
  · intro h
    induction h with
    | terminal ρ => exact .now (.inl ⟨ρ, rfl⟩)
    | exiting label ρ => exact .now (.inr ⟨label, ρ, rfl⟩)
    | step progress _ ih => exact .step progress ih
  · intro h
    induction h with
    | now hfinal =>
      rcases hfinal with ⟨ρ, rfl⟩ | ⟨label, ρ, rfl⟩
      · exact .terminal ρ
      · exact .exiting label ρ
    | step progress _ ih => exact .step progress ih

end Strata.Logic

end -- public section
