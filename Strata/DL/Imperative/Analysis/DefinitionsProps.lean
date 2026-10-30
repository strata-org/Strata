/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.DL.Imperative.Analysis.Definitions
public import Strata.DL.Imperative.Logic.TerminationProps
public import Strata.DL.Imperative.Logic.Temporal

/-! # Analyses as definitions: properties

## Key results

- `EventLang.RunsOverapproximate.refl`, `.trans`, `.mono`: overapproximation of
  runs is reflexive, composes and is monotone in its relation.
- `EventLang.RunsOverapproximate.reaches`: every configuration the source
  reaches has a configuration the target reaches, with related traces.
- `EventLang.RunsOverapproximate.tracesSatisfy`: a property of finite traces
  that the relation reflects carries back from the target to the source, so
  safety proved on a transformed program holds on the original.
-/

public section

namespace Strata.Logic

open Imperative

variable {P : PureExpr} {EventT : Type} {EL : EventLang P EventT}

/-- Overapproximation of runs is reflexive for a reflexive relation. -/
theorem EventLang.RunsOverapproximate.refl {R : Relation (List EventT)} (hR : IsReflexive R)
    (cfg : EL.CfgT) : EL.RunsOverapproximate R EL cfg cfg :=
  fun n trace c h => ⟨n, trace, c, h, hR trace⟩

/-- **Overapproximation of runs composes**, up to the composition of the
    relations. -/
theorem EventLang.RunsOverapproximate.trans {R₁ R₂ : Relation (List EventT)}
    {EL₁ EL₂ EL₃ : EventLang P EventT} {c₁ : EL₁.CfgT} {c₂ : EL₂.CfgT} {c₃ : EL₃.CfgT}
    (h₁₂ : EL₁.RunsOverapproximate R₁ EL₂ c₁ c₂) (h₂₃ : EL₂.RunsOverapproximate R₂ EL₃ c₂ c₃) :
    EL₁.RunsOverapproximate (RComp R₁ R₂) EL₃ c₁ c₃ := by
  intro n trace c h
  obtain ⟨m, trace', c', h', hr⟩ := h₁₂ n trace c h
  obtain ⟨k, trace'', c'', h'', hr'⟩ := h₂₃ m trace' c' h'
  exact ⟨k, trace'', c'', h'', trace', hr, hr'⟩

/-- Overapproximation of runs is monotone in the relation. -/
theorem EventLang.RunsOverapproximate.mono {EventT₁ EventT₂ : Type}
    {R R' : List EventT₁ → List EventT₂ → Prop}
    {EL₁ : EventLang P EventT₁} {EL₂ : EventLang P EventT₂} {c₁ : EL₁.CfgT} {c₂ : EL₂.CfgT}
    (h : EL₁.RunsOverapproximate R EL₂ c₁ c₂) (hRR' : ∀ t t', R t t' → R' t t') :
    EL₁.RunsOverapproximate R' EL₂ c₁ c₂ := by
  intro n trace c hr
  obtain ⟨m, trace', c', h', hrel⟩ := h n trace c hr
  exact ⟨m, trace', c', h', hRR' _ _ hrel⟩

/-- **Overapproximation preserves reachability**: every configuration the
    source reaches has a configuration the target reaches, along a related
    trace. -/
theorem EventLang.RunsOverapproximate.reaches {EventT₁ EventT₂ : Type}
    {R : List EventT₁ → List EventT₂ → Prop}
    {EL₁ : EventLang P EventT₁} {EL₂ : EventLang P EventT₂} {c₁ : EL₁.CfgT} {c₂ : EL₂.CfgT}
    (h : EL₁.RunsOverapproximate R EL₂ c₁ c₂) {c : EL₁.CfgT} (hr : EL₁.Reaches c₁ c) :
    ∃ c' trace trace', EL₂.Reaches c₂ c' ∧ EL₁.traceStar c₁ trace c ∧
      EL₂.traceStar c₂ trace' c' ∧ R trace trace' := by
  obtain ⟨trace, hrun⟩ := hr
  obtain ⟨n, hn⟩ := EventLang.traceStar_iff_reachesWithin.mp hrun
  obtain ⟨m, trace', c', hm, hrel⟩ := h n trace c hn
  have hrun' := EventLang.traceStar_iff_reachesWithin.mpr ⟨m, hm⟩
  exact ⟨c', trace, trace', ⟨trace', hrun'⟩, hrun, hrun', hrel⟩

/-- **Safety carries back along an overapproximation**: when every trace of the
    target satisfies `φ`, and the relation reflects `φ`, every trace of the
    source satisfies it. Deductive verification is the case where `φ` is
    validity of an assertion. -/
theorem EventLang.RunsOverapproximate.tracesSatisfy {EventT₁ EventT₂ : Type}
    {R : List EventT₁ → List EventT₂ → Prop}
    {EL₁ : EventLang P EventT₁} {EL₂ : EventLang P EventT₂} {c₁ : EL₁.CfgT} {c₂ : EL₂.CfgT}
    {φ₁ : List EventT₁ → Prop} {φ₂ : List EventT₂ → Prop}
    (h : EL₁.RunsOverapproximate R EL₂ c₁ c₂) (hR : ∀ t t', R t t' → φ₂ t' → φ₁ t)
    (hsafe : EL₂.TracesSatisfy φ₂ c₂) : EL₁.TracesSatisfy φ₁ c₁ := by
  intro trace c hrun
  obtain ⟨n, hn⟩ := EventLang.traceStar_iff_reachesWithin.mp hrun
  obtain ⟨m, trace', c', hm, hrel⟩ := h n trace c hn
  exact hR _ _ hrel (hsafe _ _ (EventLang.traceStar_iff_reachesWithin.mpr ⟨m, hm⟩))

end Strata.Logic

end -- public section
