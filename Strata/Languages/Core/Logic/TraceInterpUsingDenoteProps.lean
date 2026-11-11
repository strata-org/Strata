/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Core.Logic.TraceInterpUsingDenote
public import Strata.DL.Imperative.BigStep.Sem
public import Strata.DL.Imperative.Logic.TraceRelations

/-! # Properties of the denotation-based condition interpretation

`DenoteBasedInterp F` reads a condition captured under a runtime factory over `F` by its
evaluation to `true`, so on such conditions it agrees with evaluation to `true`
(`evalInterp_holds_iff_denoteBasedInterp`).  A condition captured under another factory is read
by an arbitrary predicate of the world, so `DenoteBasedInterp F` is stable under an
event-argument relation only for conditions captured over `F`
(`denoteBasedInterp_stableUnder`), and a trace relation stated under evaluation to `true`
carries over to it only for traces whose events are captured over `F`
(`weakensAssumes_denoteBasedInterp`).

Key theorems: `evalInterp_holds_iff_denoteBasedInterp`, `denoteBasedInterp_stableUnder`,
`weakensAssumes_denoteBasedInterp`. -/

public section

namespace Core.Logic

open Imperative

/-- For a condition captured under a runtime factory over `F`, reading it under its own
    runtime factory (`Imperative.BigStep.evalInterp`) agrees with `DenoteBasedInterp F` in
    every world. -/
theorem evalInterp_holds_iff_denoteBasedInterp {F : Lambda.Factory Core.CoreLParams}
    (w : (DenoteBasedInterp F).World) (c : Imperative.EventArg Expression)
    (hc : c.factory.factory = F) :
    (Imperative.BigStep.evalInterp : ConditionInterp Expression).holds () c ↔
      (DenoteBasedInterp F).holds w c := by
  simp [Imperative.BigStep.evalInterp, DenoteBasedInterp, hc]

/-- **`DenoteBasedInterp F` is stable on conditions captured over `F`.**  For an event-argument
    relation `R` keeping the factory, under which evaluation to `true` is stable: related
    conditions whose source is captured under a runtime factory over `F` hold alike under
    `DenoteBasedInterp F`. -/
theorem denoteBasedInterp_stableUnder {F : Lambda.Factory CoreLParams}
    {R : EventArg Expression → EventArg Expression → Prop}
    (hstable : (Imperative.BigStep.evalInterp : ConditionInterp Expression).StableUnder R)
    (hfac : ∀ {a b}, R a b → b.factory = a.factory) :
    (DenoteBasedInterp F).StableUnder (fun a b => R a b ∧ a.factory.factory = F) := by
  intro w a b ⟨h, ha⟩
  have hb : b.factory.factory = F := (hfac h) ▸ ha
  exact (evalInterp_holds_iff_denoteBasedInterp w a ha).symm.trans
    ((hstable () a b h).trans (evalInterp_holds_iff_denoteBasedInterp w b hb))

/-- **Weakened assumptions under evaluation are weakened assumptions under the denotation**, for
    traces whose events are all captured under runtime factories over `F`. -/
theorem weakensAssumes_denoteBasedInterp {F : Lambda.Factory CoreLParams}
    {s t : Trace Expression}
    (h : Trace.WeakensAssumes Imperative.BigStep.evalInterp s t)
    (hs : ∀ ev ∈ s, ev.condition.factory.factory = F)
    (ht : ∀ ev ∈ t, ev.condition.factory.factory = F) :
    Trace.WeakensAssumes (DenoteBasedInterp F) s t := by
  induction h with
  | nil => exact .nil
  | @cons e e' _ _ he _ ih =>
    have hfe := hs e List.mem_cons_self
    have hfe' := ht e' List.mem_cons_self
    refine .cons ?_ (ih (fun ev hev => hs ev (List.mem_cons_of_mem _ hev))
      (fun ev hev => ht ev (List.mem_cons_of_mem _ hev)))
    cases e <;> cases e' <;> simp only [Event.WeakensAssume, Event.condition] at he hfe hfe' ⊢
    · exact ⟨he.1, he.2.1, fun w => (evalInterp_holds_iff_denoteBasedInterp w _ hfe).symm.trans
        ((he.2.2 ()).trans (evalInterp_holds_iff_denoteBasedInterp w _ hfe'))⟩
    · exact ⟨he.1, he.2.1, fun w h => (evalInterp_holds_iff_denoteBasedInterp w _ hfe').1
        (he.2.2 () ((evalInterp_holds_iff_denoteBasedInterp w _ hfe).2 h))⟩
    · exact ⟨he.1, he.2.1, fun w => (evalInterp_holds_iff_denoteBasedInterp w _ hfe).symm.trans
        ((he.2.2 ()).trans (evalInterp_holds_iff_denoteBasedInterp w _ hfe'))⟩
  | dropAssume _ ih => exact .dropAssume (ih (fun ev hev => hs ev (List.mem_cons_of_mem _ hev)) ht)

end Core.Logic

end -- public section
