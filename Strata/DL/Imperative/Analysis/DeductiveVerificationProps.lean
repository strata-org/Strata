/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.DL.Imperative.Analysis.DeductiveVerification
public import Strata.DL.Imperative.Analysis.VerdictProps
public import Strata.DL.Imperative.Analysis.Definitions

/-! # Deductive verification: properties

## Key results

- `DeductiveVerification.of_runsOverapproximate`: a deductive-verification
  report for a program whose runs, from each entry, overapproximate the
  original's up to a validity-reflecting relation is, once its non-`valid`
  verdicts become `unknown`, one for the original.
-/

public section

namespace Strata.Analysis

open Imperative Strata.Logic

variable {P : PureExpr}

/-- **A deductive-verification report for an overapproximating program gives
    one for the original**, keeping its `valid` verdicts and turning the others
    into `unknown`. Every entry of the original has an entry of the transformed
    program whose runs overapproximate its own. A `valid` verdict holds on
    every run from that entry, and every run of the original has a transformed
    run whose validity implies its own. -/
theorem DeductiveVerification.of_runsOverapproximate {Idx₁ Idx₂ : Type}
    {EL₁ : Idx₁ → EventLang P (Event P)} {EL₂ : Idx₂ → EventLang P (Event P)}
    {I : ConditionInterp P} {E₁ : ProgramEntries EL₁} {E₂ : ProgramEntries EL₂}
    {p₁ : E₁.Program} {p₂ : E₂.Program} {R : Relation (Trace P)}
    {report : AssertId P → Verdict E₂.Entry}
    (hover : ∀ e₁, E₁.entries p₁ e₁ → ∃ e₂, E₂.entries p₂ e₂ ∧
      (EL₁ (E₁.start p₁ e₁).1).RunsOverapproximate R (EL₂ (E₂.start p₂ e₂).1)
        (E₁.start p₁ e₁).2 (E₂.start p₂ e₂).2)
    (hR : ∀ t t', R t t' → ValidityReflected I t t')
    (hdv : DeductiveVerification I E₂ p₂ report) :
    DeductiveVerification I E₁ p₁ (fun a => (report a).keepValid) := by
  intro a
  have hc := hdv a
  show VerdictCorrect I E₁ p₁ a (report a).keepValid
  cases hr : report a with
  | valid =>
    rw [hr] at hc
    intro e₁ he₁ n trace ⟨c, h⟩
    obtain ⟨e₂, he₂, hov⟩ := hover e₁ he₁
    obtain ⟨m, trace', c', h', hv⟩ := hov n trace c h
    exact hR _ _ hv a (hc e₂ he₂ m trace' ⟨c', h'⟩)
  | unknown _ | failed _ => exact trivial

end Strata.Analysis

end -- public section
