/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Core.Analysis.DeductiveVerification
public import Strata.Languages.Core.Analysis.ProcedureCorrectnessProps
public import Strata.DL.Imperative.Analysis.DeductiveVerificationProps
public import Strata.DL.Imperative.Analysis.DefinitionsProps

/-! # Deductive verification of Core programs: properties

## Key results

- `Analysis.isDeductiveVerifier_pipelineVerify` — a pipeline of phases that each
  overapproximate the runs of every entry point, followed by a deductive
  verifier, is a deductive verifier.
- `Analysis.PhaseOverapproximates.preservesDeductiveVerification` — such a
  phase meets `PhasePreservesDeductiveVerification`, the per-phase hypothesis of
  `CoreVerifyIsDeductive`.
- `evalInterp_holds_iff_denoteBasedInterp` — for a condition captured under a
  runtime factory over `F`, the reading of `DeductiveVerificationOnCore` agrees
  with `DenoteBasedInterp F` in every world.
-/

public section

namespace Core.Specification

open Core Core.Logic Imperative Strata.Logic Imperative.Logic

/-- For a condition captured under a runtime factory over `F`, reading it under its own
    runtime factory (`Imperative.BigStep.evalInterp`) agrees with `DenoteBasedInterp F` in
    every world. -/
theorem evalInterp_holds_iff_denoteBasedInterp {F : Lambda.Factory Core.CoreLParams}
    (w : (DenoteBasedInterp F).World) (c : Imperative.EventArg Expression)
    (hc : c.factory.factory = F) :
    (Imperative.BigStep.evalInterp : ConditionInterp Expression).holds () c ↔
      (DenoteBasedInterp F).holds w c := by
  simp [Imperative.BigStep.evalInterp, DenoteBasedInterp, hc]

/-! ## Pipelines of overapproximating phases -/

namespace Analysis

/-- `vcResultsVerdict` claims only `valid` or `unknown`, so reading it back
    through `keepValid` changes nothing. -/
private theorem vcResultsVerdict_keepValid {E : Type _} {E' : Type _} (results : VCResults)
    (a : Imperative.AssertId Expression) :
    (vcResultsVerdict (Entry := E) results a).keepValid = vcResultsVerdict (Entry := E') results a := by
  unfold vcResultsVerdict
  split <;> rfl

/-- The empty result array reports `unknown` for every assertion. -/
private theorem vcResultsVerdict_empty {E : Type _} (a : Imperative.AssertId Expression) :
    vcResultsVerdict (Entry := E) #[] a = .unknown none := by
  simp [vcResultsVerdict]

/-- Validity reflection composed with itself is validity reflection. -/
private theorem validityReflected_comp
    {t t' : List (Event Expression)}
    (h : RComp (Strata.Analysis.ValidityReflected Imperative.BigStep.evalInterp)
      (Strata.Analysis.ValidityReflected Imperative.BigStep.evalInterp) t t') :
    Strata.Analysis.ValidityReflected Imperative.BigStep.evalInterp t t' :=
  RComp.collapse (Strata.Analysis.ValidityReflected.trans _) (fun _ _ h => h) (fun _ _ h => h) h

/-- The identity pipeline overapproximates. -/
private theorem phaseOverapproximates_some :
    PhaseOverapproximates (fun p p' => some p = some p') := by
  intro p p' h w hw
  cases h
  exact ⟨w, rfl, hw,
    EventLang.RunsOverapproximate.refl (Strata.Analysis.ValidityReflected.refl _) _⟩

/-- Running phases that each overapproximate overapproximates. -/
private theorem phaseOverapproximates_runPhases :
    ∀ phases : List (Program → Option Program),
      (∀ phase ∈ phases, PhaseOverapproximates (fun p p' => phase p = some p')) →
      PhaseOverapproximates (fun p p' => runPhases phases p = some p')
  | [], _ => phaseOverapproximates_some
  | phase :: rest, h => by
    intro p p'' hrun w hw
    simp only [runPhases, Option.bind_eq_some_iff] at hrun
    obtain ⟨p', hphase, hrest⟩ := hrun
    obtain ⟨w', hname', hw', hover⟩ :=
      h phase (List.mem_cons_self ..) p p' hphase w hw
    obtain ⟨w'', hname'', hw'', hover'⟩ :=
      phaseOverapproximates_runPhases rest (fun q hq => h q (List.mem_cons_of_mem _ hq))
        p' p'' hrest w' hw'
    exact ⟨w'', hname''.trans hname', hw'',
      (hover.trans hover').mono fun _ _ h => validityReflected_comp h⟩

/-- Deductive verification of the program a phase produces is deductive
    verification of its input, when the phase overapproximates. -/
private theorem deductiveVerificationOnCore_of_overapproximates
    {R : Program → Program → Prop}
    (h : PhaseOverapproximates R) {p p' : Program} (hR : R p p')
    {entryPoints : List String} {results : VCResults}
    (hdv : DeductiveVerificationOnCore ⟨entryPoints, p'⟩ results) :
    DeductiveVerificationOnCore ⟨entryPoints, p⟩ results := by
  have hv := Strata.Analysis.DeductiveVerification.of_runsOverapproximate
    (E₁ := coreEntries) (E₂ := coreEntries)
    (p₁ := (⟨entryPoints, p⟩ : CoreVerifierInput)) (p₂ := (⟨entryPoints, p'⟩ : CoreVerifierInput))
    (fun w ⟨hmem, hw⟩ => by
      obtain ⟨w', hname, hw', hover⟩ := h p p' hR w hw
      refine ⟨w', ⟨hname ▸ hmem, hw'⟩, ?_⟩
      exact hover)
    (fun _ _ h => h) hdv
  simp only [vcResultsVerdict_keepValid] at hv
  exact hv

/-- **A phase that overapproximates the runs of every entry point preserves
    deductive verification backwards.** -/
theorem PhaseOverapproximates.preservesDeductiveVerification {phase : PipelinePhase}
    (h : PhaseOverapproximates phase.Transforms) :
    PhasePreservesDeductiveVerification phase :=
  fun _ _ ht _ _ => deductiveVerificationOnCore_of_overapproximates h ht

/-- **A pipeline of overapproximating phases followed by a deductive verifier is
    a deductive verifier.** Each `valid` verdict the final phase reports holds
    on every bounded run of the transformed program, and every run of the
    original has a transformed run whose validity implies its own. -/
theorem isDeductiveVerifier_pipelineVerify
    (phases : List (Program → Option Program)) (vcg : CoreVerifierInput → VCResults)
    (hphases : ∀ phase ∈ phases, PhaseOverapproximates (fun p p' => phase p = some p'))
    (hvcg : IsDeductiveVerifier vcg) :
    IsDeductiveVerifier (pipelineVerify phases vcg) := by
  intro input
  unfold pipelineVerify
  cases hrun : runPhases phases input.prog with
  | none =>
    intro a
    rw [vcResultsVerdict_empty]
    trivial
  | some p' =>
    exact deductiveVerificationOnCore_of_overapproximates
      (phaseOverapproximates_runPhases phases hphases) hrun (hvcg ⟨input.entryPoints, p'⟩)

end Analysis

end Core.Specification

end -- public section
