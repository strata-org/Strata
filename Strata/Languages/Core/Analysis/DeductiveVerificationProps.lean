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
-/

public section

namespace Core.Specification

open Core Core.Logic Imperative Strata.Logic Imperative.Logic

/-! ## Pipelines of overapproximating phases -/

namespace Analysis

/-- `vcResultsVerdict` claims only `valid` or `unknown`, so reading it back
    through `keepValid` changes nothing. -/
private theorem vcResultsVerdict_keepValid {E E' : Type} (results : VCResults)
    (a : Imperative.AssertId Expression) :
    (vcResultsVerdict (Entry := E) results a).keepValid = vcResultsVerdict (Entry := E') results a := by
  unfold vcResultsVerdict
  split <;> rfl

/-- The empty result array reports `unknown` for every assertion. -/
private theorem vcResultsVerdict_empty {E : Type} (a : Imperative.AssertId Expression) :
    vcResultsVerdict (Entry := E) #[] a = .unknown none := by
  simp [vcResultsVerdict]

/-- Validity reflection composed with itself is validity reflection. -/
private theorem validityReflected_comp (model : Lambda.Interp Core.Factory)
    {t t' : List (Event Expression)}
    (h : RComp (Strata.Analysis.ValidityReflected (DenoteBasedInterp model))
      (Strata.Analysis.ValidityReflected (DenoteBasedInterp model)) t t') :
    Strata.Analysis.ValidityReflected (DenoteBasedInterp model) t t' :=
  RComp.collapse (Strata.Analysis.ValidityReflected.trans _) (fun _ _ h => h) (fun _ _ h => h) h

/-- The identity pipeline overapproximates. -/
private theorem phaseOverapproximates_some :
    PhaseOverapproximates (fun p p' => some p = some p') := by
  intro p p' h w hw
  cases h
  exact ⟨w, rfl, hw, fun model =>
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
    exact ⟨w'', hname''.trans hname', hw'', fun model =>
      ((hover model).trans (hover' model)).mono fun _ _ h => validityReflected_comp model h⟩

/-- Deductive verification of the program a phase produces is deductive
    verification of its input, when the phase overapproximates. -/
private theorem deductiveVerificationOnCore_of_overapproximates
    {R : Program → Program → Prop}
    (h : PhaseOverapproximates R) {p p' : Program} (hR : R p p')
    {model : Lambda.Interp Core.Factory} {entryPoints : List String} {results : VCResults}
    (hdv : DeductiveVerificationOnCore model ⟨entryPoints, p'⟩ results) :
    DeductiveVerificationOnCore model ⟨entryPoints, p⟩ results := by
  have hv := Strata.Analysis.DeductiveVerification.of_runsOverapproximate
    (E₁ := coreEntries) (E₂ := coreEntries)
    (p₁ := (⟨entryPoints, p⟩ : CoreVerifierInput)) (p₂ := (⟨entryPoints, p'⟩ : CoreVerifierInput))
    (fun w ⟨hmem, hw⟩ => by
      obtain ⟨w', hname, hw', hover⟩ := h p p' hR w hw
      refine ⟨w', ⟨hname ▸ hmem, hw'⟩, ?_⟩
      exact hover model)
    (fun _ _ h => h) hdv
  simp only [vcResultsVerdict_keepValid] at hv
  exact hv

/-- **A phase that overapproximates the runs of every entry point preserves
    deductive verification backwards.** -/
theorem PhaseOverapproximates.preservesDeductiveVerification {phase : PipelinePhase}
    (h : PhaseOverapproximates phase.Transforms) :
    PhasePreservesDeductiveVerification phase :=
  fun _ _ ht _ _ _ => deductiveVerificationOnCore_of_overapproximates h ht

/-- **A pipeline of overapproximating phases followed by a deductive verifier is
    a deductive verifier.** Each `valid` verdict the final phase reports holds
    on every bounded run of the transformed program, and every run of the
    original has a transformed run whose validity implies its own. -/
theorem isDeductiveVerifier_pipelineVerify
    (phases : List (Program → Option Program)) (vcg : CoreVerifierInput → VCResults)
    (hphases : ∀ phase ∈ phases, PhaseOverapproximates (fun p p' => phase p = some p'))
    (hvcg : IsDeductiveVerifier vcg) :
    IsDeductiveVerifier (pipelineVerify phases vcg) := by
  intro model input
  unfold pipelineVerify
  cases hrun : runPhases phases input.prog with
  | none =>
    intro a
    rw [vcResultsVerdict_empty]
    trivial
  | some p' =>
    exact deductiveVerificationOnCore_of_overapproximates
      (phaseOverapproximates_runPhases phases hphases) hrun (hvcg model ⟨input.entryPoints, p'⟩)

end Analysis

end Core.Specification

end -- public section
