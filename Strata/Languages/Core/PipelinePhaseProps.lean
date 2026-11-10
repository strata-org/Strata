/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Core.PipelinePhase
public import Strata.Languages.Core.ProgramFactProps
public import Strata.Languages.Core.ProgramFactSetProps

/-! # Properties of pipeline phases

Key results:

* `PipelinePhase.missingRequires_eq_nil_iff` — the diagnostic reports
  nothing missing exactly when the phase may run.
* `PipelinePhase.transforms_iff_runs` — a phase transforms `p` into `p'` exactly when
  it runs from some state to some state.

What the facts themselves mean on a program lives in
`ProgramFactProps.lean` and `ProgramFactSetProps.lean`, which this module re-exports. -/

namespace Core

public section

/-- The diagnostic reports nothing missing exactly when the phase may
    run. -/
theorem PipelinePhase.missingRequires_eq_nil_iff {p : PipelinePhase} {σ : ProgramFactSet} :
    p.missingRequires σ = [] ↔ p.requires ⊑ σ := by
  simp [PipelinePhase.missingRequires, Strata.Pipeline.missingFacts_eq_nil_iff]

/-- A phase run hides its states in `PipelinePhase.Transforms`. -/
theorem PipelinePhase.transforms_iff_runs {phase : PipelinePhase}
    {p p' : Program} : phase.Transforms p p' ↔ ∃ s s', phase.Runs s p s' p' := by
  constructor
  · rintro ⟨s, changed, s', h⟩; exact ⟨s, s', changed, h⟩
  · rintro ⟨s, s', changed, h⟩; exact ⟨s, changed, s', h⟩

end -- public section

end Core
