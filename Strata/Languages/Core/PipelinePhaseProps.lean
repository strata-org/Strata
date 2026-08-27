/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Core.PipelinePhase
public import Strata.Languages.Core.ProgramFactProps
public import Strata.Languages.Core.ProgramFactSetProps

/-! # Properties of pipeline phases

Key result:

* `PipelinePhase.missingRequires_eq_nil_iff` — the diagnostic reports
  nothing missing exactly when the phase may run.

What the facts themselves mean on a program lives in
`ProgramFactProps.lean` and `ProgramFactSetProps.lean`, which this module re-exports. -/

namespace Core

public section

/-- The diagnostic reports nothing missing exactly when the phase may
    run. -/
theorem PipelinePhase.missingRequires_eq_nil_iff {p : PipelinePhase} {σ : ProgramFactSet} :
    p.missingRequires σ = [] ↔ p.requires ⊑ σ := by
  simp [PipelinePhase.missingRequires, Strata.Pipeline.missingFacts_eq_nil_iff]

end -- public section

end Core
