/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Core.PipelineUnitChain
public import Strata.Languages.Core.PipelinePhaseUnits

/-! # Pipeline run records

Key definition: `RunRecords`, the description of a run of the pipeline phases by one
record (`PhaseRecord`: phase, input program, output program) per executed phase. -/

namespace Core

public section

/-- The records of a run of `phases` from `p` that has reached program `cur` with carriers
    `links`: one record per executed phase, chained from `p` to `cur`, each a successful run of
    its phase. -/
@[expose] def RunRecords (p : Program) (phases : List PipelinePhase) (cur : Program)
    (links : List RuntimeBackLink) (records : List PhaseRecord) : Prop :=
  links = records.map PhaseRecord.link ∧ PhaseRecord.Chained records ∧
    (∀ r ∈ records.head?, r.input = p) ∧ (records.getLast?.map (·.output)).getD p = cur ∧
    ∀ r ∈ records, r.phase ∈ phases ∧ r.phase.Produces r.input r.output

end -- public section

end Core
