/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.DL.Imperative.PathConditionHolds

/-!
## Properties of `PathConditions.Holds`

- `PathConditions.Holds.filter` — leaving entries out of a path condition (as relevance pruning
  leaves out axioms) is a weakening
-/

namespace Imperative

public section

/-- **Leaving entries out of a path condition is a weakening.** A store where every entry of
`pcs` holds is one where every entry `p` keeps holds. So a goal valid under the kept entries,
for instance with the axioms that relevance pruning drops left out, is valid under all of them. -/
theorem PathConditions.Holds.filter {P : PureExpr} [HasBool P] {f : P.Factory}
    {σ : SemanticStore P} {pcs : PathConditions P} (h : PathConditions.Holds f σ pcs)
    (p : PathConditionEntry P → Bool) :
    PathConditions.Holds f σ (pcs.map (·.filter p)) := by
  intro pc hpc e he
  obtain ⟨pc', hpc', rfl⟩ := List.mem_map.1 hpc
  exact h pc' hpc' e (List.mem_filter.1 he).1

end

end Imperative
