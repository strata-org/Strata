/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Transform.UnrollBoundedQuantifiers
import all Strata.Transform.UnrollBoundedQuantifiers

/-! # Properties of bounded-quantifier unrolling

- `Stats.mem_all`: `Stats.all` lists every counter the pass reports.

A placeholder: it proves that one property, not (yet) that the rewrite preserves models.
-/

namespace Core.UnrollBoundedQuantifiers

/-- `Stats.all` misses no counter; a counter added without extending it fails here. -/
theorem Stats.mem_all (s : Stats) : s ∈ Stats.all := by
  cases s
  case ineligible k => cases k <;> simp [Stats.all, BinderKind.all]
  all_goals simp [Stats.all, BinderKind.all]

end Core.UnrollBoundedQuantifiers
