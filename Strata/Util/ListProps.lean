/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Util.List

/-!
# Properties of `List` utilities

## Key theorems

* `List.length_eq_of_nodup_of_mem_iff` — two duplicate-free lists with the same
  membership have equal length.
-/

/-- Two duplicate-free lists with the same membership have equal length. -/
public theorem List.length_eq_of_nodup_of_mem_iff [BEq κ] [LawfulBEq κ]
    {l₁ l₂ : List κ}
    (d₁ : l₁.Nodup) (d₂ : l₂.Nodup) (hmem : ∀ a, a ∈ l₁ ↔ a ∈ l₂) :
    l₁.length = l₂.length := by
  have hperm : List.Perm l₁ l₂ := by
    rw [List.perm_iff_count]
    intro a
    rw [d₁.count, d₂.count]
    simp only [hmem a]
  exact hperm.length_eq
