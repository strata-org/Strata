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

public theorem List.inj_implies_nodup {α} (l : List α)
  (p : ∀(i j : Nat) (p : i < l.length) (q : j < l.length), l[i] = l[j] → i = j)  :
     l.Nodup := by
  induction l with
  | nil => exact List.nodup_nil
  | cons h l ind =>
    rw [List.nodup_cons]
    constructor
    · intro hmem
      rw [List.mem_iff_getElem] at hmem
      obtain ⟨k, hk, hval⟩ := hmem
      have := p 0 (k + 1) (by simp) (by simp [hk]) (by simp [hval])
      omega
    · exact ind (fun i j hi hj heq => by
        have := p (i + 1) (j + 1) (by simp [hi]) (by simp[hj]) (by simpa using heq)
        omega)

/-- An element's measure is bounded by the sum of the mapped measures. -/
public theorem List.sum_size_le (f : α → Nat) {l : List α} {x : α} (x_in : x ∈ l) :
    f x ≤ List.sum (l.map f) := by
  induction l; simp_all; grind
