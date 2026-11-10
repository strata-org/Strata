/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Util.LeftistHeap

/-! # Properties of leftist heaps

The elements of a merge are those of its operands (`LeftistHeap.mem_merge`), and merging keeps
heaps ordered (`LeftistHeap.ord_merge`); removing the largest elements equal to `k` keeps a heap
ordered, removes no other element and, from a heap bounded by `k`, leaves elements below `k`
(`LeftistHeap.popEq_facts`, `LeftistHeap.mem_popEq`); the largest element bounds the elements of
an ordered heap (`LeftistHeap.le_max`, `LeftistHeap.max?_mem`).

Key theorems: `LeftistHeap.mem_merge`, `LeftistHeap.ord_merge`, `LeftistHeap.popEq_facts`,
`LeftistHeap.le_max`. -/

namespace Strata.Util

public section

namespace LeftistHeap

/-- The elements of a merge are those of its operands. -/
theorem mem_merge : ∀ (a b : LeftistHeap) (x : Nat),
    x ∈ (merge a b).elems ↔ x ∈ a.elems ∨ x ∈ b.elems := fun a b x => by
  fun_induction merge a b <;> grind [mk, elems]

/-- A merge of ordered heaps is ordered. -/
theorem ord_merge : ∀ (a b : LeftistHeap), a.Ord → b.Ord → (merge a b).Ord :=
  fun a b ha hb => by fun_induction merge a b <;> grind [Ord, elems, mem_merge, mk]

/-- Removing the top elements equal to `k` keeps an ordered heap ordered and removes no other
    element, and of an ordered heap bounded by `k` leaves elements below `k` only. -/
theorem popEq_facts (k : Nat) : ∀ h : LeftistHeap, h.Ord →
    (popEq k h).Ord ∧ (∀ x ∈ (popEq k h).elems, x ∈ h.elems) ∧
      ((∀ x ∈ h.elems, x ≤ k) → ∀ x ∈ (popEq k h).elems, x < k) := fun h => by
  fun_induction popEq k h <;> grind [Ord, elems, mem_merge, ord_merge, List.mem_cons_self]

/-- Removing the top elements equal to `k` keeps every other element. -/
theorem mem_popEq (k : Nat) : ∀ (h : LeftistHeap) (x : Nat), x ∈ h.elems →
    x ≠ k → x ∈ (popEq k h).elems := fun h x => by
  fun_induction popEq k h <;> grind [elems, mem_merge]

/-- An element of an ordered heap is at most its largest element. -/
theorem le_max {h : LeftistHeap} (ho : h.Ord) {x : Nat} (hx : x ∈ h.elems) :
    ∃ K, h.max? = some K ∧ x ≤ K := by
  cases h with
  | empty => cases hx
  | node r v l q => exact ⟨v, rfl, by grind [Ord, elems]⟩

/-- The largest element of a heap is an element. -/
theorem max?_mem {h : LeftistHeap} {t : Nat} (ht : h.max? = some t) :
    t ∈ h.elems := by cases h <;> grind [max?, elems]

end LeftistHeap

end -- public section

end Strata.Util
