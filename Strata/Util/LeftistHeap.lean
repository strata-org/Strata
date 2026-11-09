/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Init

/-! # Leftist heaps of natural numbers

A leftist max-heap of natural numbers: the largest element is at the root (`LeftistHeap.max?`),
two heaps merge in logarithmic time (`LeftistHeap.merge`), and the largest elements equal to a
given number are removed together (`LeftistHeap.popEq`).

Key definitions: `LeftistHeap`, `LeftistHeap.merge`, `LeftistHeap.single`, `LeftistHeap.max?`,
`LeftistHeap.popEq`. -/

namespace Strata.Util

public section

/-- A leftist max-heap of natural numbers. -/
inductive LeftistHeap where
  | empty
  | node (rank : Nat) (v : Nat) (l r : LeftistHeap)
  deriving Inhabited

namespace LeftistHeap

/-- The rank of a heap: the length of its right spine. -/
@[expose] def rank : LeftistHeap → Nat
  | .empty => 0
  | .node r _ _ _ => r

/-- The number of elements of a heap. -/
@[expose] def size : LeftistHeap → Nat
  | .empty => 0
  | .node _ _ l r => size l + size r + 1

/-- A node with the higher-ranked child on the left. -/
@[expose] def mk (v : Nat) (a b : LeftistHeap) : LeftistHeap :=
  if b.rank ≤ a.rank then .node (b.rank + 1) v a b else .node (a.rank + 1) v b a

/-- The union of two heaps, in O(log n). -/
@[expose] def merge : LeftistHeap → LeftistHeap → LeftistHeap
  | .empty, h => h
  | h, .empty => h
  | .node r1 v1 l1 q1, .node r2 v2 l2 q2 =>
    if v2 ≤ v1 then mk v1 l1 (merge q1 (.node r2 v2 l2 q2))
    else mk v2 l2 (merge (.node r1 v1 l1 q1) q2)
  termination_by a b => a.size + b.size
  decreasing_by all_goals simp only [size]; omega

/-- The one-element heap. -/
@[expose] def single (v : Nat) : LeftistHeap := .node 1 v .empty .empty

/-- The largest element. -/
@[expose] def max? : LeftistHeap → Option Nat
  | .empty => none
  | .node _ v _ _ => some v

/-- The heap built by `mk` from `v` and two heaps has one more element than the two together. -/
private theorem size_mk (v : Nat) (a b : LeftistHeap) : (mk v a b).size = a.size + b.size + 1 := by
  unfold mk; split <;> simp only [size] <;> omega

/-- Merging two heaps keeps all their elements: its size is the sum of their sizes. -/
private theorem size_merge :
    ∀ (a b : LeftistHeap), (merge a b).size = a.size + b.size := fun a b => by
  fun_induction merge a b <;> simp only [size, size_mk, *] <;> omega

/-- Remove the largest elements while they equal `k` (each element is removed once). -/
@[expose] def popEq (k : Nat) : LeftistHeap → LeftistHeap
  | .empty => .empty
  | .node r v l q =>
    if v = k then popEq k (merge l q) else .node r v l q
  termination_by h => h.size
  decreasing_by rw [size_merge]; simp only [size]; omega

end LeftistHeap

end -- public section

end Strata.Util
