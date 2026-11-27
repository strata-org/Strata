/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Util.DecidableEq
import all Strata.Util.DecidableEq

/-!
## Properties of the decidable-equality utilities

Key results:

- `ptrFastEq_eq` / `ptrFastEq_self` — the pointer-accelerated equality test
  decides equality: a `true` answer proves its arguments equal, and every
  value compares equal to itself.
- `ptrFastEq_eq_decide` — the pointer-accelerated test is `decide` of equality.
-/

public section

/-- A `true` answer from the pointer-accelerated test proves its arguments are
    equal. The pointer fast path cannot report equality where there is none. -/
theorem ptrFastEq_eq {α : Type u} [DecidableEq α] {x y : α}
    (h : ptrFastEq x y = true) : x = y :=
  @of_decide_eq_true (x = y) (withPtrEqDecEq x y fun _ => inferInstance) h

/-- Every value compares equal to itself. -/
theorem ptrFastEq_self {α : Type u} [DecidableEq α] (x : α) : ptrFastEq x x = true :=
  @decide_eq_true (x = x) (withPtrEqDecEq x x fun _ => inferInstance) rfl

/-- The pointer-accelerated equality test returns the same answer as deciding equality. -/
theorem ptrFastEq_eq_decide {α : Type u} [DecidableEq α] (x y : α) :
    ptrFastEq x y = decide (x = y) := by
  by_cases h : x = y
  · simp [h, ptrFastEq_self]
  · simp [h, Bool.eq_false_iff.2 (h ∘ ptrFastEq_eq)]

end
