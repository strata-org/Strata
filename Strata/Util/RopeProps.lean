/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Util.Rope

/-! # Properties of ropes

The elements of a rope (`Rope.toList`) of the empty rope, of a one-element rope, of a
concatenation and of a fold of concatenations, and when a rope or a concatenation is empty.

Key theorems: `Rope.toList_nil`, `Rope.toList_one`, `Rope.toList_app`, `Rope.toList_foldl_app`,
`Rope.isNil_toList`, `Rope.isNil_app'`. -/

namespace Strata.Util

public section

/-- The elements of a rope, by structural recursion. -/
private def Rope.elems {α : Type} : Rope α → List α
  | .nil => []
  | .one a => [a]
  | .cat a b => a.elems ++ b.elems

/-- The work-list traversal prepends the elements of the ropes of the work list, the first
    rope rightmost. -/
private theorem Rope.toListAux_eq {α : Type} (st : List (Rope α)) (acc : List α) :
    Rope.toListAux st acc = st.reverse.flatMap Rope.elems ++ acc := by
  fun_induction Rope.toListAux <;> simp_all [Rope.elems]

/-- The empty rope has no elements. -/
theorem Rope.toList_nil {α : Type} : (Rope.nil : Rope α).toList = [] := by
  simp [Rope.toList, Rope.toListAux]

/-- A one-element rope has that element. -/
theorem Rope.toList_one {α : Type} (a : α) : (Rope.one a).toList = [a] := by
  simp [Rope.toList, Rope.toListAux]

/-- `Rope.app` concatenates the elements of its operands. -/
theorem Rope.toList_app {α : Type} (a b : Rope α) : (a.app b).toList = a.toList ++ b.toList := by
  cases a <;> cases b <;> simp [Rope.toList, Rope.toListAux_eq, Rope.elems, Rope.app]

/-- A rope built only from `nil` has no elements. -/
theorem Rope.isNil_toList {α : Type} {s : Rope α} (h : s.isNil = true) : s.toList = [] := by
  cases s <;> simp_all [Rope.isNil, Rope.toList_nil]

/-- Folding `Rope.app` over a list of ropes appends their elements in order. -/
theorem Rope.toList_foldl_app {α : Type} (l : List (Rope α)) (s : Rope α) :
    (l.foldl Rope.app s).toList = s.toList ++ l.flatMap Rope.toList := by
  induction l generalizing s <;> simp_all [Rope.toList_app]

/-- A concatenation is empty exactly when both operands are. -/
theorem Rope.isNil_app' {α : Type} (a b : Rope α) :
    (a.app b).isNil = (a.isNil && b.isNil) := by cases a <;> cases b <;> rfl

end -- public section

end Strata.Util
