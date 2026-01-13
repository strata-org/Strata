/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
set_option autoImplicit false

namespace List

theorem sizeOf_pos {α} [SizeOf α] (l : List α) : sizeOf l > 0 := by
  match l with
  | [] => simp
  | h :: l => decreasing_tactic

@[simp]
theorem sizeOf_append {α} [SizeOf α] (k l : List α) :
  sizeOf (k ++ l) = sizeOf k + sizeOf l - 1 := by
  induction k
  case nil =>
    simp
  case cons h k ind =>
    have p := sizeOf_pos l
    decreasing_tactic

/--
This is similiar to `Array.sizeOf_lt_of_mem`, but stren
-/
theorem sizeOf_lt_of_mem_strict {α} [inst : SizeOf α] {as : List α} {a} (h : a ∈ as) : sizeOf a + 2 ≤ sizeOf as := by
  induction h with
  | head as =>
    have p := sizeOf_pos as
    decreasing_tactic
  | tail _ _ ih => exact Nat.lt_trans ih (by simp +arith)

@[simp]
theorem sizeOf_set {α} [h : SizeOf α] (as : List α) (i : Nat) (v : α)  :
    sizeOf (as.set i v) =
      if p : i < as.length then
        sizeOf as + sizeOf v - sizeOf as[i]
      else
        sizeOf as := by
  unfold List.set
  split
  case h_1 =>
    rename_i head as
    decreasing_tactic
  case h_2 =>
    rename_i b bs j
    simp [sizeOf_set _ j]
    split
    case isTrue jLt =>
      have h : sizeOf bs[j] < sizeOf bs := List.sizeOf_get _ _
      decreasing_tactic
    case isFalse jGe =>
      decreasing_tactic
  case h_3 =>
    simp

/--
Rewrites non-emptty list membership to drop last and get last.
-/
theorem mem_ne_as_dropLast {α} (a : α) {as : List α} (ne : as ≠ []) :
    a ∈ as ↔ a ∈ as.dropLast ∨ a = as.getLast ne :=
  match as with
  | []    => by
    simp at ne
  | [b]   => by
    simp
  | b0 :: b1 :: bs => by
    if h : a = b0 then
      simp [h]
    else
      have ne' : b1 :: bs ≠ [] := by simp
      have p := List.mem_ne_as_dropLast a ne'
      grind

end List
