/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
import all Strata.DDM.Util.List

set_option autoImplicit false

namespace Array

@[simp]
theorem anyM_empty {α m} [Monad m] (f : α → m Bool) (start : Nat := 0) (stop : Nat := 0)
  : Array.anyM f #[] start stop = @pure m _ _ false := by
  unfold Array.anyM
  split
  case isTrue stopLE =>
    have stopZero : stop = 0 := by simp at stopLE; omega
    unfold anyM.loop
    simp [stopZero]
  case isFalse stopGT =>
    unfold anyM.loop
    simp

private theorem extract_loop_succ_upper {α} (as b : Array α) (i j : Nat) (h : i + j < as.size) :
    Array.extract.loop as (i + 1) j b =
      (Array.extract.loop as i j b).push (as[i + j]'h) := by
  revert b j
  induction i
  case zero =>
    intro b i i_lt
    simp at i_lt
    simp [i_lt, extract.loop]
  case succ j hyp =>
    intro b i i_lt
    have g : i < as.size := by omega
    unfold extract.loop
    have h : j + (i + 1) < as.size := by omega
    have p : j + (i + 1) = j + 1 + i := by omega
    simp [g, hyp _ _ h, p]

private theorem extract_succ {α} (as : Array α) {i j : Nat} (g : i ≤ j) (h : j < as.size) : as.extract i (j + 1) = (as.extract i j).push (as[j]'h) := by
  have j1_le : (j + 1) ≤ as.size := by omega
  have j_le : j ≤ as.size := by omega
  have p : j + 1 - i = j - i + 1 := by omega
  have q : j - i + i = j := by omega
  simp [Array.extract, Nat.min_eq_left, j1_le, j_le, p, Array.extract_loop_succ_upper, q, h]

private theorem sizeOf_toList {α} [SizeOf α] (as : Array α) :
  sizeOf as = 1 + sizeOf as.toList := rfl

theorem sizeOf_min {α} [SizeOf α] (as : Array α) : sizeOf as ≥ 2 := by
  have p := sizeOf_toList as
  have q := List.sizeOf_pos as.toList
  omega

@[simp]
theorem sizeOf_push {α} [SizeOf α] (as : Array α) (a : α) :
  sizeOf (as.push a) = sizeOf as + sizeOf a + 1 := by
  simp [Array.push, sizeOf_toList]
  omega

@[simp]
theorem sizeOf_set {α} [SizeOf α] (a : Array α) (i : Nat) (v : α)  (hi : i < a.size) : sizeOf (a.set i v) = sizeOf a - sizeOf a[i] + sizeOf v := by
  match a with
  | .mk l =>
    unfold Array.set
    simp at hi
    simp [hi]
    have memLt : sizeOf l[i] < sizeOf l := List.sizeOf_get _ _
    omega

@[simp]
theorem sizeOf_swap {α} [h : SizeOf α] (a : Array α) (i : Nat) (j : Nat)  (hi : i < a.size) (hj : j < a.size) : sizeOf (a.swap i j) = sizeOf a := by
  unfold Array.swap
  have h : sizeOf a[i] < sizeOf a := sizeOf_getElem _ _ _
  simp [Array.getElem_set]
  omega

private theorem sizeOf_reverse_loop {α} [h : SizeOf α] (as : Array α) (i : Nat) (j : Fin as.size) : sizeOf (reverse.loop as i j) = sizeOf as := by
  unfold reverse.loop
  split
  case isTrue p =>
    apply Eq.trans (sizeOf_reverse_loop _ _ _)
    simp
  case isFalse p =>
    trivial
  termination_by j.val - i

@[simp]
theorem sizeOf_reverse {α} [SizeOf α] (a : Array α) : sizeOf a.reverse = sizeOf a := by
  unfold reverse
  split
  case isTrue p =>
    trivial
  case isFalse p =>
    simp [sizeOf_reverse_loop]

theorem sizeOf_lt_of_mem_strict {α} [SizeOf α] {a} {as : Array α} (h : a ∈ as) : sizeOf a + 3 ≤ sizeOf as := by
  cases as with | _ as =>
  simp +arith [List.sizeOf_lt_of_mem_strict h.val]

theorem mem_iff_back_or_pop {α} (a : α) {as : Array α} (p : as.size > 0 := by get_elem_tactic) :
  a ∈ as ↔ (a = as.back ∨ a ∈ as.pop) := by
  simp [Array.mem_iff_getElem]
  grind

theorem of_mem_pop {α} {a : α} {as : Array α} : a ∈ as.pop → a ∈ as := by
  simp [Array.mem_iff_getElem]
  grind

theorem mem_pop_ne {α} {a : α} {as : Array α} (ne : as.size > 0) :
    a ∈ as ↔ a ∈ as.pop ∨ a = as.back := by
  have as_ne : as ≠ #[] := Array.ne_empty_of_size_pos ne
  have ne' : as.toList ≠ [] :=
          as_ne ∘ Array.toList_eq_nil_iff.mp
  simp only [
    ← Array.mem_toList_iff,
    List.mem_ne_as_dropLast _ ne',
    Array.getLast_toList,
    Array.toList_pop
  ]

theorem size_filter_pos {α} {p : α → Bool} {as : Array α} {i : Nat}
   {h : i < as.size} (witness : p as[i] = true) : (Array.filter p as).size > 0 := by
  have as_eq : as.filter p = (as.set i as[i] h).filter p := by
    simp [Array.set_getElem_self]
  rw [as_eq]
  simp only [Array.set_eq_push_extract_append_extract]
  simp only [Array.filter_append, Array.size_append, Array.filter_push]
  simp [witness]
  omega

theorem size_filter_set {α} (p : α → Bool) (as : Array α) (i : Nat) (v : α)
          (h : i < as.size := by get_elem_tactic) : (Array.filter p (as.set i v)).size =
    (Array.filter p as).size
      + (if p v then 1 else 0)
      - (if p as[i] = true then 1 else 0) := by
  have as_eq : as.filter p = (as.set i as[i] h).filter p := by
    simp [Array.set_getElem_self]
  rw [as_eq]
  simp only [Array.set_eq_push_extract_append_extract]
  simp only [Array.filter_append, Array.size_append, Array.filter_push]
  if newp : p v = true then
    if oldp : p as[i] = true then
      simp [newp, oldp]
    else
      simp [newp, oldp]
      omega
  else
    if oldp : p as[i] = true then
      simp [newp, oldp]
    else
      simp [newp, oldp]

end Array
