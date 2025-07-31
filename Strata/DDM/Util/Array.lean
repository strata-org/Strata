/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.DDM.Util.List

namespace Array

@[simp]
theorem Array.anyM_empty {α} [Monad m] (f : α → m Bool) (start : Nat := 0) (stop : Nat := 0)
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

@[simp]
theorem Array.any_empty (f : α → Bool) (start : Nat := 0) (stop : Nat := 0)
  : Array.any #[] f start stop = false := by
    simp [Array.any]

def map_off {α β} (as : Array α) (f : α → β)
      (start : Nat := 0) (stop : Nat := as.size)
      (init : Array β := Array.mkEmpty ((min as.size stop) - start)) : Array β :=
  as.foldl (init := init) (start := start) (stop := stop)
           fun r e => r.push (f e)

def mapM_off {α β m} [Monad m] (as : Array α) (f : α → m β)
      (start : Nat := 0) (stop := as.size)
      (init : Array β := Array.mkEmpty ((min as.size stop) - start)) : m (Array β) :=
  as.foldlM (init := init) (start := start) (stop := stop)
            fun r e => r.push <$> f e

theorem extract_loop_succ_upper {α} (as b : Array α) (i j : Nat) (h : i + j < as.size) :
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

theorem extract_succ {α} (as : Array α) {i : Nat} (g : i ≤ j) (h : j < as.size) : as.extract i (j + 1) = (as.extract i j).push (as[j]'h) := by
  have j1_le : (j + 1) ≤ as.size := by omega
  have j_le : j ≤ as.size := by omega
  have p : j + 1 - i = j - i + 1 := by omega
  have q : j - i + i = j := by omega
  simp [Array.extract, Nat.min_eq_left, j1_le, j_le, p, Array.extract_loop_succ_upper, q, h]

theorem sizeOf_toList {α} [SizeOf α] (as : Array α) :
  sizeOf as = 1 + sizeOf as.toList := rfl

theorem sizeOf_min [SizeOf α] (as : Array α) : sizeOf as ≥ 2 := by
  have p := sizeOf_toList as
  have q := List.sizeOf_pos as.toList
  omega

@[simp]
theorem sizeOf_push {α} [SizeOf α] (as : Array α) (a : α) :
  sizeOf (as.push a) = sizeOf as + sizeOf a + 1 := by
  simp [Array.push, sizeOf_toList]
  omega

@[simp]
theorem sizeOf_set [SizeOf α] (a : Array α) (i : Nat) (v : α)  (hi : i < a.size) : sizeOf (a.set i v) = sizeOf a - sizeOf a[i] + sizeOf v := by
  match a with
  | .mk l =>
    unfold Array.set
    simp at hi
    simp [hi]
    have memLt : sizeOf l[i] < sizeOf l := List.sizeOf_get _ _
    omega

@[simp]
theorem sizeOf_swap [h : SizeOf α] (a : Array α) (i : Nat) (j : Nat)  (hi : i < a.size) (hj : j < a.size) : sizeOf (a.swap i j) = sizeOf a := by
  unfold Array.swap
  have h : sizeOf a[i] < sizeOf a := sizeOf_getElem _ _ _
  simp [Array.getElem_set]
  omega

private
theorem sizeOf_reverse_loop {α} [h : SizeOf α] (as : Array α) (i : Nat) (j : Fin as.size) : sizeOf (reverse.loop as i j) = sizeOf as := by
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

theorem sizeOf_lt_of_mem_strict [SizeOf α] {as : Array α} (h : a ∈ as) : sizeOf a + 3 ≤ sizeOf as := by
  cases as with | _ as =>
  simp +arith [List.sizeOf_lt_of_mem_strict h.val]

end Array
