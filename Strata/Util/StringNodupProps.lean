/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Util.StringNodup
import all Strata.Util.StringNodup

/-! # Properties of the kernel-checkable duplicate check

Key theorems:
- `nodup_of_strictlyIncreasing_sortFuel`: a list of strings has no
  duplicates when the sorted byte codes of its elements are strictly
  increasing. -/

public section

namespace Strata.StringNodup

/-- Merging with any amount of fuel only reorders the two input lists. -/
private theorem mergeFuel_perm :
    ∀ (n : Nat) (xs ys : List Nat), (mergeFuel n xs ys).Perm (xs ++ ys)
  | 0, _, _ => List.Perm.refl _
  | _ + 1, [], _ => List.Perm.refl _
  | _ + 1, _ :: _, [] => by
    simp only [mergeFuel, List.append_nil]
    exact List.Perm.refl _
  | n + 1, x :: xs, y :: ys => by
    simp only [mergeFuel]
    cases Nat.ble x y
    · have hperm := mergeFuel_perm n (x :: xs) ys
      simp only [Bool.cond_false]
      exact (hperm.cons y).trans List.perm_middle.symm
    · have hperm := mergeFuel_perm n xs (y :: ys)
      simp only [Bool.cond_true, List.cons_append]
      exact hperm.cons x

/-- The two halves produced by `splitAlt` together hold exactly the
    elements of the input. -/
private theorem splitAlt_perm :
    ∀ l : List Nat, ((splitAlt l).1 ++ (splitAlt l).2).Perm l
  | [] => List.Perm.refl _
  | x :: t => by
    have ih := splitAlt_perm t
    simp only [splitAlt, List.cons_append]
    exact (List.perm_append_comm.trans ih).cons x

/-- Sorting with any amount of fuel only reorders the input. -/
private theorem sortFuel_perm :
    ∀ (n : Nat) (l : List Nat), (sortFuel n l).Perm l
  | 0, _ => List.Perm.refl _
  | n + 1, l => by
    have hsplit := splitAlt_perm l
    simp only [sortFuel]
    split
    · rename_i b heq
      rw [heq] at hsplit
      exact hsplit
    · rename_i a heq
      rw [heq, List.append_nil] at hsplit
      exact hsplit
    · rename_i a b _ _ heq
      rw [heq] at hsplit
      exact (mergeFuel_perm _ _ _).trans
        (((sortFuel_perm n a).append (sortFuel_perm n b)).trans hsplit)

/-- A list in which each element is smaller than the next is strictly
    increasing as a whole: every element is smaller than all later ones. -/
private theorem pairwise_lt_of_strictlyIncreasing :
    ∀ l : List Nat, strictlyIncreasing l = true → l.Pairwise (· < ·)
  | [], _ => List.Pairwise.nil
  | [_], _ => List.pairwise_singleton _ _
  | a :: b :: t, h => by
    simp only [strictlyIncreasing, Bool.and_eq_true, Nat.blt_eq] at h
    have hrest := pairwise_lt_of_strictlyIncreasing (b :: t) h.2
    refine List.Pairwise.cons ?_ hrest
    intro x hx
    rcases List.mem_cons.mp hx with hxb | hxt
    · omega
    · exact Nat.lt_trans h.1 (List.rel_of_pairwise_cons hrest hxt)

/-- A list of strings has no duplicates if the byte codes of its elements,
    once sorted, are strictly increasing. The hypothesis is a closed `Bool`
    computation meant to be discharged by `decide +kernel`, which needs
    `import all Strata.Util.StringNodup` to evaluate it. -/
theorem nodup_of_strictlyIncreasing_sortFuel (l : List String)
    (h : strictlyIncreasing (sortFuel l.length (l.map byteCode)) = true) :
    l.Nodup := by
  have hcodes : (l.map byteCode).Nodup :=
    (sortFuel_perm _ _).nodup_iff.mp
      ((pairwise_lt_of_strictlyIncreasing _ h).imp Nat.ne_of_lt)
  exact List.Pairwise.of_map (S := (· ≠ ·)) byteCode
    (fun _ _ hne heq => hne (congrArg byteCode heq)) hcodes

end Strata.StringNodup

end -- public section
