/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/



/-
Taken from mathlib4
https://github.com/leanprover-community/mathlib4/blob/d7a4adb961ed411dbec6ff6857cfc771859ec83f/Mathlib/Data/List/Defs.lean#L131-L137
https://github.com/leanprover-community/mathlib4/blob/d7a4adb961ed411dbec6ff6857cfc771859ec83f/Mathlib/Data/List/Basic.lean#L1203-L1206
-/
def Forall (p : α → Prop) : List α → Prop
  | [] => True
  | x :: [] => p x
  | x :: l => p x ∧ Forall p l

class ListP {α : Type} (π : α → Prop) (πs : List α → Prop) where
  split : ∀ {a : α} , πs (a :: as) → π a ×' πs as

class Wrapper (α : Type) where
  self : α

open List

@[simp]
theorem forall_cons (p : α → Prop) (x : α) : ∀ l : List α, Forall p (x :: l) ↔ p x ∧ Forall p l
  | [] => (and_iff_left_of_imp fun _ ↦ trivial).symm
  | _ :: _ => Iff.rfl

theorem forall_iff_forall_mem : ∀ {l : List α}, Forall p l ↔ ∀ x ∈ l, p x
  | [] => (iff_true_intro <| forall_mem_nil _).symm
  | x :: l => by rw [List.forall_mem_cons, forall_cons, forall_iff_forall_mem]
