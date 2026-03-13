/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Laurel.LaurelDenote
import Strata.Languages.Laurel.LaurelSemanticsProps

/-!
# Bridging Lemmas: Computable Helpers ↔ Inductive Relations

Forward (soundness): computable helper returns `some` → inductive relation holds.
Backward (completeness): inductive relation holds → computable helper returns `some`.
-/

namespace Strata.Laurel

/-! ## UpdateStore -/

theorem updateStore_sound {σ σ' : LaurelStore} {x : Identifier} {v : LaurelValue} :
    updateStore σ x v = some σ' → UpdateStore σ x v σ' := by
  intro h
  simp [updateStore] at h
  split at h <;> simp at h
  next v' hsome =>
    subst h
    exact .update hsome
      (by simp)
      (fun y hne => by simp [Ne.symm hne])

theorem updateStore_complete {σ σ' : LaurelStore} {x : Identifier} {v : LaurelValue} :
    UpdateStore σ x v σ' → updateStore σ x v = some σ' := by
  intro h
  cases h with
  | update hold hnew hrest =>
    simp [updateStore, hold]
    funext y
    by_cases heq : y = x
    · subst heq; simp; exact hnew.symm
    · simp [heq]; exact (hrest y (Ne.symm heq)).symm

/-! ## InitStore -/

theorem initStore_sound {σ σ' : LaurelStore} {x : Identifier} {v : LaurelValue} :
    initStore σ x v = some σ' → InitStore σ x v σ' := by
  intro h
  simp [initStore] at h
  split at h <;> simp at h
  next hnone =>
    subst h
    exact .init hnone
      (by simp)
      (fun y hne => by simp [Ne.symm hne])

theorem initStore_complete {σ σ' : LaurelStore} {x : Identifier} {v : LaurelValue} :
    InitStore σ x v σ' → initStore σ x v = some σ' := by
  intro h
  cases h with
  | init hnone hnew hrest =>
    simp [initStore, hnone]
    funext y
    by_cases heq : y = x
    · subst heq; simp; exact hnew.symm
    · simp [heq]; exact (hrest y (Ne.symm heq)).symm

/-! ## findSmallestFree specification -/

/-- `findSmallestFree` starting from offset `n` returns the smallest `addr ≥ n`
such that `h addr = none`, provided all addresses in `[n, addr)` are occupied
and `addr - n ≤ bound`. -/
private theorem findSmallestFree_offset {h : LaurelHeap} {n addr : Nat} {bound : Nat}
    (hfree : h addr = none)
    (hbelow : ∀ a, n ≤ a → a < addr → (h a).isSome)
    (hle : n ≤ addr)
    (hbound : addr - n ≤ bound) :
    findSmallestFree h n bound = addr := by
  induction bound generalizing n with
  | zero =>
    have : n = addr := by omega
    subst this; simp [findSmallestFree]
  | succ b ih =>
    simp [findSmallestFree]
    split
    next v hsome =>
      have hne : n ≠ addr := by intro heq; subst heq; simp [hfree] at hsome
      exact ih
        (fun a ha1 ha2 =>
          if heq : a = n then by subst heq; simp [hsome]
          else hbelow a (by omega) ha2)
        (by omega)
        (by omega)
    next hnone =>
      have : ¬ (n < addr) := by
        intro hlt
        exact absurd (hbelow n (Nat.le_refl n) hlt) (by simp [hnone])
      omega

theorem findSmallestFree_spec {h : LaurelHeap} {addr : Nat}
    (hfree : h addr = none)
    (hbelow : ∀ a, a < addr → (h a).isSome)
    (hbound : addr ≤ 10000 := by omega) :
    findSmallestFree h 0 = addr := by
  exact findSmallestFree_offset hfree (fun a _ ha => hbelow a ha) (by omega) (by omega)

/-! ## findSmallestFree properties -/

private theorem findSmallestFree_finds_free (h : LaurelHeap) (n : Nat) (bound : Nat)
    (hexists : ∃ k, k ≤ bound ∧ h (n + k) = none) :
    h (findSmallestFree h n bound) = none := by
  induction bound generalizing n with
  | zero =>
    obtain ⟨k, hk, hfree⟩ := hexists
    have : k = 0 := by omega
    subst this; simpa [findSmallestFree] using hfree
  | succ b ih =>
    simp [findSmallestFree]
    split
    next v hsome =>
      apply ih
      obtain ⟨k, hk, hfree⟩ := hexists
      have hk0 : k ≠ 0 := by
        intro heq; subst heq; simp at hfree; rw [hfree] at hsome; simp at hsome
      refine ⟨k - 1, by omega, ?_⟩
      have : n + 1 + (k - 1) = n + k := by omega
      rw [this]; exact hfree
    next hn => exact hn

private theorem findSmallestFree_below_occupied (h : LaurelHeap) (n : Nat) (bound : Nat) :
    ∀ a, n ≤ a → a < findSmallestFree h n bound → (h a).isSome := by
  induction bound generalizing n with
  | zero => simp [findSmallestFree]; intro a h1 h2; omega
  | succ b ih =>
    simp [findSmallestFree]
    split
    next v hsome =>
      intro a ha1 ha2
      if heq : a = n then subst heq; simp [hsome]
      else exact ih (n + 1) a (by omega) ha2
    next => intro a h1 h2; omega

/-! ## AllocHeap -/

theorem allocHeap_sound {h : LaurelHeap} {typeName : Identifier}
    {addr : Nat} {h' : LaurelHeap}
    (hexists : ∃ k : Nat, k ≤ 10000 ∧ h k = none) :
    allocHeap h typeName = some (addr, h') → AllocHeap h typeName addr h' := by
  intro heq
  simp [allocHeap] at heq
  obtain ⟨ha, hh⟩ := heq
  subst ha; subst hh
  have haddr : h (findSmallestFree h 0 10000) = none := by
    apply findSmallestFree_finds_free
    obtain ⟨k, hk, hfree⟩ := hexists
    exact ⟨k, hk, by simpa using hfree⟩
  have hmin := findSmallestFree_below_occupied h 0 10000
  refine .alloc haddr (fun a ha => hmin a (by omega) ha) ?_ ?_
  · simp
  · intro a hne; simp [Ne.symm hne]

theorem allocHeap_complete {h h' : LaurelHeap} {typeName : Identifier} {addr : Nat}
    (hbound : addr ≤ 10000 := by omega) :
    AllocHeap h typeName addr h' → allocHeap h typeName = some (addr, h') := by
  intro halloc
  cases halloc with
  | alloc hfree hmin hnew hrest =>
    simp [allocHeap]
    have hfsf := findSmallestFree_spec hfree hmin hbound
    constructor
    · exact hfsf
    · funext a
      by_cases heq : a = addr
      · subst heq; simp [hfsf]; exact hnew.symm
      · have : a ≠ findSmallestFree h 0 := by rw [hfsf]; exact heq
        simp [this]; exact (hrest a (Ne.symm heq)).symm

/-! ## HeapFieldWrite -/

theorem heapFieldWrite_sound {h h' : LaurelHeap} {addr : Nat}
    {field : Identifier} {v : LaurelValue} :
    heapFieldWrite' h addr field v = some h' → HeapFieldWrite h addr field v h' := by
  intro heq
  simp [heapFieldWrite'] at heq
  split at heq <;> simp at heq
  next tag fields hsome =>
    subst heq
    refine .write hsome ?_ ?_
    · simp
    · intro a hne; simp [Ne.symm hne]

theorem heapFieldWrite_complete {h h' : LaurelHeap} {addr : Nat}
    {field : Identifier} {v : LaurelValue} :
    HeapFieldWrite h addr field v h' → heapFieldWrite' h addr field v = some h' := by
  intro hw
  cases hw with
  | write hlook hnew hrest =>
    simp [heapFieldWrite', hlook]
    funext a
    by_cases heqa : a = addr
    · subst heqa; simp
      rw [hnew]; congr 1; congr 1; funext f; simp [beq_iff_eq]
    · simp [heqa]; exact (hrest a (Ne.symm heqa)).symm

end Strata.Laurel
