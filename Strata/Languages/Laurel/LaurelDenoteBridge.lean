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

## Assumptions

`heapFieldWrite_complete` relies on `Identifier` (= `String`) having a `BEq` instance
that agrees with `DecidableEq` (via `beq_iff_eq`). If `Identifier` ever receives a
non-standard `BEq`, that proof would need updating.
-/

namespace Strata.Laurel

/-! ## UpdateStore -/

theorem updateStore_sound {σ σ' : LaurelStore} {x : Identifier} {v : LaurelValue} :
    updateStore σ x v = some σ' → UpdateStore σ x.text v σ' := by
  intro h
  simp [updateStore] at h
  split at h <;> simp at h
  next v' hsome =>
    subst h
    exact .update hsome
      (by simp)
      (fun y hne => by simp [Ne.symm hne])

theorem updateStore_complete {σ σ' : LaurelStore} {x : Identifier} {v : LaurelValue} :
    UpdateStore σ x.text v σ' → updateStore σ x v = some σ' := by
  intro h
  cases h with
  | update hold hnew hrest =>
    simp [updateStore, hold]
    funext y
    by_cases heq : y = x.text
    · subst heq; simp; exact hnew.symm
    · simp [heq]; exact (hrest y (Ne.symm heq)).symm

/-! ## InitStore -/

theorem initStore_sound {σ σ' : LaurelStore} {x : Identifier} {v : LaurelValue} :
    initStore σ x v = some σ' → InitStore σ x.text v σ' := by
  intro h
  simp [initStore] at h
  split at h <;> simp at h
  next hnone =>
    subst h
    exact .init hnone
      (by simp)
      (fun y hne => by simp [Ne.symm hne])

theorem initStore_complete {σ σ' : LaurelStore} {x : Identifier} {v : LaurelValue} :
    InitStore σ x.text v σ' → initStore σ x v = some σ' := by
  intro h
  cases h with
  | init hnone hnew hrest =>
    simp [initStore, hnone]
    funext y
    by_cases heq : y = x.text
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
    (hbound : addr ≤ heapSearchBound := by simp [heapSearchBound]; omega) :
    findSmallestFree h 0 = addr := by
  have hb : addr ≤ heapSearchBound := hbound
  simp [heapSearchBound] at hb
  exact findSmallestFree_offset hfree (fun a _ ha => hbelow a ha) (by omega) (by simp [heapSearchBound]; omega)

/-! ## findSmallestFree properties -/

theorem findSmallestFree_finds_free (h : LaurelHeap) (n : Nat) (bound : Nat)
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

theorem findSmallestFree_below_occupied (h : LaurelHeap) (n : Nat) (bound : Nat) :
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

theorem allocHeap_sound {h : LaurelHeap} {typeName : String}
    {addr : Nat} {h' : LaurelHeap} :
    allocHeap h typeName = some (addr, h') → AllocHeap h typeName addr h' := by
  intro heq
  simp [allocHeap] at heq
  split at heq <;> simp at heq
  next hfree =>
    obtain ⟨ha, hh⟩ := heq
    subst ha; subst hh
    have hmin := findSmallestFree_below_occupied h 0 heapSearchBound
    refine .alloc hfree (fun a ha => hmin a (by omega) ha) ?_ ?_
    · simp
    · intro a hne; simp [Ne.symm hne]

theorem allocHeap_complete {h h' : LaurelHeap} {typeName : String} {addr : Nat}
    (hbound : addr ≤ heapSearchBound := by simp [heapSearchBound]; omega) :
    AllocHeap h typeName addr h' → allocHeap h typeName = some (addr, h') := by
  intro halloc
  cases halloc with
  | alloc hfree hmin hnew hrest =>
    have hfsf := findSmallestFree_spec hfree hmin hbound
    simp only [allocHeap, hfsf, hfree]
    suffices h' = fun a => if a == addr then some (typeName, fun _ => none) else h a by
      rw [this]
    funext a
    by_cases heq : a = addr
    · subst heq; simp; exact hnew
    · simp [beq_iff_eq, heq]; exact (hrest a (Ne.symm heq))

/-! ## HeapFieldWrite -/

theorem heapFieldWrite_sound {h h' : LaurelHeap} {addr : Nat}
    {field : String} {v : LaurelValue} :
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
    {field : String} {v : LaurelValue} :
    HeapFieldWrite h addr field v h' → heapFieldWrite' h addr field v = some h' := by
  intro hw
  cases hw with
  | write hlook hnew hrest =>
    simp [heapFieldWrite', hlook]
    funext a
    by_cases heqa : a = addr
    · subst heqa; simp
      -- N.B. This `congr` + `beq_iff_eq` step relies on `Identifier` (= `String`) having
      -- a `BEq` instance that agrees with `DecidableEq`. If `Identifier` ever gets a
      -- non-standard `BEq`, this proof would need updating.
      rw [hnew]; congr 1; congr 1; funext f; simp [beq_iff_eq]
    · simp [heqa]; exact (hrest a (Ne.symm heqa)).symm

end Strata.Laurel
