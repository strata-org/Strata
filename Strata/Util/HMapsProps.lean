/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Util.HMaps
import all Strata.Util.HMaps

/-! ## Properties of `HMaps` scope stacks

Lookup through pushes and concatenations, the keys and values of combined stacks, and
scope-wise equivalence of stacks (`Equiv`), and lookup after inserting bindings that agree
with a map into an `HMap`. -/

namespace Strata.Util

namespace HMaps

variable {α : Type u} {β : Type v} [BEq α] [Hashable α]

/-- A scope stack is empty exactly when it has no scopes. -/
public theorem isEmpty_iff_eq_nil {ms : HMaps α β} : ms.isEmpty = true ↔ ms = [] := by
  cases ms <;> simp only [isEmpty, reduceCtorEq]

/-- Lookup after a push checks the new scope first. -/
public theorem find?_push [EquivBEq α] [LawfulHashable α]
    (ts : HMaps α β) (m : HMap α β) (x : α) :
    HMaps.find? (ts.push m) x = (m.find? x).or (HMaps.find? ts x) := by
  simp only [push, find?]
  cases m.find? x <;> rfl

/-- Pushing a scope that does not bind a key keeps its lookup. -/
public theorem find?_push_of_none [EquivBEq α] [LawfulHashable α]
    (ts : HMaps α β) (m : HMap α β) (x : α)
    (h : m.find? x = none) : HMaps.find? (ts.push m) x = HMaps.find? ts x := by
  rw [find?_push, h]
  rfl

/-- A binding in a freshly pushed scope answers the whole-stack lookup. -/
public theorem find?_push_of_some [EquivBEq α] [LawfulHashable α]
    (ts : HMaps α β) (m : HMap α β) (x : α) (v : β)
    (h : m.find? x = some v) : HMaps.find? (ts.push m) x = some v := by
  rw [find?_push, h]
  rfl

/-- Pushing one scope onto stacks with the same lookups gives stacks with the same lookups. -/
public theorem find?_push_congr [EquivBEq α] [LawfulHashable α] {ms ms' : HMaps α β}
    (h : ∀ y, HMaps.find? ms' y = HMaps.find? ms y) (m : HMap α β) (y : α) :
    HMaps.find? (ms'.push m) y = HMaps.find? (ms.push m) y := by
  rw [find?_push, find?_push, h y]

/-- Inserting one binding into stacks with the same lookups gives stacks with the same
    lookups. -/
public theorem find?_insert_congr [LawfulBEq α] [LawfulHashable α] {ms ms' : HMaps α β}
    (h : ∀ y, HMaps.find? ms' y = HMaps.find? ms y) (x : α) (v : β) (y : α) :
    HMaps.find? (ms'.insert x v) y = HMaps.find? (ms.insert x v) y := by
  by_cases hxy : y = x
  · subst hxy
    rw [find?_insert_self, find?_insert_self]
  · rw [find?_insert_ne _ _ _ _ hxy, find?_insert_ne _ _ _ _ hxy, h y]

/-- Mapping a function that fixes every stored value gives an equivalent stack. -/
public theorem mapValues_fix_Equiv [LawfulBEq α] (f : β → β) (ms : HMaps α β)
    (h : ∀ value, value ∈ ms.values → f value = value) :
    HMaps.Equiv (ms.mapValues f) ms := by
  induction ms with
  | nil => exact True.intro
  | cons m rest ih =>
    rw [HMaps.mapValues_cons]
    have h_mem_rest : ∀ value, value ∈ values rest → value ∈ values (m :: rest) := by
      intro value hmem
      exact List.mem_append_right _ hmem
    refine ⟨?_, ih (fun value hmem => h value (h_mem_rest value hmem))⟩
    intro k
    rw [HMap.find?_mapValues]
    cases hfind : m.find? k with
    | none => simp
    | some v =>
      have hmem : v ∈ HMaps.values (m :: rest) :=
        List.mem_append_left _ (HMap.find?_mem_values m hfind)
      simp only [Option.map_some, h v hmem]

/-- If a stack lookup misses, every constituent scope misses. -/
public theorem all_scopes_find?_none [EquivBEq α] [LawfulHashable α]
    (ms : HMaps α β) (x : α)
    (h : ms.find? x = none) : ∀ m, m ∈ ms → HMap.find? m x = none := by
  induction ms with
  | nil => intro m hm; exact absurd hm (by simp)
  | cons first rest ih =>
    intro m hm
    simp only [HMaps.find?] at h
    split at h
    · rename_i hfirst
      rcases List.mem_cons.mp hm with rfl | hrest
      · exact hfirst
      · exact ih h m hrest
    · exact absurd h (by simp)

/-- Popping equivalent stacks gives equivalent stacks. -/
public theorem Equiv.pop {ms ms' : HMaps α β} (h : Equiv ms ms') : Equiv ms.pop ms'.pop := by
  match ms, ms', h with
  | [], [], _ => exact True.intro
  | [], _ :: _, h => exact h.elim
  | _ :: _, [], h => exact h.elim
  | _ :: _, _ :: _, h => exact h.2

/-- If the newest scope is the single entry `x ↦ v`, then `x` looks up to `v`. -/
public theorem find?_cons_single_self [LawfulBEq α] [LawfulHashable α] (x : α) (v : β)
    (ms : HMaps α β) :
    HMaps.find? (HMap.single x v :: ms) x = some v := by
  simp only [HMaps.find?, HMap.find?_single_self]

/-- A newest single-entry scope for `x` does not affect lookup of another key. -/
public theorem find?_cons_single_ne [LawfulBEq α] [LawfulHashable α] (x y : α) (v : β)
    (ms : HMaps α β) (h : y != x) :
    HMaps.find? (HMap.single x v :: ms) y = HMaps.find? ms y := by
  simp only [HMaps.find?, HMap.find?_single_ne x y v h]

/-- Lookup in `ms1 ++ ms2` takes `ms1`'s binding if it has one, else searches `ms2`. -/
public theorem find?_append [LawfulBEq α] [LawfulHashable α]
    (ms1 ms2 : HMaps α β) (x : α) :
    HMaps.find? (ms1 ++ ms2) x
      = match HMaps.find? ms1 x with
        | some v => some v
        | none => HMaps.find? ms2 x := by
  induction ms1 with
  | nil => rfl
  | cons m rest ih =>
    simp only [List.cons_append, HMaps.find?]
    cases hm : m.find? x with
    | some v => rfl
    | none => exact ih

/-- Where the left stack binds a key, the concatenation finds the same value. -/
public theorem find?_append_of_some [LawfulBEq α] [LawfulHashable α] {ms1 : HMaps α β} {x : α}
    {v : β}
    (h : HMaps.find? ms1 x = some v) (ms2 : HMaps α β) :
    HMaps.find? (ms1 ++ ms2) x = some v := by
  rw [find?_append, h]

/-- Where the left stack does not bind a key, the concatenation defers to the right stack. -/
public theorem find?_append_of_none [LawfulBEq α] [LawfulHashable α] {ms1 : HMaps α β} {x : α}
    (h : HMaps.find? ms1 x = none) (ms2 : HMaps α β) :
    HMaps.find? (ms1 ++ ms2) x = HMaps.find? ms2 x := by
  rw [find?_append, h]

/-- Concatenating stacks concatenates their keys. -/
public theorem keys_append (ms1 ms2 : HMaps α β) :
    HMaps.keys (ms1 ++ ms2) = HMaps.keys ms1 ++ HMaps.keys ms2 := by
  induction ms1 with
  | nil => simp only [List.nil_append, HMaps.keys]
  | cons m rest ih => simp only [List.cons_append, HMaps.keys, ih, List.append_assoc]

/-- Concatenating stacks concatenates their values. -/
public theorem values_append (ms1 ms2 : HMaps α β) :
    HMaps.values (ms1 ++ ms2) = HMaps.values ms1 ++ HMaps.values ms2 := by
  induction ms1 with
  | nil => simp only [List.nil_append, HMaps.values]
  | cons m rest ih => simp only [List.cons_append, HMaps.values, ih, List.append_assoc]

/-- Every value of a stack extended with one entry in its newest scope is a value of the original
    stack or the entry's value. -/
public theorem mem_values_addInNewest_single [LawfulBEq α] [LawfulHashable α]
    (ms : HMaps α β) (x : α) (t w : β)
    (h : w ∈ (ms.addInNewest (HMap.single x t)).values) :
    w ∈ ms.values ∨ w = t := by
  cases ms with
  | nil =>
    simp only [HMaps.addInNewest, HMaps.values, List.append_nil] at h
    exact Or.inr ((HMap.mem_values_single_iff x t w).mp h)
  | cons scope rest =>
    rw [HMaps.addInNewest_cons] at h
    simp only [HMaps.values, List.mem_append] at h
    rcases h with h_union | h_rest
    · rw [HMap.mem_values_iff_find?] at h_union
      obtain ⟨k, hk⟩ := h_union
      rw [HMap.find?_union] at hk
      cases hs : scope.find? k with
      | some v =>
        rw [hs] at hk
        simp only [Option.some_or, Option.some.injEq] at hk
        rw [← hk]
        have h_mem : v ∈ values (scope :: rest) := by
          simp only [HMaps.values, List.mem_append]
          exact Or.inl (HMap.find?_mem_values scope hs)
        exact Or.inl h_mem
      | none =>
        rw [hs] at hk
        simp only [Option.none_or] at hk
        exact Or.inr ((HMap.mem_values_single_iff x t w).mp (HMap.find?_mem_values _ hk))
    · have h_mem : w ∈ values (scope :: rest) := by
        simp only [HMaps.values, List.mem_append]
        exact Or.inr h_rest
      exact Or.inl h_mem

end HMaps

namespace HMap

variable {α : Type u} {β : Type v} [BEq α] [Hashable α]

/-- If every binding in `bs` agrees with `S'`, then inserting `bs` into `m`
    keeps each lookup that was already `S'`'s answer, and the inserted keys also
    return `S'`'s answer. -/
public theorem foldl_insert_find?_of_agree [LawfulBEq α] [LawfulHashable α]
    (S' : HMap α β) (bs : List (α × β))
    (hbs : ∀ b ∈ bs, S'.find? b.1 = some b.2) :
    ∀ (m : HMap α β) (x : α) (t : β),
      S'.find? x = some t →
      ((∃ b ∈ bs, b.1 = x) ∨ m.find? x = some t) →
      (bs.foldl (fun m b => m.insert b.1 b.2) m).find? x = some t := by
  induction bs with
  | nil =>
    intro m x t _ hcov
    rcases hcov with ⟨b, hb, _⟩ | hm
    · cases hb
    · exact hm
  | cons b rest ih =>
    intro m x t hx hcov
    have hbrest : ∀ b' ∈ rest, S'.find? b'.1 = some b'.2 :=
      fun b' hb' => hbs b' (List.mem_cons_of_mem b hb')
    have hbb : S'.find? b.1 = some b.2 := hbs b List.mem_cons_self
    simp only [List.foldl_cons]
    apply ih hbrest (m.insert b.1 b.2) x t hx
    by_cases hbx : b.1 = x
    · right
      rw [← hbx, HMap.find?_insert_self]
      rw [← hbx, hbb] at hx
      exact hx
    · rcases hcov with ⟨b', hb', hb'x⟩ | hm
      · rcases List.mem_cons.mp hb' with hh | hh
        · rw [hh] at hb'x
          exact absurd hb'x hbx
        · exact Or.inl ⟨b', hh, hb'x⟩
      · right
        rw [HMap.find?_insert_ne _ _ _ _ (bne_iff_ne.mpr (Ne.symm hbx))]
        exact hm

end HMap

end Strata.Util
