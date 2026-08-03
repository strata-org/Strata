/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Util.HMap
import all Strata.Util.HMap

/-!
A scope stack of `HMap`s, used by the typechecker's substitution and
typing-context scopes.

## Ordering discipline

Unlike a single `HMap` (which is unordered), `HMaps` IS ordered: it is a
`List HMap` searched newest-first, and that order is SEMANTIC — it encodes
variable shadowing (an inner scope shadows an outer one). Theorems here may and
do depend on the scope-stack order. They must NOT, however, depend on the
iteration order WITHIN any single `HMap`.
-/

open Std (ToFormat Format format)

namespace Strata.Util

/-- A stack of scopes, newest first. -/
public abbrev HMaps (α : Type u) (β : Type v) [BEq α] [Hashable α] :=
  List (HMap α β)

namespace HMaps

variable {α : Type u} {β : Type v} [BEq α] [Hashable α]

public instance : Inhabited (HMaps α β) where
  default := []

/-! ### Core operations -/

/-- Keys across all scopes. -/
public def keys (ms : HMaps α β) : List α :=
  match ms with
  | [] => []
  | m :: rest => m.keys ++ keys rest

/-- Values across all scopes. -/
public def values (ms : HMaps α β) : List β :=
  match ms with
  | [] => []
  | m :: rest => m.values ++ values rest

public def isEmpty (ms : HMaps α β) : Bool :=
  match ms with
  | [] => true
  | _ => false

/-- Build a scope stack from a list of scopes, each given as an association
    list. Since `HMap` is opaque, clients cannot write a scope-stack literal
    directly and must go through this builder. -/
public def ofScopes (scopes : List (List (α × β))) : HMaps α β :=
  scopes.map HMap.ofList

/-- Add a fresh scope at the front (newest). -/
public def push (ms : HMaps α β) (m : HMap α β) : HMaps α β :=
  m :: ms

/-- Drop the newest scope. -/
public def pop (ms : HMaps α β) : HMaps α β :=
  match ms with
  | [] => []
  | _ :: rest => rest

/-- The newest scope (empty if none). -/
public def newest (ms : HMaps α β) : HMap α β :=
  match ms with | [] => .empty | m :: _ => m

/-- Look up `x`, searching newest scope first. -/
public def find? [EquivBEq α] [LawfulHashable α] (ms : HMaps α β) (x : α) : Option β :=
  match ms with
  | [] => none
  | m :: rest =>
    match m.find? x with
    | none => find? rest x
    | some v => some v

/-- Remove `x` from every scope. -/
public def remove (ms : HMaps α β) (x : α) : HMaps α β :=
  match ms with
  | [] => []
  | m :: rest => m.erase x :: remove rest x

/-- Merge the entries of `m` into the newest scope. On a key collision the
    existing scope binding wins. -/
public def addInNewest (ms : HMaps α β) (m : HMap α β) : HMaps α β :=
  match ms with
  | [] => [m]
  | scope :: rest => m.union scope :: rest

/-- Transform every value in every scope with `f`. -/
public def mapValues (f : β → γ) (ms : HMaps α β) : HMaps α γ :=
  ms.map (HMap.mapValues f)

/-- Update `x` with `v` in the scope where it lives. Do nothing if `x` is
    absent. -/
public def update [EquivBEq α] [LawfulHashable α] (ms : HMaps α β) (x : α) (v : β) : HMaps α β :=
  match ms with
  | [] => []
  | m :: rest =>
    match m.find? x with
    | none => m :: update rest x v
    | some _ => m.insert x v :: rest

/-- Insert `(x, v)`. If `x` already exists in some scope, update it there;
    otherwise add it to the newest scope. -/
public def insert [EquivBEq α] [LawfulHashable α] (ms : HMaps α β) (x : α) (v : β) : HMaps α β :=
  match ms.find? x with
  | none => (ms.pop).push ((ms.newest).insert x v)
  | some _ => ms.update x v

/-! ### Semantic lemmas -/

/-- After removing `x` from every scope, looking up `x` returns `none`. -/
public theorem find?_remove_self [EquivBEq α] [LawfulHashable α]
    (ms : HMaps α β) (x : α) :
    (ms.remove x).find? x = none := by
  induction ms with
  | nil => simp [remove, find?]
  | cons m rest ih =>
    simp only [remove, find?, HMap.find?_erase_self, ih]

/-- Removing `x` from every scope does not affect lookups for `y ≠ x`. -/
public theorem find?_remove_ne [EquivBEq α] [LawfulHashable α]
    (ms : HMaps α β) (x y : α) (h_ne : y != x) :
    (ms.remove x).find? y = ms.find? y := by
  induction ms with
  | nil => simp [remove, find?]
  | cons m rest ih =>
    simp only [remove, find?, HMap.find?_erase_ne m x y h_ne, ih]

/-- Removing `x` shrinks the key set. -/
public theorem keys_remove_subset [LawfulBEq α] [LawfulHashable α]
    (ms : HMaps α β) (x : α) :
    ∀ k, k ∈ (ms.remove x).keys → k ∈ ms.keys := by
  intro k hk
  induction ms with
  | nil => simp [remove, keys] at hk
  | cons m rest ih =>
    simp only [remove, keys] at hk ⊢
    rcases List.mem_append.mp hk with h | h
    · exact List.mem_append_left _ (HMap.keys_erase_subset m x k h)
    · exact List.mem_append_right _ (ih h)

/-- Removing a different key preserves key membership. -/
public theorem keys_remove_mem_of_ne [LawfulBEq α] [LawfulHashable α]
    {ms : HMaps α β} {a x : α} (h_key : a ∈ ms.keys) (h_ne : a ≠ x) :
    a ∈ (ms.remove x).keys := by
  induction ms with
  | nil => simp [keys] at h_key
  | cons m rest ih =>
    simp only [remove, keys] at h_key ⊢
    rcases List.mem_append.mp h_key with h | h
    · exact List.mem_append_left _ (HMap.keys_erase_mem_of_ne m h h_ne)
    · exact List.mem_append_right _ (ih h)

/-- Removing `x` shrinks the value set. -/
public theorem values_remove_subset [LawfulBEq α] [LawfulHashable α]
    (ms : HMaps α β) (x : α) :
    ∀ v, v ∈ (ms.remove x).values → v ∈ ms.values := by
  intro v hv
  induction ms with
  | nil => simp [remove, values] at hv
  | cons m rest ih =>
    simp only [remove, values] at hv ⊢
    rcases List.mem_append.mp hv with h | h
    · exact List.mem_append_left _ (HMap.values_erase_subset m x v h)
    · exact List.mem_append_right _ (ih h)

/-! ### Key/value membership bridges -/

/-- If `find?` returns `some v`, the key is in `keys`. -/
public theorem find?_mem_keys [LawfulBEq α] [LawfulHashable α]
    (ms : HMaps α β) (h : ms.find? k = some v) : k ∈ ms.keys := by
  induction ms with
  | nil => simp [find?] at h
  | cons m rest ih =>
    simp only [find?] at h
    simp only [keys, List.mem_append]
    cases hm : m.find? k with
    | some w => exact Or.inl (HMap.find?_mem_keys m hm)
    | none => rw [hm] at h; exact Or.inr (ih h)

/-- A value is in the stack's `values` iff it is in some scope's `values`. -/
public theorem mem_values_iff_exists_scope (ms : HMaps α β) (v : β) :
    v ∈ ms.values ↔ ∃ m, m ∈ ms ∧ v ∈ m.values := by
  induction ms with
  | nil => simp [values]
  | cons m rest ih =>
    simp only [values, List.mem_append, List.mem_cons, ih]
    constructor
    · rintro (h | ⟨m', hm', hv⟩)
      · exact ⟨m, Or.inl rfl, h⟩
      · exact ⟨m', Or.inr hm', hv⟩
    · rintro ⟨m', (rfl | hm'), hv⟩
      · exact Or.inl hv
      · exact Or.inr ⟨m', hm', hv⟩

/-- If `find?` returns `some v`, the value is in `values`. -/
public theorem find?_mem_values [LawfulBEq α] [LawfulHashable α]
    (ms : HMaps α β) (h : ms.find? k = some v) : v ∈ ms.values := by
  induction ms with
  | nil => simp [find?] at h
  | cons m rest ih =>
    simp only [find?] at h
    simp only [values, List.mem_append]
    cases hm : m.find? k with
    | some w => rw [hm] at h; injection h with h; subst h; exact Or.inl (HMap.find?_mem_values m hm)
    | none => rw [hm] at h; exact Or.inr (ih h)

/-- If the key is in `keys`, then `find?` succeeds. -/
public theorem find?_of_mem_keys [LawfulBEq α] [LawfulHashable α]
    (ms : HMaps α β) (k : α) (hk : k ∈ ms.keys) : ∃ v, ms.find? k = some v := by
  induction ms with
  | nil => simp [keys] at hk
  | cons m rest ih =>
    simp only [keys, List.mem_append] at hk
    simp only [find?]
    cases hm : m.find? k with
    | some w => exact ⟨w, rfl⟩
    | none =>
      have h_not_m : k ∉ m.keys := HMap.find?_of_not_mem_keys m hm
      exact ih (hk.resolve_left h_not_m)

/-- Key membership is exactly "find? succeeds". -/
public theorem mem_keys_iff_find? [LawfulBEq α] [LawfulHashable α]
    (ms : HMaps α β) (k : α) :
    k ∈ ms.keys ↔ ∃ v, ms.find? k = some v :=
  ⟨find?_of_mem_keys ms k, fun ⟨_v, h⟩ => find?_mem_keys ms h⟩

/-- If `find?` returns `none`, the key is not in `keys`. -/
public theorem find?_of_not_mem_values [LawfulBEq α] [LawfulHashable α]
    (ms : HMaps α β) (h : ms.find? k = none) : k ∉ ms.keys := by
  intro hk
  obtain ⟨v, hv⟩ := find?_of_mem_keys ms k hk
  rw [hv] at h; exact absurd h (by simp)

/-- `find?` returns `none` when the key is not in `keys`. -/
public theorem not_mem_keys_find?_none [LawfulBEq α] [LawfulHashable α]
    (ms : HMaps α β) (k : α) (h : k ∉ ms.keys) : ms.find? k = none := by
  cases hf : ms.find? k with
  | none => rfl
  | some v => exact absurd (find?_mem_keys ms hf) h

/-! ### `mapValues` lemmas -/

@[simp]
public theorem mapValues_nil (f : β → γ) : mapValues f ([] : HMaps α β) = [] := by
  simp [mapValues]

@[simp]
public theorem mapValues_cons (f : β → γ) (m : HMap α β) (rest : HMaps α β) :
    mapValues f (m :: rest) = m.mapValues f :: mapValues f rest := by
  simp [mapValues]

/-- Looking up in `mapValues f ms` maps the found value through `f`. -/
public theorem find?_mapValues [LawfulBEq α] [LawfulHashable α]
    (f : β → γ) (ms : HMaps α β) (k : α) :
    (ms.mapValues f).find? k = (ms.find? k).map f := by
  induction ms with
  | nil => simp [find?]
  | cons m rest ih =>
    simp only [mapValues_cons, find?, HMap.find?_mapValues]
    cases hm : m.find? k with
    | some v => simp
    | none => simp only [Option.map_none]; exact ih

/-- `mapValues` preserves the key set (as membership). -/
public theorem mem_keys_mapValues_iff [LawfulBEq α] [LawfulHashable α]
    (f : β → γ) (ms : HMaps α β) (k : α) :
    k ∈ (ms.mapValues f).keys ↔ k ∈ ms.keys := by
  induction ms with
  | nil => simp [keys]
  | cons m rest ih =>
    simp only [mapValues_cons, keys, List.mem_append]
    rw [HMap.mem_keys_mapValues_iff, ih]

/-- A value is in `(mapValues f ms).values` iff it is `f` of some value of `ms`. -/
public theorem mem_values_mapValues [LawfulBEq α] [LawfulHashable α]
    (f : β → γ) (ms : HMaps α β) (w : γ) :
    w ∈ (ms.mapValues f).values ↔ ∃ v, v ∈ ms.values ∧ w = f v := by
  induction ms with
  | nil => simp [values]
  | cons m rest ih =>
    simp only [mapValues_cons, values, List.mem_append]
    rw [HMap.mem_values_mapValues, ih]
    constructor
    · rintro (⟨v, hv, rfl⟩ | ⟨v, hv, rfl⟩)
      · exact ⟨v, Or.inl hv, rfl⟩
      · exact ⟨v, Or.inr hv, rfl⟩
    · rintro ⟨v, hv | hv, rfl⟩
      · exact Or.inl ⟨v, hv, rfl⟩
      · exact Or.inr ⟨v, hv, rfl⟩

/-- Looking up in a single-scope stack `[m]` is just the `HMap` lookup. -/
public theorem find?_single_scope [EquivBEq α] [LawfulHashable α] (m : HMap α β) (x : α) :
    HMaps.find? [m] x = m.find? x := by
  simp only [find?]
  cases m.find? x <;> rfl

/-! ### `addInNewest` lemmas -/

/-- `addInNewest` on a non-empty stack unites the new map into the newest scope. -/
public theorem addInNewest_cons (scope : HMap α β) (rest : HMaps α β) (m : HMap α β) :
    addInNewest (scope :: rest) m = m.union scope :: rest := by
  simp [addInNewest]

/-- Collision semantics of `addInNewest` on a non-empty stack: the newest scope
    wins, then the added map, then the rest of the stack. In particular a binding
    already in the newest scope shadows the added map. -/
public theorem find?_addInNewest [LawfulBEq α] [LawfulHashable α]
    (scope : HMap α β) (rest : HMaps α β) (m : HMap α β) (k : α) :
    (addInNewest (scope :: rest) m).find? k =
      (scope.find? k).or ((m.find? k).or (rest.find? k)) := by
  rw [addInNewest_cons]
  simp only [find?, HMap.find?_union]
  cases scope.find? k <;> cases m.find? k <;> simp

/-- If every scope gives `none` for `x`, then `find?` gives `none`. -/
public theorem find?_of_all_none [EquivBEq α] [LawfulHashable α]
    (ms : HMaps α β) (x : α) (h : ∀ m, m ∈ ms → m.find? x = none) :
    ms.find? x = none := by
  induction ms with
  | nil => rfl
  | cons m rest ih =>
    simp only [find?]
    rw [h m List.mem_cons_self]
    exact ih (fun m' hm' => h m' (List.mem_cons_of_mem m hm'))

/-- A successful lookup after `addInNewest m` comes either from `m` or from the
    original stack (general `m`, not just a `single`). -/
public theorem find?_addInNewest_mem [LawfulBEq α] [LawfulHashable α]
    (ms : HMaps α β) (m : HMap α β) (y : α) (v : β)
    (h : (ms.addInNewest m).find? y = some v) :
    m.find? y = some v ∨ ms.find? y = some v := by
  cases ms with
  | nil =>
    simp only [HMaps.addInNewest, HMaps.find?] at h
    left; cases hm : m.find? y with
    | none => rw [hm] at h; exact absurd h (by simp)
    | some w => rw [hm] at h; exact h
  | cons scope rest =>
    rw [find?_addInNewest] at h
    simp only [find?]
    cases hs : scope.find? y with
    | some w => rw [hs] at h; simp only [Option.some_or] at h; right; exact h
    | none =>
      rw [hs] at h; simp only [Option.none_or] at h
      cases hm : m.find? y with
      | some w => rw [hm] at h; simp only [Option.some_or] at h; left; exact h
      | none => rw [hm] at h; simp only [Option.none_or] at h; right; exact h

/-- Every value after `addInNewest m` comes either from `m` or from the original
    stack (general `m`, not just a `single`). -/
public theorem mem_values_addInNewest [LawfulBEq α] [LawfulHashable α]
    (ms : HMaps α β) (m : HMap α β) (w : β)
    (h : w ∈ (ms.addInNewest m).values) :
    w ∈ m.values ∨ w ∈ ms.values := by
  cases ms with
  | nil =>
    simp only [HMaps.addInNewest, HMaps.values, List.append_nil] at h
    exact Or.inl h
  | cons scope rest =>
    rw [addInNewest_cons] at h
    simp only [values, List.mem_append] at h
    rcases h with h_union | h_rest
    · rw [HMap.mem_values_iff_find?] at h_union
      obtain ⟨k, hk⟩ := h_union
      rw [HMap.find?_union] at hk
      cases hs : scope.find? k with
      | some v => rw [hs] at hk; simp only [Option.some_or, Option.some.injEq] at hk
                  rw [← hk]; right; simp only [values, List.mem_append]
                  exact Or.inl (HMap.find?_mem_values scope hs)
      | none => rw [hs] at hk; simp only [Option.none_or] at hk
                left; exact HMap.find?_mem_values m hk
    · right; simp only [values, List.mem_append]; exact Or.inr h_rest

/-- Looking up in `addInNewest ms (single x v)` either returns the new binding
    (when the key matches) or falls through to the original stack. -/
public theorem find?_addInNewest_single [LawfulBEq α] [LawfulHashable α]
    (ms : HMaps α β) (x : α) (v : β) (y : α) :
    (addInNewest ms (HMap.single x v)).find? y = some v ∧ y = x ∨
    (addInNewest ms (HMap.single x v)).find? y = ms.find? y := by
  cases ms with
  | nil =>
    simp only [addInNewest, find?]
    by_cases h : y = x
    · subst h; left; exact ⟨by rw [HMap.find?_single_self], rfl⟩
    · right; rw [HMap.find?_single_ne x y v (by simp [bne, h])]
  | cons m rest =>
    rw [addInNewest_cons]
    simp only [find?, HMap.find?_union]
    by_cases h : y = x
    · subst h; rw [HMap.find?_single_self]
      cases hm : m.find? y with
      | none => left; exact ⟨rfl, rfl⟩
      | some w => right; simp
    · rw [HMap.find?_single_ne x y v (by simp [bne, h])]; right
      cases m.find? y <;> simp

/-- Looking up `y` in `addInNewest ms (single x v)` is unchanged when `y ≠ x`. -/
public theorem find?_addInNewest_ne [LawfulBEq α] [LawfulHashable α]
    (ms : HMaps α β) (x : α) (v : β) (y : α) (h_ne : y ≠ x) :
    (addInNewest ms (HMap.single x v)).find? y = ms.find? y := by
  rcases find?_addInNewest_single ms x v y with ⟨_, h_eq⟩ | h
  · exact absurd h_eq h_ne
  · exact h

/-- When `x` is fresh (not found in any scope), `addInNewest` makes it findable. -/
public theorem find?_addInNewest_self [LawfulBEq α] [LawfulHashable α]
    (ms : HMaps α β) (x : α) (v : β)
    (h_fresh : ∀ m, m ∈ ms → m.find? x = none) :
    (addInNewest ms (HMap.single x v)).find? x = some v := by
  cases ms with
  | nil => simp only [addInNewest, find?, HMap.find?_single_self]
  | cons m rest =>
    rw [addInNewest_cons]
    simp only [find?, HMap.find?_union, HMap.find?_single_self,
      h_fresh m List.mem_cons_self, Option.none_or]

/-- find?-level cancellation: removing a freshly-added single binding recovers the
    original stack's lookups, for every key. Stated at the `find?` level since
    `HMap` opacity gives no `find?`-based extensionality, so the structural
    equation `remove (addInNewest ms (single x v)) x = ms` is not provable. -/
public theorem find?_remove_addInNewest_single_fresh [LawfulBEq α] [LawfulHashable α]
    (ms : HMaps α β) (x : α) (v : β)
    (h_fresh : ∀ m, m ∈ ms → m.find? x = none) (k : α) :
    ((addInNewest ms (HMap.single x v)).remove x).find? k = ms.find? k := by
  by_cases hk : k = x
  · subst hk
    rw [find?_remove_self]
    symm
    induction ms with
    | nil => simp [find?]
    | cons m rest ih =>
      simp only [find?]
      rw [h_fresh m List.mem_cons_self]
      exact ih (fun m' hm' => h_fresh m' (List.mem_cons_of_mem m hm'))
  · rw [find?_remove_ne _ x k (by simp [bne, hk]),
        find?_addInNewest_ne ms x v k hk]

/-! ### `insert`/`update` lookup lemmas -/

/-- `update ms x v` maps `x` to `v` when `x` was already present. -/
public theorem find?_update_self [LawfulBEq α] [LawfulHashable α]
    (ms : HMaps α β) (x : α) (v : β) (h : ms.find? x ≠ none) :
    (ms.update x v).find? x = some v := by
  induction ms with
  | nil => simp [find?] at h
  | cons m rest ih =>
    simp only [update]; split
    · rename_i h_none; simp only [find?, h_none]; apply ih
      simp only [find?, h_none] at h; exact h
    · simp only [find?, HMap.find?_insert_self]

/-- `insert ms x v` maps `x` to `v`. -/
public theorem find?_insert_self [LawfulBEq α] [LawfulHashable α]
    (ms : HMaps α β) (x : α) (v : β) :
    (ms.insert x v).find? x = some v := by
  simp only [insert]; split
  · rename_i h_none
    cases ms with
    | nil => simp only [pop, push, newest, find?, HMap.find?_insert_self]
    | cons m rest => simp only [pop, push, newest, find?, HMap.find?_insert_self]
  · exact find?_update_self ms x v (by simp_all)

/-- `find?` is unchanged for a different key after `insert`. -/
public theorem find?_insert_ne [LawfulBEq α] [LawfulHashable α]
    (ms : HMaps α β) (x y : α) (v : β) (h_ne : x ≠ y) :
    (ms.insert y v).find? x = ms.find? x := by
  simp only [insert]
  cases h_fb : ms.find? y with
  | none =>
    cases ms with
    | nil =>
      simp only [pop, push, newest, find?]
      rw [HMap.find?_insert_ne _ y x v (by simp [bne, h_ne]), HMap.find?_empty]
    | cons m rest =>
      simp only [pop, push, newest, find?]
      rw [HMap.find?_insert_ne _ y x v (by simp [bne, h_ne])]
  | some val =>
    induction ms with
    | nil => simp [find?] at h_fb
    | cons m rest ih =>
      simp only [update]
      split
      · rename_i h_none
        simp only [find?]
        cases m.find? x with
        | none =>
          have h_rest : HMaps.find? rest y = some val := by
            simp only [find?, h_none] at h_fb; exact h_fb
          exact ih h_rest
        | some _ => rfl
      · simp only [find?]
        rw [HMap.find?_insert_ne _ y x v (by simp [bne, h_ne])]

/-! ### Insert key/value subset lemmas -/

/-- `update` never grows the key set. -/
private theorem update_keys_subset [LawfulBEq α] [LawfulHashable α]
    (ms : HMaps α β) (key : α) (val : β) :
    ∀ k, k ∈ (ms.update key val).keys → k ∈ ms.keys := by
  intro k hk
  induction ms with
  | nil => simp [update, keys] at hk
  | cons m rest ih =>
    simp only [update] at hk
    split at hk
    · simp only [keys, List.mem_append] at hk ⊢
      exact hk.imp id ih
    · -- some branch: m.insert key val :: rest, and find? m key = some
      rename_i w h_find
      simp only [keys, List.mem_append] at hk ⊢
      rcases hk with h | h
      · left
        rcases List.mem_cons.mp (HMap.insert_keys_subset m key val k h) with h' | h'
        · rw [h']; exact HMap.find?_mem_keys m h_find
        · exact h'
      · right; exact h

/-- `update` never grows the value set beyond adding `val`. -/
private theorem update_values_subset [LawfulBEq α] [LawfulHashable α]
    (ms : HMaps α β) (key : α) (val : β) :
    ∀ v, v ∈ (ms.update key val).values → v ∈ val :: ms.values := by
  intro v hv
  induction ms with
  | nil => simp [update, values] at hv
  | cons m rest ih =>
    simp only [update] at hv
    split at hv
    · simp only [values, List.mem_append] at hv
      simp only [values, List.mem_cons, List.mem_append]
      rcases hv with h | h
      · exact Or.inr (Or.inl h)
      · rcases List.mem_cons.mp (ih h) with h' | h'
        · exact Or.inl h'
        · exact Or.inr (Or.inr h')
    · simp only [values, List.mem_append] at hv
      simp only [values, List.mem_cons, List.mem_append]
      rcases hv with h | h
      · rcases List.mem_cons.mp (HMap.insert_values_subset m key val v h) with h' | h'
        · exact Or.inl h'
        · exact Or.inr (Or.inl h')
      · exact Or.inr (Or.inr h)

/-- Inserting can only add `key` to the key set. -/
public theorem insert_keys_subset [LawfulBEq α] [LawfulHashable α]
    (ms : HMaps α β) (key : α) (val : β) :
    ∀ k, k ∈ (ms.insert key val).keys → k ∈ key :: ms.keys := by
  intro k hk
  simp only [insert] at hk
  split at hk
  · -- fresh: (ms.pop).push (ms.newest.insert key val)
    rename_i h_none
    cases ms with
    | nil =>
      simp only [pop, push, newest, keys, List.append_nil] at hk
      have := HMap.insert_keys_subset (.empty : HMap α β) key val k hk
      rcases List.mem_cons.mp this with h' | h'
      · rw [h']; exact List.mem_cons_self
      · obtain ⟨w, hw⟩ := (HMap.mem_keys_iff_find? .empty k).mp h'
        rw [HMap.find?_empty] at hw; exact absurd hw (by simp)
    | cons m rest =>
      simp only [pop, push, newest, keys, List.mem_append] at hk
      simp only [keys, List.mem_cons, List.mem_append]
      rcases hk with h | h
      · rcases List.mem_cons.mp (HMap.insert_keys_subset m key val k h) with h' | h'
        · exact Or.inl h'
        · exact Or.inr (Or.inl h')
      · exact Or.inr (Or.inr h)
  · exact List.mem_cons_of_mem _ (update_keys_subset ms key val k hk)

/-- Inserting can only add `val` to the value set. -/
public theorem insert_values_subset [LawfulBEq α] [LawfulHashable α]
    (ms : HMaps α β) (key : α) (val : β) :
    ∀ v, v ∈ (ms.insert key val).values → v ∈ val :: ms.values := by
  intro v hv
  simp only [insert] at hv
  split at hv
  · rename_i h_none
    cases ms with
    | nil =>
      simp only [pop, push, newest, values, List.append_nil] at hv
      have := HMap.insert_values_subset (.empty : HMap α β) key val v hv
      rcases List.mem_cons.mp this with h' | h'
      · rw [h']; exact List.mem_cons_self
      · obtain ⟨w, hw⟩ := (HMap.mem_values_iff_find? .empty v).mp h'
        rw [HMap.find?_empty] at hw; exact absurd hw (by simp)
    | cons m rest =>
      simp only [pop, push, newest, values, List.mem_append] at hv
      simp only [values, List.mem_cons, List.mem_append]
      rcases hv with h | h
      · rcases List.mem_cons.mp (HMap.insert_values_subset m key val v h) with h' | h'
        · exact Or.inl h'
        · exact Or.inr (Or.inl h')
      · exact Or.inr (Or.inr h)
  · exact update_values_subset ms key val v hv


/-! ### Scope-stack equivalence (find?-level stand-in for structural equality)

`HMap` is opaque and has no `find?`-based extensionality, so two scopes built by
different operation sequences can agree on every lookup without being
propositionally equal. Context-preservation results are therefore stated as an
*equivalence* rather than `=`. Per-scope agreement on equal-length stacks is
stronger than bare stack-`find?` agreement: it also pins each scope's `values`
(shadowed entries included) and the scope count. -/

/-- Two scope stacks are equivalent when they have the same number of scopes and
    corresponding scopes are `HMap.Equiv`. (No `List.Forall2` in this toolchain,
    so defined by direct recursion.) -/
public def Equiv : HMaps α β → HMaps α β → Prop
  | [], [] => True
  | m :: rest, m' :: rest' => HMap.Equiv m m' ∧ Equiv rest rest'
  | _, _ => False

@[refl] public theorem Equiv.refl (ms : HMaps α β) : Equiv ms ms := by
  induction ms with
  | nil => exact True.intro
  | cons m rest ih => exact ⟨HMap.Equiv.refl m, ih⟩

public theorem Equiv.symm {ms ms' : HMaps α β} (h : Equiv ms ms') : Equiv ms' ms := by
  match ms, ms', h with
  | [], [], _ => exact True.intro
  | m :: rest, m' :: rest', ⟨hm, ht⟩ => exact ⟨hm.symm, Equiv.symm ht⟩

public theorem Equiv.trans {ms ms' ms'' : HMaps α β}
    (h1 : Equiv ms ms') (h2 : Equiv ms' ms'') : Equiv ms ms'' := by
  match ms, ms', ms'', h1, h2 with
  | [], [], [], _, _ => exact True.intro
  | m :: rest, m' :: rest', m'' :: rest'', ⟨hm1, ht1⟩, ⟨hm2, ht2⟩ =>
    exact ⟨hm1.trans hm2, Equiv.trans ht1 ht2⟩

/-- An `Eq` of scope stacks is in particular an `Equiv`. -/
public theorem Equiv.of_eq {ms ms' : HMaps α β} (h : ms = ms') : Equiv ms ms' :=
  h ▸ Equiv.refl ms

/-- `Equiv` is preserved by dropping the newest scope. This is what lets the
    block-level `popContext` recover the input context tail up to `Equiv` (a
    structural equality of the popped tail does not survive the `HMap`
    migration, since `remove`/`erase` reconstruct every scope). -/
public theorem Equiv.pop {ms ms' : HMaps α β} (h : Equiv ms ms') :
    Equiv ms.pop ms'.pop := by
  match ms, ms', h with
  | [], [], _ => exact True.intro
  | _ :: rest, _ :: rest', ⟨_, ht⟩ => exact ht

/-- `Equiv` scope stacks have `find?`-agreeing newest scopes. -/
public theorem Equiv.newest [EquivBEq α] [LawfulHashable α] {ms ms' : HMaps α β}
    (h : Equiv ms ms') (k : α) : (ms.newest).find? k = (ms'.newest).find? k := by
  match ms, ms', h with
  | [], [], _ => rfl
  | m :: rest, m' :: rest', ⟨hm, _⟩ => exact hm k

/-- `mapValues` preserves scope-stack `Equiv`. -/
public theorem mapValues_equiv [LawfulBEq α] [LawfulHashable α]
    (f : β → γ) {ms ms' : HMaps α β} (h : Equiv ms ms') :
    Equiv (ms.mapValues f) (ms'.mapValues f) := by
  match ms, ms', h with
  | [], [], _ => exact True.intro
  | m :: rest, m' :: rest', ⟨hm, ht⟩ =>
    exact ⟨HMap.mapValues_equiv f hm, mapValues_equiv f ht⟩

/-- Fusing two `mapValues` into one, up to scope-stack `Equiv`. -/
public theorem mapValues_mapValues [LawfulBEq α] [LawfulHashable α]
    (f : γ → δ) (g : β → γ) (ms : HMaps α β) :
    Equiv ((ms.mapValues g).mapValues f) (ms.mapValues (fun v => f (g v))) := by
  induction ms with
  | nil => exact True.intro
  | cons m rest ih =>
    exact ⟨HMap.mapValues_mapValues f g m, ih⟩

/-- `mapValues` of functions agreeing on the stored values are `Equiv`. -/
public theorem mapValues_congr [LawfulBEq α] [LawfulHashable α]
    {f g : β → γ} (ms : HMaps α β) (h : ∀ v ∈ ms.values, f v = g v) :
    Equiv (ms.mapValues f) (ms.mapValues g) := by
  induction ms with
  | nil => exact True.intro
  | cons m rest ih =>
    refine ⟨HMap.mapValues_congr m (fun v hv => h v ?_), ih (fun v hv => h v ?_)⟩
    · simp only [values, List.mem_append]; exact Or.inl hv
    · simp only [values, List.mem_append]; exact Or.inr hv

/-- `Equiv` implies pointwise `find?` agreement across the whole stack. -/
public theorem Equiv.find? [LawfulBEq α] [LawfulHashable α]
    {ms ms' : HMaps α β} (h : Equiv ms ms') (k : α) :
    ms.find? k = ms'.find? k := by
  match ms, ms', h with
  | [], [], _ => rfl
  | m :: rest, m' :: rest', ⟨hm, ht⟩ =>
    simp only [HMaps.find?]; rw [hm k, Equiv.find? ht k]

/-- `Equiv` preserves membership in `values` (both directions). -/
public theorem Equiv.mem_values [LawfulBEq α] [LawfulHashable α]
    {ms ms' : HMaps α β} (h : Equiv ms ms') (v : β) :
    v ∈ ms.values ↔ v ∈ ms'.values := by
  match ms, ms', h with
  | [], [], _ => rfl
  | m :: rest, m' :: rest', ⟨hm, ht⟩ =>
    simp only [HMaps.values, List.mem_append]
    have ih := Equiv.mem_values ht v
    constructor
    · rintro (h1 | h2)
      · left; rw [HMap.mem_values_iff_find?] at h1 ⊢
        obtain ⟨k, hk⟩ := h1; exact ⟨k, (hm k).symm.trans hk⟩
      · exact Or.inr (ih.mp h2)
    · rintro (h1 | h2)
      · left; rw [HMap.mem_values_iff_find?] at h1 ⊢
        obtain ⟨k, hk⟩ := h1; exact ⟨k, (hm k).trans hk⟩
      · exact Or.inr (ih.mpr h2)

/-- `Equiv` preserves scope count, hence non-emptiness. -/
public theorem Equiv.length {ms ms' : HMaps α β} (h : Equiv ms ms') : ms.length = ms'.length := by
  match ms, ms', h with
  | [], [], _ => rfl
  | m :: rest, m' :: rest', ⟨_, ht⟩ => simp only [List.length_cons]; rw [Equiv.length ht]

public theorem Equiv.ne_nil {ms ms' : HMaps α β} (h : Equiv ms ms') (h_ne : ms ≠ []) : ms' ≠ [] := by
  match ms, ms', h with
  | [], _, _ => exact absurd rfl h_ne
  | _ :: _, [], h => exact absurd h (by simp [Equiv])
  | _ :: _, _ :: _, _ => exact List.cons_ne_nil _ _

/-- `HMaps.update` respects `Equiv`. -/
public theorem update_equiv [LawfulBEq α] [LawfulHashable α]
    {ms ms' : HMaps α β} (h : Equiv ms ms') (x : α) (v : β) :
    Equiv (ms.update x v) (ms'.update x v) := by
  match ms, ms', h with
  | [], [], _ => exact True.intro
  | m :: rest, m' :: rest', ⟨hm, ht⟩ =>
    simp only [HMaps.update]; rw [hm x]
    cases hfind : m'.find? x with
    | none => exact ⟨hm, update_equiv ht x v⟩
    | some _ => exact ⟨HMap.insert_equiv hm x v, ht⟩

/-- `HMaps.insert` respects `Equiv`. -/
public theorem insert_equiv [LawfulBEq α] [LawfulHashable α]
    {ms ms' : HMaps α β} (h : Equiv ms ms') (x : α) (v : β) :
    Equiv (ms.insert x v) (ms'.insert x v) := by
  simp only [HMaps.insert]; rw [h.find? x]
  cases hfind : ms'.find? x with
  | none =>
    match ms, ms', h with
    | [], [], _ => exact ⟨HMap.insert_equiv (HMap.Equiv.refl _) x v, True.intro⟩
    | m :: rest, m' :: rest', ⟨hm, ht⟩ =>
      simp only [HMaps.pop, HMaps.newest, HMaps.push]; exact ⟨HMap.insert_equiv hm x v, ht⟩
  | some _ => exact update_equiv h x v

/-- `remove` respects `Equiv` (removes from every scope, preserving count). -/
public theorem remove_equiv [LawfulBEq α] [LawfulHashable α]
    {ms ms' : HMaps α β} (h : Equiv ms ms') (x : α) :
    Equiv (ms.remove x) (ms'.remove x) := by
  match ms, ms', h with
  | [], [], _ => exact True.intro
  | m :: rest, m' :: rest', ⟨hm, ht⟩ =>
    simp only [HMaps.remove]
    refine ⟨fun k => ?_, remove_equiv ht x⟩
    by_cases hk : k = x
    · subst hk; rw [HMap.find?_erase_self, HMap.find?_erase_self]
    · rw [HMap.find?_erase_ne _ _ _ (by simp [bne, hk]),
          HMap.find?_erase_ne _ _ _ (by simp [bne, hk])]
      exact hm k

/-- `addInNewest` respects `Equiv` when the merged scope is `HMap.Equiv`. -/
public theorem addInNewest_equiv [LawfulBEq α] [LawfulHashable α]
    {ms ms' : HMaps α β} (h : Equiv ms ms') {m m' : HMap α β} (hm : HMap.Equiv m m') :
    Equiv (ms.addInNewest m) (ms'.addInNewest m') := by
  match ms, ms', h with
  | [], [], _ => simp only [HMaps.addInNewest]; exact ⟨hm, True.intro⟩
  | scope :: rest, scope' :: rest', ⟨hs, ht⟩ =>
    simp only [HMaps.addInNewest]
    refine ⟨fun k => ?_, ht⟩
    rw [HMap.find?_union, HMap.find?_union, hs k, hm k]

/-- `mapValues` of a fresh `addInNewest`-single is `Equiv` to inserting the mapped
    value into the mapped stack. Needs `ms ≠ []` and `x` fresh in `ms`. -/
public theorem mapValues_addInNewest_single_equiv_insert [LawfulBEq α] [LawfulHashable α]
    (f : β → γ) (ms : HMaps α β) (x : α) (v : β)
    (h_ne : ms ≠ []) (h_fresh : find? ms x = none) :
    Equiv (mapValues f (ms.addInNewest (HMap.single x v)))
      ((mapValues f ms).insert x (f v)) := by
  cases ms with
  | nil => exact absurd rfl h_ne
  | cons m rest =>
    -- head scope: m.find? x = none from the stack freshness
    have h_head_fresh : m.find? x = none := by
      simp only [find?] at h_fresh
      cases hm : m.find? x with
      | none => rfl
      | some w => rw [hm] at h_fresh; simp at h_fresh
    -- RHS insert on the mapped stack targets the (non-empty) newest scope
    have h_map_fresh : find? (mapValues f (m :: rest)) x = none := by
      rw [find?_mapValues, h_fresh]; rfl
    have h_ins : (mapValues f (m :: rest)).insert x (f v) =
        (m.mapValues f).insert x (f v) :: mapValues f rest := by
      unfold insert
      rw [h_map_fresh]
      simp only [mapValues, List.map_cons, pop, push, newest]
    rw [addInNewest_cons, h_ins]
    simp only [mapValues, List.map_cons]
    refine ⟨?_, Equiv.refl _⟩
    -- head scope Equiv: (m.union (single x v)).mapValues f  ≈  (m.mapValues f).insert x (f v)
    intro k
    rw [HMap.find?_mapValues, HMap.find?_union]
    by_cases h_eq : k = x
    · subst h_eq
      rw [HMap.find?_single_self, HMap.find?_insert_self, h_head_fresh]; rfl
    · rw [HMap.find?_single_ne x k v (by simp [bne, h_eq]),
          HMap.find?_insert_ne _ x k (f v) (by simp [bne, h_eq]),
          HMap.find?_mapValues, Option.or_none]

/-- `mapValues` commutes with `insert`, up to `Equiv`. -/
public theorem mapValues_insert_equiv [LawfulBEq α] [LawfulHashable α]
    (f : β → γ) (ms : HMaps α β) (x : α) (v : β) :
    Equiv (mapValues f (ms.insert x v)) ((mapValues f ms).insert x (f v)) := by
  have h_map_find : find? (mapValues f ms) x = (find? ms x).map f := find?_mapValues f ms x
  cases h_fx : find? ms x with
  | none =>
    -- Both sides go through the `push`-to-newest branch of `insert`.
    have h_map_none : find? (mapValues f ms) x = none := by rw [h_map_find, h_fx]; rfl
    have h_lhs : HMaps.insert ms x v = (ms.pop).push ((ms.newest).insert x v) := by
      unfold insert; rw [h_fx]
    have h_rhs : (mapValues f ms).insert x (f v)
        = ((mapValues f ms).pop).push (((mapValues f ms).newest).insert x (f v)) := by
      unfold insert; rw [h_map_none]
    rw [h_lhs, h_rhs]
    cases ms with
    | nil =>
      simp only [pop, push, newest, mapValues, List.map_nil]
      have h_empty : HMap.Equiv (HMap.mapValues f (HMap.empty : HMap α β)) HMap.empty := by
        intro k; rw [HMap.find?_mapValues, HMap.find?_empty, HMap.find?_empty]; rfl
      exact ⟨(HMap.mapValues_insert f HMap.empty x v).trans (HMap.insert_equiv h_empty x (f v)),
        True.intro⟩
    | cons m rest =>
      simp only [pop, push, newest, mapValues, List.map_cons]
      exact ⟨HMap.mapValues_insert f m x v, Equiv.refl _⟩
  | some w =>
    -- Both sides go through the `update` branch.
    have h_map_some : find? (mapValues f ms) x = some (f w) := by rw [h_map_find, h_fx]; rfl
    have h_lhs : HMaps.insert ms x v = ms.update x v := by unfold insert; rw [h_fx]
    have h_rhs : (mapValues f ms).insert x (f v) = (mapValues f ms).update x (f v) := by
      unfold insert; rw [h_map_some]
    rw [h_lhs, h_rhs]
    -- `mapValues (update x v) ≈ update x (f v) (mapValues)` by spine induction.
    clear h_fx h_map_find h_map_some h_lhs h_rhs
    induction ms with
    | nil => exact True.intro
    | cons m rest ih =>
      simp only [update, mapValues, List.map_cons]
      rw [HMap.find?_mapValues]
      cases hm : m.find? x with
      | none =>
        simp only [Option.map_none]
        exact ⟨HMap.Equiv.refl _, ih⟩
      | some _ =>
        simp only [Option.map_some]
        exact ⟨HMap.mapValues_insert f m x v, Equiv.refl _⟩

/-- Erasing a key fresh in every scope is an `Equiv`-identity. -/
public theorem remove_of_fresh_equiv [LawfulBEq α] [LawfulHashable α]
    (ms : HMaps α β) (x : α) (h_fresh : ∀ m, m ∈ ms → m.find? x = none) :
    Equiv (ms.remove x) ms := by
  cases ms with
  | nil => exact True.intro
  | cons scope rest =>
    simp only [HMaps.remove]
    have h_scope_fresh : scope.find? x = none := h_fresh scope List.mem_cons_self
    refine ⟨fun k => ?_, remove_of_fresh_equiv rest x
      (fun m hm => h_fresh m (List.mem_cons_of_mem scope hm))⟩
    by_cases hk : k = x
    · subst hk; rw [HMap.find?_erase_self, h_scope_fresh]
    · rw [HMap.find?_erase_ne _ _ _ (by simp [bne, hk])]

/-- Removing a freshly-added single binding from a non-empty stack recovers an
    `Equiv` stack. The `≠ []` hypothesis is essential: on the empty stack
    `addInNewest` creates a new scope, changing the count. -/
public theorem remove_addInNewest_single_fresh_equiv [LawfulBEq α] [LawfulHashable α]
    (ms : HMaps α β) (x : α) (v : β)
    (h_ne : ms ≠ []) (h_fresh : ∀ m, m ∈ ms → m.find? x = none) :
    Equiv ((ms.addInNewest (HMap.single x v)).remove x) ms := by
  cases ms with
  | nil => exact absurd rfl h_ne
  | cons scope rest =>
    simp only [HMaps.addInNewest, HMaps.remove]
    have h_scope_fresh : scope.find? x = none := h_fresh scope List.mem_cons_self
    refine ⟨fun k => ?_, remove_of_fresh_equiv rest x
      (fun m hm => h_fresh m (List.mem_cons_of_mem scope hm))⟩
    by_cases hk : k = x
    · subst hk; rw [HMap.find?_erase_self, h_scope_fresh]
    · rw [HMap.find?_erase_ne _ _ _ (by simp [bne, hk]), HMap.find?_union,
          HMap.find?_single_ne x k v (by simp [bne, hk]), Option.or_none]


end HMaps

end Strata.Util
