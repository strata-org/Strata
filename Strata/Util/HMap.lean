/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Std.Data.HashMap.Lemmas

/-!
A HashMap-backed finite map, used to make the typechecker's substitution/context
lookups O(1).

## Opacity

`HMap` is an OPAQUE single-field structure wrapping a `Std.HashMap`. It is
deliberately NOT `@[expose]`, and its field `rep` is `private`. Clients that
`public import` this module can only use the operations and the theorems below;
they cannot see or depend on the underlying representation. This lets the
backing be swapped (e.g. to an insertion-ordered map for deterministic test
output) without touching any client.

## Ordering discipline

`HMap` is UNORDERED. Its `keys`/`values`/`toList` have unspecified iteration
order, and NO theorem here may depend on that order. Order-sensitive facts
belong to the scope-stack (`HMaps`, a `List HMap`), never to a single `HMap`.
-/

open Std (ToFormat Format format)

namespace Strata.Util

/-- An opaque HashMap-backed map. The `rep` field is private so the
    representation stays hidden across module boundaries. -/
public structure HMap (α : Type u) (β : Type v) [BEq α] [Hashable α] where
  private mk ::
  private rep : Std.HashMap α β

namespace HMap

variable {α : Type u} {β : Type v} {γ : Type w} [BEq α] [Hashable α]

/-! ### Core operations -/

public def empty : HMap α β := ⟨Std.HashMap.emptyWithCapacity⟩

public instance : EmptyCollection (HMap α β) where
  emptyCollection := empty

public instance : Inhabited (HMap α β) where
  default := empty

public def insert (m : HMap α β) (a : α) (b : β) : HMap α β :=
  ⟨m.rep.insert a b⟩

/-- Look up the value at key `a`. -/
public def find? (m : HMap α β) (a : α) : Option β :=
  m.rep.get? a

/-- Remove key `a`. -/
public def erase (m : HMap α β) (a : α) : HMap α β :=
  ⟨m.rep.erase a⟩

public def contains (m : HMap α β) (a : α) : Bool :=
  m.rep.contains a

public def isEmpty (m : HMap α β) : Bool :=
  m.rep.isEmpty

public def size (m : HMap α β) : Nat :=
  m.rep.size

/-- Keys, in unspecified order. -/
public def keys (m : HMap α β) : List α :=
  m.rep.keys

/-- Entries, in unspecified order. -/
public def toList (m : HMap α β) : List (α × β) :=
  m.rep.toList

/-- Values, in unspecified order. Defined via `toList` so that value membership
    can be reasoned about through the `toList` lemmas. -/
public def values (m : HMap α β) : List β :=
  m.toList.map Prod.snd

public def ofList (l : List (α × β)) : HMap α β :=
  ⟨Std.HashMap.ofList l⟩

/-- A single-entry map. -/
public def single (a : α) (b : β) : HMap α β :=
  (empty : HMap α β).insert a b

/-- Check a predicate against every entry. -/
public def all (m : HMap α β) (p : α → β → Bool) : Bool :=
  m.rep.all p

/-- If `all p` holds and `find? k = some v`, then `p k v`. -/
public theorem all_of_find? [LawfulBEq α] [LawfulHashable α]
    {m : HMap α β} {p : α → β → Bool} (h_all : m.all p = true)
    {k : α} {v : β} (h_find : m.find? k = some v) : p k v = true := by
  simp only [all, Std.HashMap.all_eq_true_iff_forall_mem_getElem] at h_all
  have h_mem : k ∈ m.rep := by
    simp only [find?, Std.HashMap.get?_eq_getElem?] at h_find
    exact Std.HashMap.mem_iff_isSome_getElem?.mpr (by rw [h_find]; rfl)
  have h_get : m.rep[k]'h_mem = v := by
    simp only [find?, Std.HashMap.get?_eq_getElem?] at h_find
    have h_eq := Std.HashMap.getElem?_eq_some_getElem (m := m.rep) (a := k) h_mem
    rw [h_find] at h_eq
    exact (Option.some.inj h_eq).symm
  have := h_all k h_mem
  rw [h_get] at this
  exact this

/-- Merge `m2` into `m1`; on key collisions `m2` wins. -/
public def union (m1 m2 : HMap α β) : HMap α β :=
  ⟨m1.rep.insertMany m2.toList⟩

/-- Transform every value with `f`, leaving keys untouched. -/
public def mapValues (f : β → γ) (m : HMap α β) : HMap α γ :=
  ⟨m.rep.map (fun _ v => f v)⟩

/-! ### Instances -/

/-- Content equality via the underlying map's `BEq`. Like `Std.HashMap`, this is
    NOT lawful and there is deliberately no `DecidableEq` (see module docs). -/
public def beq [BEq β] (m1 m2 : HMap α β) : Bool := m1.rep == m2.rep

public instance [BEq β] : BEq (HMap α β) where
  beq := HMap.beq

/-- Show the entries. Goes through the public `toList`, so it needs no access to
    the private representation. -/
public instance [Repr α] [Repr β] : Repr (HMap α β) where
  reprPrec m := reprPrec m.toList

/-! ### Semantic lemmas -/

@[simp]
public theorem find?_empty (a : α) : (empty : HMap α β).find? a = none := by
  simp [find?, empty]

@[simp]
public theorem isEmpty_empty : (empty : HMap α β).isEmpty = true := by
  simp [isEmpty, empty]

@[simp]
public theorem keys_empty : (empty : HMap α β).keys = [] := by
  simp [keys, empty]

@[simp]
public theorem toList_empty : (empty : HMap α β).toList = [] := by
  simp [toList, empty]

@[simp]
public theorem values_empty : (empty : HMap α β).values = [] := by
  simp [values, toList_empty]

/-- Looking up a freshly inserted key returns the inserted value. -/
@[simp]
public theorem find?_insert_self [EquivBEq α] [LawfulHashable α]
    (m : HMap α β) (a : α) (b : β) :
    (m.insert a b).find? a = some b := by
  unfold find? insert
  simp

/-- Inserting at key `a` does not affect lookup at a different key `x ≠ a`. -/
public theorem find?_insert_ne [EquivBEq α] [LawfulHashable α]
    (m : HMap α β) (a x : α) (b : β) (h : x != a) :
    (m.insert a b).find? x = m.find? x := by
  unfold find? insert
  simp only [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert]
  have hx : (x == a) = false := by simpa [bne] using h
  have h' : (a == x) = false := by rw [BEq.comm]; exact hx
  simp [h']

/-- Looking up in an empty map returns `none`. -/
public theorem find?_of_isEmpty [EquivBEq α] [LawfulHashable α]
    (m : HMap α β) (a : α) (h : m.isEmpty) : m.find? a = none := by
  simp only [find?, Std.HashMap.get?_eq_getElem?]
  exact Std.HashMap.getElem?_of_isEmpty h

/-- After erasing key `a`, looking it up returns `none`. -/
@[simp]
public theorem find?_erase_self [EquivBEq α] [LawfulHashable α]
    (m : HMap α β) (a : α) :
    (m.erase a).find? a = none := by
  unfold find? erase
  simp

/-- Erasing key `a` does not affect lookup at a different key `x ≠ a`. -/
public theorem find?_erase_ne [EquivBEq α] [LawfulHashable α]
    (m : HMap α β) (a x : α) (h : x != a) :
    (m.erase a).find? x = m.find? x := by
  unfold find? erase
  simp only [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_erase]
  have hx : (x == a) = false := by simpa [bne] using h
  have h' : (a == x) = false := by rw [BEq.comm]; exact hx
  simp [h']

/-- Erasing shrinks the key set. -/
public theorem keys_erase_subset [LawfulBEq α] [LawfulHashable α]
    (m : HMap α β) (a : α) :
    ∀ k, k ∈ (m.erase a).keys → k ∈ m.keys := by
  intro k hk
  simp only [keys, erase] at hk ⊢
  rw [Std.HashMap.mem_keys] at hk ⊢
  exact Std.HashMap.mem_of_mem_erase hk

/-- A value is in `values` iff some key maps to it. -/
public theorem mem_values_iff_find? [LawfulBEq α] [LawfulHashable α]
    (m : HMap α β) (v : β) :
    v ∈ m.values ↔ ∃ k, m.find? k = some v := by
  simp only [values, find?, List.mem_map, toList]
  constructor
  · rintro ⟨⟨k, v'⟩, h_mem, rfl⟩
    exact ⟨k, (Std.HashMap.mem_toList_iff_getElem?_eq_some.mp h_mem)⟩
  · rintro ⟨k, hk⟩
    exact ⟨(k, v), Std.HashMap.mem_toList_iff_getElem?_eq_some.mpr hk, rfl⟩

/-- Erasing shrinks the value multiset (as a set of memberships). -/
public theorem values_erase_subset [LawfulBEq α] [LawfulHashable α]
    (m : HMap α β) (a : α) :
    ∀ v, v ∈ (m.erase a).values → v ∈ m.values := by
  intro v hv
  rw [mem_values_iff_find?] at hv ⊢
  obtain ⟨k, hk⟩ := hv
  by_cases h : k = a
  · subst h; rw [find?_erase_self] at hk; exact absurd hk (by simp)
  · refine ⟨k, ?_⟩
    rw [← hk, find?_erase_ne m a k (by simp [bne, h])]

/-! ### Key/value membership bridges

Relate `find?` to `keys`/`values` membership. -/

/-- Key membership is exactly "find? succeeds". -/
public theorem mem_keys_iff_find? [LawfulBEq α] [LawfulHashable α]
    (m : HMap α β) (k : α) :
    k ∈ m.keys ↔ ∃ v, m.find? k = some v := by
  simp only [keys, find?, Std.HashMap.mem_keys, Std.HashMap.get?_eq_getElem?,
    Std.HashMap.mem_iff_isSome_getElem?, Option.isSome_iff_exists]

/-- If `find?` returns `some v`, the key is in `keys`. -/
public theorem find?_mem_keys [LawfulBEq α] [LawfulHashable α]
    (m : HMap α β) (h : m.find? k = some v) : k ∈ m.keys :=
  (mem_keys_iff_find? m k).mpr ⟨v, h⟩

/-- If `find?` returns `some v`, the value is in `values`. -/
public theorem find?_mem_values [LawfulBEq α] [LawfulHashable α]
    (m : HMap α β) (h : m.find? k = some v) : v ∈ m.values :=
  (mem_values_iff_find? m v).mpr ⟨k, h⟩

/-- Value-mapping the source list commutes with `find?` on `ofList`: building the
    map from a list whose values have been transformed by `f` is the same as
    transforming the found value through `f`. -/
public theorem find?_ofList_map_snd [LawfulBEq α] [LawfulHashable α]
    (l : List (α × β)) (f : β → γ) (k : α) :
    HMap.find? (HMap.ofList (l.map (fun p => (p.1, f p.2)))) k =
      (HMap.find? (HMap.ofList l) k).map f := by
  simp only [find?, ofList, Std.HashMap.get?_eq_getElem?,
    Std.HashMap.ofList_eq_insertMany_empty, Std.HashMap.getElem?_insertMany_list,
    Std.HashMap.getElem?_empty, Option.or_none]
  rw [List.findSomeRev?_eq_findSome?_reverse, List.findSomeRev?_eq_findSome?_reverse,
    ← List.map_reverse]
  generalize l.reverse = l'
  induction l' with
  | nil => simp
  | cons p rest ih =>
    obtain ⟨a, b⟩ := p
    simp only [List.map_cons, List.findSome?_cons]
    by_cases hk : (a == k) = true
    · simp only [hk, if_true, Option.map_some]
    · simp only [hk, Bool.false_eq_true, if_false, ih]

/-- Every value of `HMap.ofList l` comes from a value in `l`. -/
public theorem mem_values_ofList [LawfulBEq α] [LawfulHashable α]
    (l : List (α × β)) (v : β) (h : v ∈ (HMap.ofList l).values) :
    v ∈ l.map Prod.snd := by
  obtain ⟨k, hk⟩ := (mem_values_iff_find? (HMap.ofList l) v).mp h
  simp only [find?, ofList, Std.HashMap.get?_eq_getElem?] at hk
  rw [Std.HashMap.ofList_eq_insertMany_empty, Std.HashMap.getElem?_insertMany_list,
      Std.HashMap.getElem?_empty, Option.or_none,
      List.findSomeRev?_eq_findSome?_reverse] at hk
  obtain ⟨p, hp_mem, hp_eq⟩ := List.exists_of_findSome?_eq_some hk
  obtain ⟨a, b⟩ := p
  simp only at hp_eq
  split at hp_eq
  · injection hp_eq with hbv; subst hbv
    rw [List.mem_reverse] at hp_mem
    exact List.mem_map_of_mem hp_mem
  · exact absurd hp_eq (by simp)

/-- `find?` returns `some` for any key present in `l`'s key list. -/
public theorem find?_ofList_of_mem_keys [LawfulBEq α] [LawfulHashable α]
    (l : List (α × β)) (k : α) (hk : k ∈ l.map Prod.fst) :
    ∃ v, HMap.find? (HMap.ofList l) k = some v := by
  rw [← mem_keys_iff_find?]
  simp only [keys, ofList, Std.HashMap.mem_keys]
  rw [Std.HashMap.mem_ofList]
  exact List.contains_iff_mem.mpr hk

/-- Every key of `HMap.ofList l` is a key in `l`. -/
public theorem mem_keys_ofList [LawfulBEq α] [LawfulHashable α]
    (l : List (α × β)) (k : α) (hk : k ∈ (HMap.ofList l).keys) :
    k ∈ l.map Prod.fst := by
  simp only [keys, ofList, Std.HashMap.mem_keys] at hk
  rw [Std.HashMap.mem_ofList] at hk
  exact List.contains_iff_mem.mp hk

/-- When `k0` is not among `l`'s keys, `ofList ((k0,v0) :: l)` agrees on `find?`
    with `(ofList l).insert k0 v0` at every key. (The no-duplicate-key condition
    rules out the case where a later `l` entry would shadow `k0`.) -/
public theorem find?_ofList_cons_eq_find?_insert [LawfulBEq α] [LawfulHashable α]
    (k0 : α) (v0 : β) (l : List (α × β)) (hnk : k0 ∉ l.map Prod.fst) (k : α) :
    HMap.find? (HMap.ofList ((k0, v0) :: l)) k =
      HMap.find? ((HMap.ofList l).insert k0 v0) k := by
  simp only [find?, ofList, insert, Std.HashMap.get?_eq_getElem?]
  rw [Std.HashMap.getElem?_insert, Std.HashMap.ofList_cons,
      Std.HashMap.getElem?_insertMany_list, Std.HashMap.ofList_eq_insertMany_empty,
      Std.HashMap.getElem?_insertMany_list, Std.HashMap.getElem?_insert,
      Std.HashMap.getElem?_empty]
  have hnone : (l.findSomeRev? (fun x => if x.1 == k then some x.2 else none)) = none
      ∨ (k0 == k) = false := by
    by_cases hk : (k0 == k) = true
    · left
      have hkk : k = k0 := (beq_iff_eq.mp hk).symm
      rw [List.findSomeRev?_eq_findSome?_reverse, List.findSome?_eq_none_iff]
      intro x hx
      have hxne : x.1 ≠ k := by
        intro he; rw [hkk] at he
        exact hnk (he ▸ List.mem_map_of_mem (List.mem_reverse.mp hx))
      simp [hxne]
    · right; simpa using hk
  rcases hnone with h | h
  · rw [h]; simp
  · simp only [h, Bool.false_eq_true, if_false, Option.or_none]

/-- If `find?` returns `none`, the key is not in `keys`. -/
public theorem find?_of_not_mem_keys [LawfulBEq α] [LawfulHashable α]
    (m : HMap α β) (h : m.find? k = none) : k ∉ m.keys := by
  intro hk
  obtain ⟨v, hv⟩ := (mem_keys_iff_find? m k).mp hk
  rw [hv] at h; exact absurd h (by simp)

/-- `find?` returns `none` when the key is not in `keys`. -/
public theorem not_mem_keys_find?_none [LawfulBEq α] [LawfulHashable α]
    (m : HMap α β) (k : α) (h : k ∉ m.keys) : m.find? k = none := by
  cases hf : m.find? k with
  | none => rfl
  | some v => exact absurd (find?_mem_keys m hf) h

/-- Erasing a different key preserves key membership. -/
public theorem keys_erase_mem_of_ne [LawfulBEq α] [LawfulHashable α]
    (m : HMap α β) {a x : α} (h_mem : a ∈ m.keys) (h_ne : a ≠ x) :
    a ∈ (m.erase x).keys := by
  obtain ⟨v, hv⟩ := (mem_keys_iff_find? m a).mp h_mem
  refine (mem_keys_iff_find? (m.erase x) a).mpr ⟨v, ?_⟩
  rw [find?_erase_ne m x a (by simp [bne, h_ne]), hv]

/-! ### Insert key/value subset lemmas

These bound the key/value sets after an `insert`. -/

/-- Inserting can only add `key` to the key set. -/
public theorem insert_keys_subset [LawfulBEq α] [LawfulHashable α]
    (m : HMap α β) (key : α) (val : β) :
    ∀ k, k ∈ (m.insert key val).keys → k ∈ key :: m.keys := by
  intro k hk
  simp only [keys, insert] at hk
  rw [Std.HashMap.mem_keys] at hk
  rw [Std.HashMap.mem_insert] at hk
  rcases hk with h | h
  · rw [LawfulBEq.eq_of_beq h]; exact List.mem_cons_self
  · exact List.mem_cons_of_mem _ (by rw [mem_keys_iff_find?]; rw [Std.HashMap.mem_iff_isSome_getElem?, Option.isSome_iff_exists] at h; simpa [find?, Std.HashMap.get?_eq_getElem?] using h)

/-- Inserting can only add `val` to the value set. -/
public theorem insert_values_subset [LawfulBEq α] [LawfulHashable α]
    (m : HMap α β) (key : α) (val : β) :
    ∀ v, v ∈ (m.insert key val).values → v ∈ val :: m.values := by
  intro v hv
  rw [mem_values_iff_find?] at hv
  obtain ⟨k, hk⟩ := hv
  by_cases h : k = key
  · subst h; rw [find?_insert_self] at hk; injection hk with hk; subst hk; exact List.mem_cons_self
  · refine List.mem_cons_of_mem _ ?_
    rw [mem_values_iff_find?]
    exact ⟨k, by rw [← hk, find?_insert_ne m key k val (by simp [bne, h])]⟩

/-! ### `union` lookup law -/

/-- Looking up in `union m1 m2` returns `m2`'s binding if present, else `m1`'s. -/
public theorem find?_union [LawfulBEq α] [LawfulHashable α]
    (m1 m2 : HMap α β) (k : α) :
    (m1.union m2).find? k = (m2.find? k).or (m1.find? k) := by
  simp only [find?, union, toList, Std.HashMap.get?_eq_getElem?]
  cases hk : m2.rep[k]? with
  | some v =>
    have h_mem : (⟨k, v⟩ : α × β) ∈ m2.rep.toList :=
      Std.HashMap.mem_toList_iff_getElem?_eq_some.mpr hk
    rw [Std.HashMap.getElem?_insertMany_list_of_mem (k_beq := BEq.refl k)
      Std.HashMap.distinct_keys_toList h_mem]
    simp
  | none =>
    have h_notmem : ¬ k ∈ m2.rep := by
      rw [Std.HashMap.mem_iff_isSome_getElem?, hk]; simp
    have h_nc : (m2.rep.toList.map Prod.fst).contains k = false := by
      rw [Std.HashMap.map_fst_toList_eq_keys]
      simp only [List.contains_eq_mem, decide_eq_false_iff_not, Std.HashMap.mem_keys]
      exact h_notmem
    rw [Std.HashMap.getElem?_insertMany_list_of_contains_eq_false h_nc]
    simp

/-- `union` unites the key sets. -/
public theorem mem_keys_union [LawfulBEq α] [LawfulHashable α]
    (m1 m2 : HMap α β) (k : α) :
    k ∈ (m1.union m2).keys ↔ k ∈ m1.keys ∨ k ∈ m2.keys := by
  rw [mem_keys_iff_find?, mem_keys_iff_find?, mem_keys_iff_find?, find?_union]
  cases h2 : m2.find? k <;> cases h1 : m1.find? k <;> simp_all

/-! ### `mapValues` lookup law -/

/-- Looking up in `mapValues f m` maps the found value through `f`. -/
@[simp]
public theorem find?_mapValues [LawfulBEq α] [LawfulHashable α]
    (f : β → γ) (m : HMap α β) (k : α) :
    (m.mapValues f).find? k = (m.find? k).map f := by
  simp only [find?, mapValues, Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_map]

/-- `mapValues` preserves the key set (as membership). -/
public theorem mem_keys_mapValues_iff [LawfulBEq α] [LawfulHashable α]
    (f : β → γ) (m : HMap α β) (k : α) :
    k ∈ (m.mapValues f).keys ↔ k ∈ m.keys := by
  rw [mem_keys_iff_find?, mem_keys_iff_find?]
  constructor
  · rintro ⟨v, hv⟩; rw [find?_mapValues] at hv
    exact (Option.map_eq_some_iff.mp hv).imp (fun _ h => h.1)
  · rintro ⟨v, hv⟩; exact ⟨f v, by rw [find?_mapValues, hv]; rfl⟩

/-! ### `single` lookup lemmas -/

@[simp]
public theorem find?_single_self [EquivBEq α] [LawfulHashable α]
    (a : α) (b : β) : (single a b).find? a = some b := by
  simp [single, find?_insert_self]

public theorem find?_single_ne [EquivBEq α] [LawfulHashable α]
    (a x : α) (b : β) (h : x != a) : (single a b).find? x = none := by
  simp only [single]
  rw [find?_insert_ne _ a x b h, find?_empty]

/-- `single a b` has exactly key `a`. -/
public theorem mem_keys_single_iff [LawfulBEq α] [LawfulHashable α]
    (a x : α) (b : β) : x ∈ (single a b).keys ↔ x = a := by
  rw [mem_keys_iff_find?]
  constructor
  · rintro ⟨v, hv⟩
    by_cases h : x = a
    · exact h
    · rw [find?_single_ne a x b (by simp [bne, h])] at hv; exact absurd hv (by simp)
  · rintro rfl; exact ⟨b, find?_single_self x b⟩

/-- `single a b` has exactly value `b`. -/
public theorem mem_values_single_iff [LawfulBEq α] [LawfulHashable α]
    (a : α) (b v : β) : v ∈ (single a b).values ↔ v = b := by
  rw [mem_values_iff_find?]
  constructor
  · rintro ⟨k, hk⟩
    by_cases h : k = a
    · subst h; rw [find?_single_self] at hk; injection hk with hk; exact hk.symm
    · rw [find?_single_ne a k b (by simp [bne, h])] at hk; exact absurd hk (by simp)
  · rintro rfl; exact ⟨a, find?_single_self a v⟩

/-- A value is in `(mapValues f m).values` iff it is `f` of some value of `m`. -/
public theorem mem_values_mapValues [LawfulBEq α] [LawfulHashable α]
    (f : β → γ) (m : HMap α β) (w : γ) :
    w ∈ (m.mapValues f).values ↔ ∃ v, v ∈ m.values ∧ w = f v := by
  rw [mem_values_iff_find?]
  constructor
  · rintro ⟨k, hk⟩
    rw [find?_mapValues] at hk
    obtain ⟨v, hv, hwv⟩ := Option.map_eq_some_iff.mp hk
    exact ⟨v, find?_mem_values m hv, hwv.symm⟩
  · rintro ⟨v, hv, rfl⟩
    obtain ⟨k, hk⟩ := (mem_values_iff_find? m v).mp hv
    exact ⟨k, by rw [find?_mapValues, hk]; rfl⟩

/-! ### `Equiv` (lookup agreement) -/

/-- Two maps are equivalent when they agree on every lookup. Since a single
    `HMap` has unique keys, this determines both its key set and its value
    multiset. -/
public def Equiv (m m' : HMap α β) : Prop := ∀ k, m.find? k = m'.find? k

@[refl] public theorem Equiv.refl (m : HMap α β) : Equiv m m := fun _ => rfl

public theorem Equiv.symm {m m' : HMap α β} (h : Equiv m m') : Equiv m' m :=
  fun k => (h k).symm

public theorem Equiv.trans {m m' m'' : HMap α β}
    (h1 : Equiv m m') (h2 : Equiv m' m'') : Equiv m m'' :=
  fun k => (h1 k).trans (h2 k)

/-- `mapValues` preserves `Equiv`. -/
public theorem mapValues_equiv [LawfulBEq α] [LawfulHashable α]
    (f : β → γ) {m m' : HMap α β} (h : Equiv m m') :
    Equiv (m.mapValues f) (m'.mapValues f) := by
  intro k; rw [HMap.find?_mapValues, HMap.find?_mapValues, h k]

/-- `insert` preserves `Equiv`. -/
public theorem insert_equiv [LawfulBEq α] [LawfulHashable α]
    {m m' : HMap α β} (h : Equiv m m') (x : α) (v : β) :
    Equiv (m.insert x v) (m'.insert x v) := by
  intro k
  by_cases hk : k = x
  · subst hk; rw [HMap.find?_insert_self, HMap.find?_insert_self]
  · rw [HMap.find?_insert_ne _ _ _ _ (by simp [bne, hk]),
        HMap.find?_insert_ne _ _ _ _ (by simp [bne, hk])]
    exact h k

end HMap

end Strata.Util
