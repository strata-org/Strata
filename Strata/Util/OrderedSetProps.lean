/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import Strata.Util.OrderedSet
import all Strata.Util.OrderedSet
import Strata.Util.ListProps
import Std.Data.HashSet.Lemmas

/-!
# Coherence proofs for `OrderedKeyedSet`

`OrderedKeyedSet` keeps a `Std.HashSet` key index (`setIdx`) alongside the
ordered `values`. The module enforces — by construction, via the private
constructor — that the index mirrors the keys of the elements.

The file culminates in a two-part coherence characterization: the
`OrderedKeyedSetWF` predicate captures both *index-faithfulness* (the key index
reflects exactly the keys of the ordered elements) and *key-injectivity* (the
ordered values have pairwise-distinct keys). From these, we show the index and
the ordered values always agree in size.

## Key theorems

* `empty_wf`, `insert_wf`, `ofArray_wf` — the smart constructors preserve
  well-formedness; `ofArrayUnchecked_wf` does so given key-distinct input.
* `size_setIdx_eq_size` — in a well-formed set the key index and the
  ordered values have equal cardinality.
-/

namespace Strata.Util
namespace OrderedKeyedSet

variable {κ α : Type _} [BEq κ] [Hashable κ] {key : α → κ}

/-- The empty collection contains no key. -/
theorem containsKey_empty (k : κ) :
    (empty : OrderedKeyedSet key).containsKey k = false := by
  simp only [containsKey, empty, Std.HashSet.contains_empty]

/-- The `containsThenInsert` call inside `insert` splits into the pre-insert
    membership flag and the extended index. Every `insert` characterization below
    unfolds through this. -/
private theorem containsThenInsert_eq (s : OrderedKeyedSet key) (a : α) :
    s.setIdx.containsThenInsert (key a)
      = (s.setIdx.contains (key a), s.setIdx.insert (key a)) :=
  Prod.ext Std.HashSet.containsThenInsert_fst Std.HashSet.containsThenInsert_snd

/-- `insert` extends the index by exactly the inserted element's key. -/
theorem containsKey_insert [EquivBEq κ] [LawfulHashable κ]
    (s : OrderedKeyedSet key) (a : α) (k : κ) :
    (s.insert a).containsKey k = (s.containsKey k || (key a == k)) := by
  simp only [insert, containsKey, containsThenInsert_eq]
  split <;> rename_i h
  · -- Already present: `insert` is a no-op, so the index is unchanged.
    by_cases hk : (key a == k) = true
    · simp only [Std.HashSet.contains_congr hk ▸ h, Bool.true_or]
    · simp only [Bool.not_eq_true] at hk; simp [hk]
  · -- Fresh key: the extended index gains exactly `key a`.
    simp only [Std.HashSet.contains_insert]
    exact Bool.or_comm _ _

/-- Element-level form of `containsKey_empty`. -/
theorem contains_empty (a : α) :
    (empty : OrderedKeyedSet key).contains a = false :=
  containsKey_empty (key a)

/-- Element-level form of `containsKey_insert`. -/
theorem contains_insert [EquivBEq κ] [LawfulHashable κ]
    (s : OrderedKeyedSet key) (b a : α) :
    (s.insert b).contains a = (s.contains a || (key b == key a)) :=
  containsKey_insert s b (key a)

/-- `insert` never drops an already-present element (monotonicity). -/
theorem contains_insert_mono [EquivBEq κ] [LawfulHashable κ]
    (s : OrderedKeyedSet key) (b : α) {a : α} (h : s.contains a = true) :
    (s.insert b).contains a = true := by
  rw [contains_insert, h]
  simp only [Bool.true_or]

/-- `insert` only touches its own key: an absent element with a different key
    stays absent. -/
theorem not_contains_insert [LawfulBEq κ] [LawfulHashable κ]
    (s : OrderedKeyedSet key) (b : α) {a : α}
    (ha : s.contains a = false) (hne : key b ≠ key a) :
    (s.insert b).contains a = false := by
  simp [contains_insert, ha, hne]

/-- `contains` is `containsKey` at the projected key. -/
theorem contains_eq_containsKey (s : OrderedKeyedSet key) (a : α) :
    s.contains a = s.containsKey (key a) := rfl

/-- Inserting an element whose key is already present is a no-op.  -/
theorem insert_of_contains (s : OrderedKeyedSet key) (a : α)
    (h : s.contains a = true) : s.insert a = s := by
  have h' : s.setIdx.contains (key a) = true := h
  simp only [insert, containsThenInsert_eq]
  split
  · rfl
  · rename_i hcon; exact absurd h' hcon

/-- After inserting `a`, its key is present. -/
theorem contains_insert_self [EquivBEq κ] [LawfulHashable κ]
    (s : OrderedKeyedSet key) (a : α) : (s.insert a).contains a = true := by
  rw [contains_insert]; simp only [BEq.rfl, Bool.or_true]

/-- `insert` is idempotent. -/
theorem insert_idem [EquivBEq κ] [LawfulHashable κ]
    (s : OrderedKeyedSet key) (a : α) : (s.insert a).insert a = s.insert a :=
  insert_of_contains (s.insert a) a (contains_insert_self s a)

/-! ### Element-array characterization

These describe how the *ordered values* (the source of truth) evolve — the
array-side counterpart to the index-membership lemmas above. Together they show
the array and its index stay in step. -/

/-- `toList` is `toArray` viewed as a list. -/
theorem toList_eq_toArray_toList (s : OrderedKeyedSet key) :
    s.toList = s.toArray.toList := rfl

theorem toArray_empty : (empty : OrderedKeyedSet key).toArray = #[] := rfl
theorem toList_empty : (empty : OrderedKeyedSet key).toList = [] := rfl

/-! ### `ofArrayUnchecked` characterization -/

/-- `ofArrayUnchecked` stores its argument verbatim, so recovering the ordered
    elements is definitional. -/
theorem toArray_ofArrayUnchecked (xs : Array α) :
    (ofArrayUnchecked xs : OrderedKeyedSet key).toArray = xs := rfl

theorem toList_ofArrayUnchecked (xs : Array α) :
    (ofArrayUnchecked xs : OrderedKeyedSet key).toList = xs.toList := rfl

/-- `ofArrayUnchecked`'s index is exactly `Std.HashSet.ofList` of the projected
    keys, so membership is decided by the key list. -/
theorem containsKey_ofArrayUnchecked [LawfulBEq κ] [LawfulHashable κ]
    (xs : Array α) (k : κ) :
    (ofArrayUnchecked xs : OrderedKeyedSet key).containsKey k
      = (xs.toList.map key).contains k := by
  show (Std.HashSet.ofList (xs.toList.map key)).contains k = (xs.toList.map key).contains k
  exact Std.HashSet.contains_ofList

/-- `insert` appends the element unless its key is already present. -/
theorem toArray_insert (s : OrderedKeyedSet key) (a : α) :
    (s.insert a).toArray = if s.contains a then s.toArray else s.toArray.push a := by
  simp only [insert, toArray, contains, containsThenInsert_eq]
  split <;> rfl

/-- When the key is fresh, `insert` pushes the element onto the array. -/
theorem toArray_insert_of_not_contains (s : OrderedKeyedSet key) (a : α)
    (h : s.contains a = false) : (s.insert a).toArray = s.toArray.push a := by
  simp only [toArray_insert, h, Bool.false_eq_true, ↓reduceIte]

/-- `insert` appends the element unless its key is already present. -/
theorem toList_insert (s : OrderedKeyedSet key) (a : α) :
    (s.insert a).toList = if s.contains a then s.toList else s.toList ++ [a] := by
  rw [toList_eq_toArray_toList, toArray_insert]
  split <;> simp only [toList_eq_toArray_toList, Array.toList_push]

/-- When the key is fresh, `insert` appends the element to the ordered list. -/
theorem toList_insert_of_not_contains (s : OrderedKeyedSet key) (a : α)
    (h : s.contains a = false) : (s.insert a).toList = s.toList ++ [a] := by
  rw [toList_eq_toArray_toList, toArray_insert_of_not_contains s a h, Array.toList_push,
      ← toList_eq_toArray_toList]

/-- `size` counts the elements of `toList`. -/
theorem length_toList (s : OrderedKeyedSet key) : s.toList.length = s.size := by
  simp only [toList, size, Array.length_toList]

/-! ### `ofArray` coverage

`ofArray` folds `insert`, so it deduplicates first-wins. It does *not* preserve the input array verbatim
(colliding keys collapse), but it covers every input key. -/

/-- Folding `insert` never drops an element already in the accumulator. -/
private theorem contains_foldl_insert_mono [EquivBEq κ] [LawfulHashable κ]
    (l : List α) {s : OrderedKeyedSet key} {a : α} (h : s.contains a = true) :
    (l.foldl insert s).contains a = true := by
  induction l generalizing s with
  | nil => simpa using h
  | cons b t ih => rw [List.foldl_cons]; exact ih (contains_insert_mono s b h)

/-- Every element of the list is `contains`-visible after folding `insert`.
    Split the list at `a`: the fold inserts it, then monotonicity carries it
    through the remaining elements. -/
private theorem contains_foldl_insert_of_mem [EquivBEq κ] [LawfulHashable κ]
    (l : List α) {s : OrderedKeyedSet key} {a : α} (ha : a ∈ l) :
    (l.foldl insert s).contains a = true := by
  have ⟨p, q, hpq⟩ := List.append_of_mem ha
  rw [hpq, List.foldl_append, List.foldl_cons]
  exact contains_foldl_insert_mono q (contains_insert_self _ a)

/-- Every element of the input array is `contains`-visible in `ofArray xs`, which
    just folds `insert` over the array. -/
theorem contains_ofArray_of_mem [EquivBEq κ] [LawfulHashable κ]
    {xs : Array α} {a : α} (ha : a ∈ xs) :
    (ofArray xs : OrderedKeyedSet key).contains a = true := by
  rw [ofArray, ← Array.foldl_toList]
  exact contains_foldl_insert_of_mem xs.toList (by simpa using ha)

/-! ### Ordered-list recovery for distinct-keyed inputs

When inserting the input, if their projected keys are pairwise distinct, no dedup fires and
the input array is recovered verbatim. -/

/-- Folding `insert` over a key-distinct list into a set that shares none of its
    keys appends the list verbatim. -/
private theorem toList_foldl_insert_of_nodup [LawfulBEq κ] [LawfulHashable κ]
    (l : List α) {s : OrderedKeyedSet key}
    (hs : ∀ a ∈ l, s.contains a = false) (hnodup : (l.map key).Nodup) :
    (l.foldl insert s).toList = s.toList ++ l := by
  induction l generalizing s with
  | nil => simp only [List.foldl_nil, List.append_nil]
  | cons a t ih =>
    rw [List.map_cons, List.nodup_cons] at hnodup
    have hsa : s.contains a = false := hs a (by simp only [List.mem_cons, true_or])
    have hs' : ∀ b ∈ t, (s.insert a).contains b = false := by
      intro b hb
      have hsb : s.contains b = false := hs b (List.mem_cons_of_mem a hb)
      have hne : key a ≠ key b :=
        (ne_of_mem_of_not_mem (List.mem_map_of_mem (f := key) hb) hnodup.1).symm
      exact not_contains_insert s a hsb hne
    rw [List.foldl_cons, ih hs' hnodup.2, toList_insert_of_not_contains s a hsa,
        List.append_assoc]
    rfl

/-- When the input's projected keys are distinct, `ofArray` recovers the input
    array as its ordered `toList`. -/
theorem toList_ofArray_of_keys_nodup [LawfulBEq κ] [LawfulHashable κ]
    {xs : Array α} (h : (xs.toList.map key).Nodup) :
    (ofArray xs : OrderedKeyedSet key).toList = xs.toList := by
  rw [ofArray, ← Array.foldl_toList,
      toList_foldl_insert_of_nodup xs.toList (fun a _ => contains_empty a) h,
      toList_empty, List.nil_append]

/-- Array-level form of `toList_ofArray_of_keys_nodup`: with distinct keys,
    `ofArray` recovers the input array verbatim as its ordered `values`. -/
theorem toArray_ofArray_of_keys_nodup [LawfulBEq κ] [LawfulHashable κ]
    {xs : Array α} (h : (xs.toList.map key).Nodup) :
    (ofArray xs : OrderedKeyedSet key).toArray = xs := by
  apply Array.toList_inj.mp
  rw [← toList_eq_toArray_toList]
  exact toList_ofArray_of_keys_nodup h

/-- With distinct keys, `ofArrayUnchecked` and `ofArray` produce `BEq`-equal
    sets: both store the input's elements in order. -/
theorem ofArrayUnchecked_beq_ofArray [LawfulBEq κ] [LawfulHashable κ] [BEq α] [LawfulBEq α]
    {xs : Array α} (h : (xs.toList.map key).Nodup) :
    ((ofArrayUnchecked xs : OrderedKeyedSet key) == ofArray xs) = true := by
  show ((ofArrayUnchecked xs : OrderedKeyedSet key).values == (ofArray xs).values) = true
  have hu : (ofArrayUnchecked xs : OrderedKeyedSet key).values = xs := rfl
  have ho : (ofArray xs : OrderedKeyedSet key).values = xs := toArray_ofArray_of_keys_nodup h
  rw [hu, ho, beq_self_eq_true]

end OrderedKeyedSet

/-! ## `OrderedSet` specializations

`OrderedSet α = OrderedKeyedSet (id : α → α)`, so each lemma specializes the
`OrderedKeyedSet` one at `key = id` (where `key a == key b` becomes `a == b`). -/

namespace OrderedSet

variable {α : Type _} [BEq α] [Hashable α]

theorem toList_empty : (empty : OrderedSet α).toList = [] :=
  OrderedKeyedSet.toList_empty

theorem toList_ofArray_of_nodup [LawfulBEq α] [LawfulHashable α] {xs : Array α}
    (h : xs.toList.Nodup) : (ofArray xs : OrderedSet α).toList = xs.toList :=
  OrderedKeyedSet.toList_ofArray_of_keys_nodup (by simpa using h)

/-- With distinct elements, `ofArrayUnchecked` and `ofArray` agree up to `==`. -/
theorem ofArrayUnchecked_beq_ofArray [LawfulBEq α] [LawfulHashable α] {xs : Array α}
    (h : xs.toList.Nodup) :
    ((ofArrayUnchecked xs : OrderedSet α) == ofArray xs) = true := by
  apply OrderedKeyedSet.ofArrayUnchecked_beq_ofArray
  rw [List.map_id]
  exact h

end OrderedSet

/-! ## Well-formedness

`OrderedKeyedSetWF` is a predicate over an existing `OrderedKeyedSet` capturing the
coherence invariant. It cannot be asserted for an *arbitrary* value: `empty`,
`insert`, and `ofArray` always yield well-formed sets, but `ofArrayUnchecked`
stores its array verbatim and so is well-formed only when the input keys are
distinct (see `ofArrayUnchecked_wf`). -/

open OrderedKeyedSet

variable {κ α : Type _} [BEq κ] [Hashable κ] {key : α → κ}

namespace OrderedKeyedSetWF

/-- The empty collection is well-formed. -/
public theorem empty_wf : OrderedKeyedSetWF (OrderedKeyedSet.empty : OrderedKeyedSet key) where
  containsKey_eq_any := by
    simp only [containsKey_empty, toArray_empty, List.size_toArray, List.length_nil,
      List.any_toArray', List.any_nil, implies_true]
  nodupKeys := by rw [toList_empty]; simp only [List.map_nil, List.nodup_nil]

/-- Propositional form of index faithfulness: a key is among the projected keys
    of the ordered elements iff the index reports it. -/
theorem mem_map_key_iff_containsKey [LawfulBEq κ] {s : OrderedKeyedSet key}
    (h : OrderedKeyedSetWF s) (k : κ) :
    k ∈ s.toList.map key ↔ s.containsKey k = true := by
  rw [h.containsKey_eq_any k]
  simp only [Array.any_eq_true', List.mem_map, toList_eq_toArray_toList,
             Array.mem_toList_iff, beq_iff_eq]

/-- Well-formedness is preserved by `insert`. `LawfulBEq` is needed to line up
    key-distinctness (an `Eq` fact) with the `==` membership test. -/
public theorem insert_wf [LawfulBEq κ] [LawfulHashable κ] {s : OrderedKeyedSet key}
    (h : OrderedKeyedSetWF s) (a : α) : OrderedKeyedSetWF (s.insert a) := by
  by_cases hc : s.contains a = true
  · -- Already present: `insert` is a no-op, so well-formedness transfers verbatim.
    rwa [insert_of_contains s a hc]
  · -- Fresh key: `insert` genuinely appends `a`; each invariant only has to cover
    -- the append (the `if`'s already-present branch contradicts `hc`).
    have hcf : s.contains a = false := by simpa using hc
    refine { containsKey_eq_any := ?_, nodupKeys := ?_ }
    · -- index faithfulness: the index gains exactly `key a`, matching the pushed
      -- element.
      intro k
      rw [containsKey_insert, toArray_insert_of_not_contains s a hcf, Array.any_push,
          ← h.containsKey_eq_any k]
    · -- key injectivity: `a` is appended, and its key is new (nothing already
      -- carries it, since `s` did not contain `a`).
      rw [toList_insert_of_not_contains s a hcf, List.map_append, List.map_cons, List.map_nil]
      have hnotin : key a ∉ s.toList.map key := by
        rw [mem_map_key_iff_containsKey h, ← contains_eq_containsKey, hcf]
        simp
      -- `s.toList.map key ++ [key a]` is nodup: the left part is nodup, and every
      -- existing projected key differs from the fresh `key a`.
      have hdisjoint : ∀ x ∈ s.toList.map key, ∀ y ∈ [key a], x ≠ y := by
        intro x hx y hy
        rw [List.mem_singleton] at hy
        subst hy
        exact ne_of_mem_of_not_mem hx hnotin
      exact List.nodup_append.mpr ⟨h.nodupKeys, by simp only [List.nodup_cons, List.not_mem_nil,
        not_false_eq_true, List.nodup_nil, and_self], hdisjoint⟩

private theorem foldl_insert [LawfulBEq κ] [LawfulHashable κ] (l : List α)
    {s : OrderedKeyedSet key} (h : OrderedKeyedSetWF s) :
    OrderedKeyedSetWF (l.foldl OrderedKeyedSet.insert s) := by
  induction l generalizing s with
  | nil => simpa using h
  | cons a t ih => rw [List.foldl_cons]; exact ih (insert_wf h a)

/-- `ofArray` is well-formed. It folds `insert`, so well-formedness is preserved
    from `empty` through each element. -/
public theorem ofArray_wf [LawfulBEq κ] [LawfulHashable κ] (xs : Array α) :
    OrderedKeyedSetWF (OrderedKeyedSet.ofArray xs : OrderedKeyedSet key) := by
  rw [OrderedKeyedSet.ofArray, ← Array.foldl_toList]
  exact foldl_insert xs.toList OrderedKeyedSetWF.empty_wf

/-- `ofArrayUnchecked` is well-formed *provided its keys are distinct*. -/
public theorem ofArrayUnchecked_wf [LawfulBEq κ] [LawfulHashable κ] {xs : Array α}
    (h : (xs.toList.map key).Nodup) :
    OrderedKeyedSetWF (OrderedKeyedSet.ofArrayUnchecked xs : OrderedKeyedSet key) where
  containsKey_eq_any k := by
    rw [containsKey_ofArrayUnchecked, toArray_ofArrayUnchecked]
    simp only [List.contains_eq_any_beq, List.any_map, Function.comp_def,
               Array.any_toList, Bool.beq_comm]
  nodupKeys := by rw [toList_ofArrayUnchecked]; exact h

/-- Element-level coherence: in a well-formed set, `contains a` is exactly
    "some element shares `a`'s key".  -/
theorem contains_eq_any {s : OrderedKeyedSet key} (h : OrderedKeyedSetWF s) (a : α) :
    s.contains a = s.toArray.any (fun b => key b == key a) :=
  h.containsKey_eq_any (key a)

/-- `==`-equal well-formed sets agree on `containsKey` everywhere. -/
theorem containsKey_congr_of_beq [BEq α] [LawfulBEq α] {s t : OrderedKeyedSet key}
    (hs : OrderedKeyedSetWF s) (ht : OrderedKeyedSetWF t)
    (h : (s == t) = true) (k : κ) :
    s.containsKey k = t.containsKey k := by
  have hv : s.values = t.values := by
    simp only [BEq.beq] at h
    exact eq_of_beq h
  rw [hs.containsKey_eq_any k, ht.containsKey_eq_any k]
  simp only [OrderedKeyedSet.toArray, hv]

/-- `==`-equal well-formed sets agree on `contains` everywhere. -/
theorem contains_congr_of_beq [BEq α] [LawfulBEq α] {s t : OrderedKeyedSet key}
    (hs : OrderedKeyedSetWF s) (ht : OrderedKeyedSetWF t)
    (h : (s == t) = true) (a : α) :
    s.contains a = t.contains a :=
  containsKey_congr_of_beq hs ht h (key a)

/-- In a well-formed set, an element present in the ordered list is seen by
    `contains`. -/
theorem contains_of_mem_toArray [ReflBEq κ] {s : OrderedKeyedSet key}
    (h : OrderedKeyedSetWF s) {a : α} (ha : a ∈ s.toArray) : s.contains a = true := by
  rw [contains_eq_any h, Array.any_eq_true']
  exact ⟨a, ha, by simp⟩

/-- In a well-formed set the O(1) key index and the ordered elements
    have equal cardinality: the index neither drops nor duplicates
    anything relative to the ordered source of truth. -/
theorem size_setIdx_eq_size [LawfulBEq κ] [LawfulHashable κ]
    {s : OrderedKeyedSet key} (h : OrderedKeyedSetWF s) :
    s.setIdx.size = s.size := by
  have hmemiff : ∀ k, k ∈ s.setIdx.toList ↔ k ∈ s.toList.map key := by
    intro k
    rw [Std.HashSet.mem_toList, Std.HashSet.mem_iff_contains]
    change s.containsKey k = true ↔ k ∈ s.toList.map key
    rw [mem_map_key_iff_containsKey h]
  -- The index's key list is `Nodup`: its elements are pairwise `==`-distinct,
  -- and under `LawfulBEq` that is genuine inequality.
  have hdistinct : s.setIdx.toList.Pairwise (fun a b => (a == b) = false) :=
    Std.HashSet.distinct_toList
  have hbeq_false_imp_ne : ∀ {a b : κ}, (a == b) = false → a ≠ b := by
    intro a b hab he
    subst he
    simp only [BEq.rfl, Bool.true_eq_false] at hab
  have hnodup₁ : s.setIdx.toList.Nodup := hdistinct.imp hbeq_false_imp_ne
  have hlen := List.length_eq_of_nodup_of_mem_iff hnodup₁ h.nodupKeys hmemiff
  rw [← Std.HashSet.length_toList, hlen, List.length_map, length_toList]

end OrderedKeyedSetWF
end Strata.Util
