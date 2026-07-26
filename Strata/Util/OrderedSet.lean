/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Std.Data.HashSet.Basic

/-! # Insertion-ordered set

An array paired with a `Std.HashSet` membership index. The array is the source
of truth for iteration order; the set provides O(1) membership and
deduplication.

`OrderedKeyedSet key` (with `key : α → κ`) deduplicates elements of type `α` on
a projected key: two elements collide when their keys are equal.

`OrderedSet α` is the common special case where the key is the element itself
(`OrderedKeyedSet (id : α → α)`).

The two halves are kept in sync by building values only through the smart
constructors — `empty`, `ofArray`, `ofArrayUnchecked`, and growth via `insert`.
Since the raw constructor `mk` is private, external code cannot fabricate a
mismatched pair.

The methods `empty`, `insert`, and `ofArray` maintain full coherence.
Meanwhile, `ofArrayUnchecked` always builds a faithful index but stores its
array verbatim. Therefore, it is coherent only when the caller supplies
key-distinct elements.
-/

namespace Strata.Util

public structure OrderedKeyedSet {κ α : Type _} [BEq κ] [Hashable κ] (key : α → κ) where
  private mk ::
  /-- O(1) key index mirroring the keys of `values`. -/
  setIdx : Std.HashSet κ
  /-- Elements in insertion order (the source of truth). -/
  values : Array α

namespace OrderedKeyedSet

variable {κ α : Type _} [BEq κ] [Hashable κ] {key : α → κ}

/-- Show only the ordered `values`; the index is derived and its iteration order
    is unspecified. -/
public instance [Repr α] : Repr (OrderedKeyedSet key) where
  reprPrec s prec := reprPrec s.values prec

/-- Boolean equality on the ordered `values` (the source of truth). The derived
    key index is deliberately ignored. -/
public instance [BEq α] : BEq (OrderedKeyedSet key) where
  beq s t := s.values == t.values

/-- The empty collection. -/
public def empty : OrderedKeyedSet key := .mk {} #[]

public instance : Inhabited (OrderedKeyedSet key) := ⟨empty⟩

/-- Lets callers write `{}` for the empty collection. -/
public instance : EmptyCollection (OrderedKeyedSet key) := ⟨empty⟩

/-- O(1) membership test on a key. -/
public def containsKey (s : OrderedKeyedSet key) (k : κ) : Bool := s.setIdx.contains k

/-- O(1) membership test on an element, via its key. -/
public def contains (s : OrderedKeyedSet key) (a : α) : Bool := s.setIdx.contains (key a)

/-- Append `a` unless an element with the same key is already present (O(1) dedup). -/
public def insert (s : OrderedKeyedSet key) (a : α) : OrderedKeyedSet key :=
  let (contained, setIdx) := s.setIdx.containsThenInsert (key a)
  if contained then s
  else { s with setIdx, values := s.values.push a }

/-- Elements in insertion order. -/
public def toArray (s : OrderedKeyedSet key) : Array α := s.values

/-- Elements in insertion order. -/
public def toList (s : OrderedKeyedSet key) : List α := s.values.toList

/-- Number of elements. -/
public def size (s : OrderedKeyedSet key) : Nat := s.values.size

/-- Wrap an array by inserting its elements in order. Deduplicates on the key
    (first occurrence wins). -/
public def ofArray (xs : Array α) : OrderedKeyedSet key :=
  xs.foldl (init := empty) insert

/-- Wrap an array whose elements are already distinct, storing it verbatim. -/
public def ofArrayUnchecked (xs : Array α) : OrderedKeyedSet key :=
  .mk (Std.HashSet.ofList (xs.toList.map key)) xs

end OrderedKeyedSet

/-- Insertion-ordered set keyed on whole elements: the common case of
    `OrderedKeyedSet` where the deduplication key is the element itself. -/
public abbrev OrderedSet (α : Type _) [BEq α] [Hashable α] : Type _ :=
  OrderedKeyedSet (id : α → α)

namespace OrderedSet
variable {α : Type _} [BEq α] [Hashable α]

/-- The empty collection. -/
public def empty : OrderedSet α := OrderedKeyedSet.empty

/-- O(1) membership test on an element. -/
public def contains (s : OrderedSet α) (a : α) : Bool := OrderedKeyedSet.contains s a

/-- Append `a` unless it is already present (O(1) dedup). -/
public def insert (s : OrderedSet α) (a : α) : OrderedSet α := OrderedKeyedSet.insert s a

/-- Elements in insertion order. -/
public def toArray (s : OrderedSet α) : Array α := OrderedKeyedSet.toArray s

/-- Elements in insertion order. -/
public def toList (s : OrderedSet α) : List α := OrderedKeyedSet.toList s

/-- Number of elements. -/
public def size (s : OrderedSet α) : Nat := OrderedKeyedSet.size s

/-- Wrap an array, computing its key index in one pass. -/
public def ofArray (xs : Array α) : OrderedSet α := OrderedKeyedSet.ofArray xs

/-- Wrap an array whose elements are already distinct, storing it verbatim. -/
public def ofArrayUnchecked (xs : Array α) : OrderedSet α :=
  OrderedKeyedSet.ofArrayUnchecked xs

/-- Order-preserving deduplication backed by a hashed membership index.
    Keeps the first occurrence of each element. -/
public def eraseDups {α : Type _} [BEq α] [Hashable α] (xs : List α) : List α :=
  (xs.foldl OrderedSet.insert (OrderedSet.empty : OrderedSet α)).toList

end OrderedSet

/-- Well-formedness for `OrderedKeyedSet`, the two-part coherence invariant:
    *index faithfulness* (the key index reflects exactly the keys of the ordered
    elements) and *key injectivity* (those ordered elements have distinct keys).

    It cannot be asserted for an *arbitrary* value: `empty`, `insert`, and
    `ofArray` always yield well-formed sets, but `ofArrayUnchecked` stores its
    array verbatim and so is well-formed only when the input keys are distinct. -/
public structure OrderedKeyedSetWF {κ α : Type _} [BEq κ] [Hashable κ] {key : α → κ}
    (s : OrderedKeyedSet key) : Prop where
  /-- Index faithfulness: a key is in the index iff some element maps to it. -/
  containsKey_eq_any : ∀ k, s.containsKey k = s.toArray.any (fun a => key a == k)
  /-- Key injectivity: the ordered elements have pairwise-distinct keys. -/
  nodupKeys : (s.toList.map key).Nodup

end Strata.Util
