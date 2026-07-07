/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Std.Data.HashSet.Basic

/-! # Insertion-ordered set

An array paired with a `Std.HashSet` membership index over the same elements.
The array is the source of truth for iteration order; the set provides O(1)
membership and deduplication.

The two halves are kept in sync by only ever building values through
`empty`/`ofArray` and growing them through `insert`, each of which updates the
array and its index together. Callers read the elements through
`toArray`/`toList` and never construct the pair by hand.
-/

namespace Strata.Util

public structure OrderedSet (α : Type _) [BEq α] [Hashable α] where
  /-- O(1) membership index mirroring `values`. -/
  setIdx : Std.HashSet α := {}
  /-- Elements in insertion order (the source of truth). -/
  values : Array α := #[]

namespace OrderedSet

variable {α : Type _} [BEq α] [Hashable α]

/-- Show only the ordered `values`; the index is derived and its iteration order
    is unspecified. -/
public instance [Repr α] : Repr (OrderedSet α) where
  reprPrec s prec := reprPrec s.values prec

/-- The empty collection. -/
@[expose] public def empty : OrderedSet α := .mk {} #[]

public instance : Inhabited (OrderedSet α) := ⟨empty⟩

/-- O(1) membership test via the index. -/
public def contains (s : OrderedSet α) (a : α) : Bool := s.setIdx.contains a

/-- Append `a` unless it is already present (O(1) dedup). -/
public def insert (s : OrderedSet α) (a : α) : OrderedSet α :=
  if s.setIdx.contains a then s
  else .mk (s.setIdx.insert a) (s.values.push a)

/-- Elements in insertion order. -/
@[expose] public def toArray (s : OrderedSet α) : Array α := s.values

/-- Elements in insertion order, as a list. -/
@[expose] public def toList (s : OrderedSet α) : List α := s.values.toList

/-- Wrap an array, computing its index in one pass so the
    two halves agree. If `xs` contains duplicates the index will be smaller than
    the array; callers are expected to pass distinct elements. -/
@[expose] public def ofArray (xs : Array α) : OrderedSet α :=
  .mk (Std.HashSet.ofList xs.toList) xs

end OrderedSet

end Strata.Util
