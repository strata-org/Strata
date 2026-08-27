/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

/-!
## Heterogeneous Lists (HList)

Type-indexed lists used to represent bound-variable valuations in the
denotational semantics.
-/

public section

/-- A heterogeneous list indexed by a list of elements of type `α`. -/
inductive HList {α : Type} (f : α → Type) : List α → Type where
  | nil  : HList f []
  | cons : f a → HList f as → HList f (a :: as)


/-- Look up the `i`-th element of an `HList`, given a proof that the list
maps index `i` to `a`. -/
@[expose] def HList.get {α : Type} {f : α → Type} {as : List α} {a : α} :
    HList f as → (i : Nat) → as[i]? = some a → f a
  | .cons x _, 0, h => by simp at h; subst h; exact x
  | .cons _ xs, n + 1, h => by simp at h; exact xs.get n h


/-- Cast an `HList` along a proof that the index lists are equal. -/
@[expose] def HList.cast {α : Type} {f : α → Type} {xs ys : List α}
    (h : xs = ys) (hlist : HList f xs) : HList f ys :=
  h ▸ hlist


/-- Append two HLists. -/
@[expose] def HList.append {α : Type} {f : α → Type} {xs ys : List α}
    : HList f xs → HList f ys → HList f (xs ++ ys)
  | .nil, ys => ys
  | .cons x xs, ys => .cons x (HList.append xs ys)

