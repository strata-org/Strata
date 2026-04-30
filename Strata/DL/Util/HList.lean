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

@[simp] theorem HList.get_cons_zero {α : Type} {f : α → Type} {a : α} {as : List α}
    (x : f a) (xs : HList f as) (h : (a :: as)[0]? = some a)
    : HList.get (.cons x xs) 0 h = x := by
  simp [HList.get]

@[simp] theorem HList.get_cons_succ {α : Type} {f : α → Type} {a b : α} {as : List α}
    (x : f a) (xs : HList f as) (n : Nat) (h : (a :: as)[n + 1]? = some b)
    : HList.get (.cons x xs) (n + 1) h = xs.get n (by simpa using h) := by
  simp [HList.get]

/-- Cast an `HList` along a proof that the index lists are equal. -/
@[expose] def HList.cast {α : Type} {f : α → Type} {xs ys : List α}
    (h : xs = ys) (hlist : HList f xs) : HList f ys :=
  h ▸ hlist

@[simp] theorem HList.cast_cast {α : Type} {f : α → Type} {xs ys zs : List α}
    (h₁ : xs = ys) (h₂ : ys = zs) (hlist : HList f xs)
    : HList.cast h₂ (HList.cast h₁ hlist) = HList.cast (h₁.trans h₂) hlist := by
  subst h₁; subst h₂; rfl

/-- `HList.get` commutes with `HList.cast`. -/
theorem HList.get_cast_gen {α : Type} {f : α → Type} {xs ys : List α} {a b : α}
    (h : xs = ys) (hl : HList f xs) (i : Nat) (hx : xs[i]? = some a) (hy : ys[i]? = some b)
    (hab : a = b)
    : (HList.cast h hl).get i hy = hab ▸ hl.get i hx := by
  subst h; subst hab; rfl

theorem HList.get_cast {α : Type} {f : α → Type} {xs ys : List α} {a : α}
    (h : xs = ys) (hl : HList f xs) (i : Nat) (hx : xs[i]? = some a) (hy : ys[i]? = some a)
    : (HList.cast h hl).get i hy = hl.get i hx := by
  exact get_cast_gen h hl i hx hy rfl

/-- Append two HLists. -/
@[expose] def HList.append {α : Type} {f : α → Type} {xs ys : List α}
    : HList f xs → HList f ys → HList f (xs ++ ys)
  | .nil, ys => ys
  | .cons x xs, ys => .cons x (HList.append xs ys)

/-- Get from an appended HList at index < |xs| returns the same as get from xs. -/
theorem HList.get_append_left {f : α → Type} {xs ys : List α} {a : α}
    (hxs : HList f xs) (hys : HList f ys)
    (i : Nat) (h : (xs ++ ys)[i]? = some a) (h' : xs[i]? = some a)
    : HList.get (HList.append hxs hys) i h = HList.get hxs i h' := by
  induction hxs generalizing i with
  | nil => simp at h'
  | cons x xs ih =>
    cases i with
    | zero => simp [HList.append, HList.get] at *
    | succ n => simp [HList.append, HList.get] at *; simp at h h'; exact ih n h h'

/-- Get from (xs ++ cons v ys) at index |xs| returns v. -/
theorem HList.get_append_cons_self {f : α → Type} {xs : List α} {a : α} {ys : List α}
    (hxs : HList f xs) (v : f a) (hys : HList f ys)
    (h : (xs ++ a :: ys)[xs.length]? = some a)
    : HList.get (HList.append hxs (.cons v hys)) xs.length h = v := by
  induction hxs with
  | nil => simp [HList.append]
  | cons x xs' ih => simp [HList.append] at *; exact ih trivial

/-- Get from an appended HList at index ≥ |xs| returns the same as get from ys. -/
theorem HList.get_append_right {f : α → Type} {xs ys : List α} {a : α}
    (hxs : HList f xs) (hys : HList f ys)
    (i : Nat) (h : (xs ++ ys)[i]? = some a) (h' : ys[i - xs.length]? = some a)
    (h_ge : i ≥ xs.length)
    : HList.get (HList.append hxs hys) i h = HList.get hys (i - xs.length) h' := by
  induction hxs generalizing i with
  | nil => simp [HList.append]
  | cons x xs' ih =>
    cases i with
    | zero => simp at h_ge
    | succ n =>
      simp [HList.append]
      exact ih n (by simpa using h) (by simpa using h') (by grind)
