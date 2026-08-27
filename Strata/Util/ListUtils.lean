/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Std.Data.HashMap.Basic

/-! ## List Properties Utilities
  This file contains miscellaneous utilities for manipulating lists and
  properties on lists.
-/

/-- Two predicates `P` and `Q` are disjoint, that is, they cannot both hold on a
    same instance of type `α` -/
def PredDisjoint (P Q : α → Prop) : Prop := ∀ a, P a → Q a → False


/-- Predicate `P` implies predicate `Q` -/
def PredImplies (P Q : α → Prop) : Prop := ∀ a, P a → Q a


-- These definitions are public because they appear in public structure field types
-- in downstream modules (e.g., WF.lean).
public section

/--
  A list with global properties (`π`) and element-wise properties (`πs`). The
  `split` method detaches the element-wise property of the first element from the
  global property.

  Usually, the global property makes use of the `Forall` predicate.
 -/
class ListP {α : Type} (π : α → Prop) (πs : List α → Prop) where
  split : ∀ {a : α} , πs (a :: as) → π a ×' πs as


/-- A `mapM` function that keeps track of the fact that the function is applied
to an argument that's an element of the original list. Useful for proving
termination. -/
def mapM₁ {m : Type u → Type v} [Monad m] {α : Type w} {β : Type u}
  (xs : List α) (f : {x : α // x ∈ xs} → m β) : m (List β) :=
  xs.attach.mapM f


/--
  Enable attaching the instance itself to properties about the instance.
  See `WFProcedure` and `WFProgram`.
-/
class Wrapper (α : Type) where
  self : α


open List

/-
Taken from mathlib4
https://github.com/leanprover-community/mathlib4/blob/d7a4adb961ed411dbec6ff6857cfc771859ec83f/Mathlib/Data/List/Defs.lean#L131-L137
https://github.com/leanprover-community/mathlib4/blob/d7a4adb961ed411dbec6ff6857cfc771859ec83f/Mathlib/Data/List/Basic.lean#L1203-L1206
-/
@[expose]
def Forall {α} (p : α → Prop) : List α → Prop
  | [] => True
  | x :: [] => p x
  | x :: l => p x ∧ Forall p l


/--
`O(|l|)`. `replace l a b` replaces **all** element in the list equal to `a` with `b`.

* `replace [1, 4, 2, 3, 3, 7] 3 6 = [1, 4, 2, 6, 6, 7]`
* `replace [1, 4, 2, 3, 3, 7] 5 6 = [1, 4, 2, 3, 3, 7]`
Adapted from List.replace
-/
def List.replaceAll [BEq α] : List α → α → α → List α
  | [],    _, _ => []
  | a::as, b, c => match b == a with
    | true  => c :: replaceAll as b c
    | false => a :: replaceAll as b c



/-- `Disjoint l₁ l₂` means that `l₁` and `l₂` have no elements in common.
Taken from https://github.com/leanprover-community/batteries/blob/3613427d66262c4e25e19b40a6a49242e94ba072/Batteries/Data/List/Basic.lean#L512-L514
-/
@[expose] def List.Disjoint (l₁ l₂ : List α) : Prop :=
  ∀ ⦃a⦄, a ∈ l₁ → a ∈ l₂ → False


end -- public section

/-! ### List duplicate detection

Generic utility for finding duplicate elements in a list using `BEq` and
`Hashable` instances for O(n) detection.
-/

/-- Find elements that appear more than once in a list. Uses a HashMap
    for O(1) lookup per element. -/
public def List.findDuplicates [BEq α] [Hashable α] (xs : List α) : List α :=
  let map := xs.foldl (fun (m : Std.HashMap α (α × Nat)) x =>
    match m[x]? with
    | some (orig, n) => m.insert x (orig, n + 1)
    | none => m.insert x (x, 1)
  ) {}
  let revDups := map.fold (fun acc _ (orig, count) =>
    if count > 1 then orig :: acc else acc
  ) ([] : List α)
  revDups.reverse

public section
/-! ### Deduplication and other `List` utilities -/

namespace List

/--
Remove duplicates in a list.
-/
def dedup {α : Type} [DecidableEq α] : List α → List α
  | [] => []
  | a :: as =>
    let as := as.dedup
    if a ∈ as then as else a :: as


/--
Tail-recursive worker for `dedup`. Walks the input left-to-right,
skipping elements that still appear later, and collects kept elements
in reverse order.
-/
def dedupTR.go {α : Type} [DecidableEq α] :
    List α → List α → List α
  | [], acc => acc.reverse
  | a :: as, acc =>
    if a ∈ as then dedupTR.go as acc else dedupTR.go as (a :: acc)


/--
Tail-recursive implementation of `dedup`.
-/
def dedupTR {α : Type} [DecidableEq α] (l : List α) : List α :=
  dedupTR.go l []



/-- Deduplicates l and counts the number of occurrences for each element. -/
def occurrences {α : Type} [DecidableEq α] (l : List α) : List (α × Nat) :=
  l.dedup.map (λ x => (x, l.count x))


/--
`foldlIdx f init l` folds `f` over `l` with an index.
-/
def foldlIdx (f : β → Nat → α → β) (init : β) (l : List α) : β :=
  ((List.range l.length).zip l).foldl (fun acc (i, a) => f acc i a) init


end List

/-! ### List.Forall₂ -/

/-- Pointwise relation between two lists. -/
inductive List.Forall₂ (R : α → β → Prop) : List α → List β → Prop where
  | nil : Forall₂ R [] []
  | cons : R a b → Forall₂ R as bs → Forall₂ R (a :: as) (b :: bs)


end
